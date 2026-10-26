import V185TrunkScan22Chunk227

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2033079 : List Nat := [1, 1, 3, 1, 3, 2, 1, 10]
def baseStart_2033079 : Nat := 118140960795 + 2033079 * 2 ^ 59
def prefixEnd_2033079 : Nat := 4983230072969 + 3 ^ 40 * 2033079 * 2
def baseEnd_2033079 : Nat := 77329387819433800204633

theorem tailTrace_2033079 : CollatzResearch.WordTrace tailWord_2033079 prefixEnd_2033079 77329387819433800204633 := by
  unfold tailWord_2033079
  simp only [CollatzResearch.WordTrace]
  refine ⟨74152483001509480094534291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49434988667672986729689527 74152483001509480094534291)
  ·
    refine ⟨111228724502264220141801437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74152483001509480094534291 111228724502264220141801437)
    ·
      refine ⟨41710771688349082553175539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111228724502264220141801437 41710771688349082553175539)
      ·
        refine ⟨62566157532523623829763309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41710771688349082553175539 62566157532523623829763309)
        ·
          refine ⟨23462309074696358936161241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62566157532523623829763309 23462309074696358936161241)
          ·
            refine ⟨17596731806022269202120931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23462309074696358936161241 17596731806022269202120931)
            ·
              refine ⟨26395097709033403803181397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17596731806022269202120931 26395097709033403803181397)
              ·
                refine ⟨77329387819433800204633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26395097709033403803181397 77329387819433800204633)
                ·
                  rfl

theorem cell22_2033079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 10].length) (baseStart_2033079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033079 prefixEnd_2033079 := by exact prefixLift 2033079
  have htrace : WordTrace (prefixWord ++ tailWord_2033079) baseStart_2033079 baseEnd_2033079 := by
    simpa [prefixWord, tailWord_2033079, baseEnd_2033079] using wordTrace_append hprefix tailTrace_2033079
  have hstable : (prefixWord ++ tailWord_2033079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033079).length < 2 ^ (prefixWord ++ tailWord_2033079).sum := by decide
  have hdescent : baseEnd_2033079 < baseStart_2033079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033100 : List Nat := [2, 2, 1, 4, 2, 2, 2, 2, 2, 3]
def baseStart_2033100 : Nat := 118140960795 + 2033100 * 2 ^ 59
def prefixEnd_2033100 : Nat := 4983230072969 + 3 ^ 40 * 2033100 * 2
def baseEnd_2033100 : Nat := 695971679104067147066633

theorem tailTrace_2033100 : CollatzResearch.WordTrace tailWord_2033100 prefixEnd_2033100 695971679104067147066633 := by
  unfold tailWord_2033100
  simp only [CollatzResearch.WordTrace]
  refine ⟨37076624467216700340524377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49435499289622267120699169 37076624467216700340524377)
  ·
    refine ⟨27807468350412525255393283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37076624467216700340524377 27807468350412525255393283)
    ·
      refine ⟨41711202525618787883089925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27807468350412525255393283 41711202525618787883089925)
      ·
        refine ⟨7820850473553522728079361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41711202525618787883089925 7820850473553522728079361)
        ·
          refine ⟨5865637855165142046059521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7820850473553522728079361 5865637855165142046059521)
          ·
            refine ⟨4399228391373856534544641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5865637855165142046059521 4399228391373856534544641)
            ·
              refine ⟨3299421293530392400908481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4399228391373856534544641 3299421293530392400908481)
              ·
                refine ⟨2474565970147794300681361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3299421293530392400908481 2474565970147794300681361)
                ·
                  refine ⟨1855924477610845725511021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2474565970147794300681361 1855924477610845725511021)
                  ·
                    refine ⟨695971679104067147066633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1855924477610845725511021 695971679104067147066633)
                    ·
                      rfl

theorem cell22_2033100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_2033100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033100 prefixEnd_2033100 := by exact prefixLift 2033100
  have htrace : WordTrace (prefixWord ++ tailWord_2033100) baseStart_2033100 baseEnd_2033100 := by
    simpa [prefixWord, tailWord_2033100, baseEnd_2033100] using wordTrace_append hprefix tailTrace_2033100
  have hstable : (prefixWord ++ tailWord_2033100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033100).length < 2 ^ (prefixWord ++ tailWord_2033100).sum := by decide
  have hdescent : baseEnd_2033100 < baseStart_2033100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033111 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 7, 3]
def baseStart_2033111 : Nat := 118140960795 + 2033111 * 2 ^ 59
def prefixEnd_2033111 : Nat := 4983230072969 + 3 ^ 40 * 2033111 * 2
def baseEnd_2033111 : Nat := 695975444628866785041599

theorem tailTrace_2033111 : CollatzResearch.WordTrace tailWord_2033111 prefixEnd_2033111 695975444628866785041599 := by
  unfold tailWord_2033111
  simp only [CollatzResearch.WordTrace]
  refine ⟨74153650137393549559699187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49435766758262366373132791 74153650137393549559699187)
  ·
    refine ⟨111230475206090324339548781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74153650137393549559699187 111230475206090324339548781)
    ·
      refine ⟨41711428202283871627330793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111230475206090324339548781 41711428202283871627330793)
      ·
        refine ⟨31283571151712903720498095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41711428202283871627330793 31283571151712903720498095)
        ·
          refine ⟨46925356727569355580747143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31283571151712903720498095 46925356727569355580747143)
          ·
            refine ⟨70388035091354033371120715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46925356727569355580747143 70388035091354033371120715)
            ·
              refine ⟨105582052637031050056681073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70388035091354033371120715 105582052637031050056681073)
              ·
                refine ⟨79186539477773287542510805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105582052637031050056681073 79186539477773287542510805)
                ·
                  refine ⟨1855934519010311426777597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 79186539477773287542510805 1855934519010311426777597)
                  ·
                    refine ⟨695975444628866785041599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1855934519010311426777597 695975444628866785041599)
                    ·
                      rfl

theorem cell22_2033111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_2033111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033111 prefixEnd_2033111 := by exact prefixLift 2033111
  have htrace : WordTrace (prefixWord ++ tailWord_2033111) baseStart_2033111 baseEnd_2033111 := by
    simpa [prefixWord, tailWord_2033111, baseEnd_2033111] using wordTrace_append hprefix tailTrace_2033111
  have hstable : (prefixWord ++ tailWord_2033111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033111).length < 2 ^ (prefixWord ++ tailWord_2033111).sum := by decide
  have hdescent : baseEnd_2033111 < baseStart_2033111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033128 : List Nat := [2, 1, 4, 1, 1, 2, 3, 2, 3, 3]
def baseStart_2033128 : Nat := 118140960795 + 2033128 * 2 ^ 59
def prefixEnd_2033128 : Nat := 4983230072969 + 3 ^ 40 * 2033128 * 2
def baseEnd_2033128 : Nat := 695981264076284407366547

theorem tailTrace_2033128 : CollatzResearch.WordTrace tailWord_2033128 prefixEnd_2033128 695981264076284407366547 := by
  unfold tailWord_2033128
  simp only [CollatzResearch.WordTrace]
  refine ⟨37077135089165980731534019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49436180118887974308712025 37077135089165980731534019)
  ·
    refine ⟨55615702633748971097301029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37077135089165980731534019 55615702633748971097301029)
    ·
      refine ⟨10427944243827932080743943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55615702633748971097301029 10427944243827932080743943)
      ·
        refine ⟨15641916365741898121115915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10427944243827932080743943 15641916365741898121115915)
        ·
          refine ⟨23462874548612847181673873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15641916365741898121115915 23462874548612847181673873)
          ·
            refine ⟨17597155911459635386255405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23462874548612847181673873 17597155911459635386255405)
            ·
              refine ⟨6598933466797363269845777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17597155911459635386255405 6598933466797363269845777)
              ·
                refine ⟨4949200100098022452384333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6598933466797363269845777 4949200100098022452384333)
                ·
                  refine ⟨1855950037536758419644125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4949200100098022452384333 1855950037536758419644125)
                  ·
                    refine ⟨695981264076284407366547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1855950037536758419644125 695981264076284407366547)
                    ·
                      rfl

theorem cell22_2033128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_2033128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033128 prefixEnd_2033128 := by exact prefixLift 2033128
  have htrace : WordTrace (prefixWord ++ tailWord_2033128) baseStart_2033128 baseEnd_2033128 := by
    simpa [prefixWord, tailWord_2033128, baseEnd_2033128] using wordTrace_append hprefix tailTrace_2033128
  have hstable : (prefixWord ++ tailWord_2033128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033128).length < 2 ^ (prefixWord ++ tailWord_2033128).sum := by decide
  have hdescent : baseEnd_2033128 < baseStart_2033128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033201 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 3, 5]
def baseStart_2033201 : Nat := 118140960795 + 2033201 * 2 ^ 59
def prefixEnd_2033201 : Nat := 4983230072969 + 3 ^ 40 * 2033201 * 2
def baseEnd_2033201 : Nat := 696006253468136550291323

theorem tailTrace_2033201 : CollatzResearch.WordTrace tailWord_2033201 prefixEnd_2033201 696006253468136550291323 := by
  unfold tailWord_2033201
  simp only [CollatzResearch.WordTrace]
  refine ⟨74156932707067494930475457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49437955138044996620316971 74156932707067494930475457)
  ·
    refine ⟨55617699530300621197856593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74156932707067494930475457 55617699530300621197856593)
    ·
      refine ⟨41713274647725465898392445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55617699530300621197856593 41713274647725465898392445)
      ·
        refine ⟨15642477992897049711897167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41713274647725465898392445 15642477992897049711897167)
        ·
          refine ⟨23463716989345574567845751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15642477992897049711897167 23463716989345574567845751)
          ·
            refine ⟨35195575484018361851768627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23463716989345574567845751 35195575484018361851768627)
            ·
              refine ⟨52793363226027542777652941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35195575484018361851768627 52793363226027542777652941)
              ·
                refine ⟨19797511209760328541619853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52793363226027542777652941 19797511209760328541619853)
                ·
                  refine ⟨7424066703660123203107445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19797511209760328541619853 7424066703660123203107445)
                  ·
                    refine ⟨696006253468136550291323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7424066703660123203107445 696006253468136550291323)
                    ·
                      rfl

theorem cell22_2033201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_2033201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033201 prefixEnd_2033201 := by exact prefixLift 2033201
  have htrace : WordTrace (prefixWord ++ tailWord_2033201) baseStart_2033201 baseEnd_2033201 := by
    simpa [prefixWord, tailWord_2033201, baseEnd_2033201] using wordTrace_append hprefix tailTrace_2033201
  have hstable : (prefixWord ++ tailWord_2033201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033201).length < 2 ^ (prefixWord ++ tailWord_2033201).sum := by decide
  have hdescent : baseEnd_2033201 < baseStart_2033201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033338 : List Nat := [3, 1, 1, 1, 2, 4, 1, 3, 6]
def baseStart_2033338 : Nat := 118140960795 + 2033338 * 2 ^ 59
def prefixEnd_2033338 : Nat := 4983230072969 + 3 ^ 40 * 2033338 * 2
def baseEnd_2033338 : Nat := 232017717122637953205301

theorem tailTrace_2033338 : CollatzResearch.WordTrace tailWord_2033338 prefixEnd_2033338 232017717122637953205301 := by
  unfold tailWord_2033338
  simp only [CollatzResearch.WordTrace]
  refine ⟨18540482376892791832053167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49441286338380778218808445 18540482376892791832053167)
  ·
    refine ⟨27810723565339187748079751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18540482376892791832053167 27810723565339187748079751)
    ·
      refine ⟨41716085348008781622119627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27810723565339187748079751 41716085348008781622119627)
      ·
        refine ⟨62574128022013172433179441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41716085348008781622119627 62574128022013172433179441)
        ·
          refine ⟨46930596016509879324884581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62574128022013172433179441 46930596016509879324884581)
          ·
            refine ⟨8799486753095602373415859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46930596016509879324884581 8799486753095602373415859)
            ·
              refine ⟨13199230129643403560123789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8799486753095602373415859 13199230129643403560123789)
              ·
                refine ⟨4949711298616276335046421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13199230129643403560123789 4949711298616276335046421)
                ·
                  refine ⟨232017717122637953205301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4949711298616276335046421 232017717122637953205301)
                  ·
                    rfl

theorem cell22_2033338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_2033338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033338 prefixEnd_2033338 := by exact prefixLift 2033338
  have htrace : WordTrace (prefixWord ++ tailWord_2033338) baseStart_2033338 baseEnd_2033338 := by
    simpa [prefixWord, tailWord_2033338, baseEnd_2033338] using wordTrace_append hprefix tailTrace_2033338
  have hstable : (prefixWord ++ tailWord_2033338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033338).length < 2 ^ (prefixWord ++ tailWord_2033338).sum := by decide
  have hdescent : baseEnd_2033338 < baseStart_2033338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033368 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 1, 6]
def baseStart_2033368 : Nat := 118140960795 + 2033368 * 2 ^ 59
def prefixEnd_2033368 : Nat := 4983230072969 + 3 ^ 40 * 2033368 * 2
def baseEnd_2033368 : Nat := 696063420981003781365811

theorem tailTrace_2033368 : CollatzResearch.WordTrace tailWord_2033368 prefixEnd_2033368 696063420981003781365811 := by
  unfold tailWord_2033368
  simp only [CollatzResearch.WordTrace]
  refine ⟨37081511848731241225902379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49442015798308321634536505 37081511848731241225902379)
  ·
    refine ⟨55622267773096861838853569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37081511848731241225902379 55622267773096861838853569)
    ·
      refine ⟨41716700829822646379140177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55622267773096861838853569 41716700829822646379140177)
      ·
        refine ⟨31287525622366984784355133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41716700829822646379140177 31287525622366984784355133)
        ·
          refine ⟨11732822108387619294133175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31287525622366984784355133 11732822108387619294133175)
          ·
            refine ⟨17599233162581428941199763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11732822108387619294133175 17599233162581428941199763)
            ·
              refine ⟨26398849743872143411799645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17599233162581428941199763 26398849743872143411799645)
              ·
                refine ⟨9899568653952053779424867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26398849743872143411799645 9899568653952053779424867)
                ·
                  refine ⟨14849352980928080669137301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9899568653952053779424867 14849352980928080669137301)
                  ·
                    refine ⟨696063420981003781365811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14849352980928080669137301 696063420981003781365811)
                    ·
                      rfl

theorem cell22_2033368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_2033368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033368 prefixEnd_2033368 := by exact prefixLift 2033368
  have htrace : WordTrace (prefixWord ++ tailWord_2033368) baseStart_2033368 baseEnd_2033368 := by
    simpa [prefixWord, tailWord_2033368, baseEnd_2033368] using wordTrace_append hprefix tailTrace_2033368
  have hstable : (prefixWord ++ tailWord_2033368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033368).length < 2 ^ (prefixWord ++ tailWord_2033368).sum := by decide
  have hdescent : baseEnd_2033368 < baseStart_2033368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033370 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 4, 3]
def baseStart_2033370 : Nat := 118140960795 + 2033370 * 2 ^ 59
def prefixEnd_2033370 : Nat := 4983230072969 + 3 ^ 40 * 2033370 * 2
def baseEnd_2033370 : Nat := 696064105621876442815805

theorem tailTrace_2033370 : CollatzResearch.WordTrace tailWord_2033370 prefixEnd_2033370 696064105621876442815805 := by
  unfold tailWord_2033370
  simp only [CollatzResearch.WordTrace]
  refine ⟨18540774160863809198344391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49442064428970157862251709 18540774160863809198344391)
  ·
    refine ⟨27811161241295713797516587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18540774160863809198344391 27811161241295713797516587)
    ·
      refine ⟨41716741861943570696274881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27811161241295713797516587 41716741861943570696274881)
      ·
        refine ⟨31287556396457678022206161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41716741861943570696274881 31287556396457678022206161)
        ·
          refine ⟨23465667297343258516654621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31287556396457678022206161 23465667297343258516654621)
          ·
            refine ⟨8799625236503721943745483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23465667297343258516654621 8799625236503721943745483)
            ·
              refine ⟨13199437854755582915618225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8799625236503721943745483 13199437854755582915618225)
              ·
                refine ⟨9899578391066687186713669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13199437854755582915618225 9899578391066687186713669)
                ·
                  refine ⟨1856170948325003847508813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9899578391066687186713669 1856170948325003847508813)
                  ·
                    refine ⟨696064105621876442815805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1856170948325003847508813 696064105621876442815805)
                    ·
                      rfl

theorem cell22_2033370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_2033370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033370 prefixEnd_2033370 := by exact prefixLift 2033370
  have htrace : WordTrace (prefixWord ++ tailWord_2033370) baseStart_2033370 baseEnd_2033370 := by
    simpa [prefixWord, tailWord_2033370, baseEnd_2033370] using wordTrace_append hprefix tailTrace_2033370
  have hstable : (prefixWord ++ tailWord_2033370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033370).length < 2 ^ (prefixWord ++ tailWord_2033370).sum := by decide
  have hdescent : baseEnd_2033370 < baseStart_2033370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033389 : List Nat := [1, 5, 1, 2, 1, 3, 3, 2, 4]
def baseStart_2033389 : Nat := 118140960795 + 2033389 * 2 ^ 59
def prefixEnd_2033389 : Nat := 4983230072969 + 3 ^ 40 * 2033389 * 2
def baseEnd_2033389 : Nat := 232023536570055575530249

theorem tailTrace_2033389 : CollatzResearch.WordTrace tailWord_2033389 prefixEnd_2033389 232023536570055575530249 := by
  unfold tailWord_2033389
  simp only [CollatzResearch.WordTrace]
  refine ⟨74163789630386403038319221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49442526420257602025546147 74163789630386403038319221)
  ·
    refine ⟨6952855277848725284842427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74163789630386403038319221 6952855277848725284842427)
    ·
      refine ⟨10429282916773087927263641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6952855277848725284842427 10429282916773087927263641)
      ·
        refine ⟨7821962187579815945447731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10429282916773087927263641 7821962187579815945447731)
        ·
          refine ⟨11732943281369723918171597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7821962187579815945447731 11732943281369723918171597)
          ·
            refine ⟨4399853730513646469314349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11732943281369723918171597 4399853730513646469314349)
            ·
              refine ⟨1649945148942617425992881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4399853730513646469314349 1649945148942617425992881)
              ·
                refine ⟨1237458861706963069494661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1649945148942617425992881 1237458861706963069494661)
                ·
                  refine ⟨232023536570055575530249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1237458861706963069494661 232023536570055575530249)
                  ·
                    rfl

theorem cell22_2033389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_2033389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033389 prefixEnd_2033389 := by exact prefixLift 2033389
  have htrace : WordTrace (prefixWord ++ tailWord_2033389) baseStart_2033389 baseEnd_2033389 := by
    simpa [prefixWord, tailWord_2033389, baseEnd_2033389] using wordTrace_append hprefix tailTrace_2033389
  have hstable : (prefixWord ++ tailWord_2033389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033389).length < 2 ^ (prefixWord ++ tailWord_2033389).sum := by decide
  have hdescent : baseEnd_2033389 < baseStart_2033389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033438 : List Nat := [4, 3, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_2033438 : Nat := 118140960795 + 2033438 * 2 ^ 59
def prefixEnd_2033438 : Nat := 4983230072969 + 3 ^ 40 * 2033438 * 2
def baseEnd_2033438 : Nat := 696087383411546932115597

theorem tailTrace_2033438 : CollatzResearch.WordTrace tailWord_2033438 prefixEnd_2033438 696087383411546932115597 := by
  unfold tailWord_2033438
  simp only [CollatzResearch.WordTrace]
  refine ⟨9270697100901110550856621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49443717871472589604568645 9270697100901110550856621)
  ·
    refine ⟨3476511412837916456571233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9270697100901110550856621 3476511412837916456571233)
    ·
      refine ⟨2607383559628437342428425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3476511412837916456571233 2607383559628437342428425)
      ·
        refine ⟨1955537669721328006821319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2607383559628437342428425 1955537669721328006821319)
        ·
          refine ⟨2933306504581992010231979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1955537669721328006821319 2933306504581992010231979)
          ·
            refine ⟨4399959756872988015347969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933306504581992010231979 4399959756872988015347969)
            ·
              refine ⟨3299969817654741011510977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4399959756872988015347969 3299969817654741011510977)
              ·
                refine ⟨2474977363241055758633233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3299969817654741011510977 2474977363241055758633233)
                ·
                  refine ⟨1856233022430791818974925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2474977363241055758633233 1856233022430791818974925)
                  ·
                    refine ⟨696087383411546932115597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1856233022430791818974925 696087383411546932115597)
                    ·
                      rfl

theorem cell22_2033438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_2033438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033438 prefixEnd_2033438 := by exact prefixLift 2033438
  have htrace : WordTrace (prefixWord ++ tailWord_2033438) baseStart_2033438 baseEnd_2033438 := by
    simpa [prefixWord, tailWord_2033438, baseEnd_2033438] using wordTrace_append hprefix tailTrace_2033438
  have hstable : (prefixWord ++ tailWord_2033438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033438).length < 2 ^ (prefixWord ++ tailWord_2033438).sum := by decide
  have hdescent : baseEnd_2033438 < baseStart_2033438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033445 : List Nat := [1, 3, 1, 2, 3, 2, 1, 4, 5]
def baseStart_2033445 : Nat := 118140960795 + 2033445 * 2 ^ 59
def prefixEnd_2033445 : Nat := 4983230072969 + 3 ^ 40 * 2033445 * 2
def baseEnd_2033445 : Nat := 232029926551533749063525

theorem tailTrace_2033445 : CollatzResearch.WordTrace tailWord_2033445 prefixEnd_2033445 232029926551533749063525 := by
  unfold tailWord_2033445
  simp only [CollatzResearch.WordTrace]
  refine ⟨74165832118183524602357789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49443888078789016401571859 74165832118183524602357789)
  ·
    refine ⟨27812187044318821725884171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74165832118183524602357789 27812187044318821725884171)
    ·
      refine ⟨41718280566478232588826257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27812187044318821725884171 41718280566478232588826257)
      ·
        refine ⟨31288710424858674441619693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41718280566478232588826257 31288710424858674441619693)
        ·
          refine ⟨11733266409322002915607385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31288710424858674441619693 11733266409322002915607385)
          ·
            refine ⟨8799949806991502186705539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11733266409322002915607385 8799949806991502186705539)
            ·
              refine ⟨13199924710487253280058309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8799949806991502186705539 13199924710487253280058309)
              ·
                refine ⟨2474985883216359990010933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13199924710487253280058309 2474985883216359990010933)
                ·
                  refine ⟨232029926551533749063525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2474985883216359990010933 232029926551533749063525)
                  ·
                    rfl

theorem cell22_2033445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_2033445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033445 prefixEnd_2033445 := by exact prefixLift 2033445
  have htrace : WordTrace (prefixWord ++ tailWord_2033445) baseStart_2033445 baseEnd_2033445 := by
    simpa [prefixWord, tailWord_2033445, baseEnd_2033445] using wordTrace_append hprefix tailTrace_2033445
  have hstable : (prefixWord ++ tailWord_2033445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033445).length < 2 ^ (prefixWord ++ tailWord_2033445).sum := by decide
  have hdescent : baseEnd_2033445 < baseStart_2033445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033475 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 3, 4]
def baseStart_2033475 : Nat := 118140960795 + 2033475 * 2 ^ 59
def prefixEnd_2033475 : Nat := 4983230072969 + 3 ^ 40 * 2033475 * 2
def baseEnd_2033475 : Nat := 696100049267691168940483

theorem tailTrace_2033475 : CollatzResearch.WordTrace tailWord_2033475 prefixEnd_2033475 696100049267691168940483 := by
  unfold tailWord_2033475
  simp only [CollatzResearch.WordTrace]
  refine ⟨74166926308074839725949879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49444617538716559817299919 74166926308074839725949879)
  ·
    refine ⟨111250389462112259588924819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74166926308074839725949879 111250389462112259588924819)
    ·
      refine ⟨166875584193168389383387229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111250389462112259588924819 166875584193168389383387229)
      ·
        refine ⟨62578344072438146018770211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166875584193168389383387229 62578344072438146018770211)
        ·
          refine ⟨93867516108657219028155317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62578344072438146018770211 93867516108657219028155317)
          ·
            refine ⟨8800079635186614283889561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93867516108657219028155317 8800079635186614283889561)
            ·
              refine ⟨6600059726389960712917171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8800079635186614283889561 6600059726389960712917171)
              ·
                refine ⟨9900089589584941069375757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6600059726389960712917171 9900089589584941069375757)
                ·
                  refine ⟨3712533596094352901015909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9900089589584941069375757 3712533596094352901015909)
                  ·
                    refine ⟨696100049267691168940483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3712533596094352901015909 696100049267691168940483)
                    ·
                      rfl

theorem cell22_2033475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 4].length) (baseStart_2033475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033475 prefixEnd_2033475 := by exact prefixLift 2033475
  have htrace : WordTrace (prefixWord ++ tailWord_2033475) baseStart_2033475 baseEnd_2033475 := by
    simpa [prefixWord, tailWord_2033475, baseEnd_2033475] using wordTrace_append hprefix tailTrace_2033475
  have hstable : (prefixWord ++ tailWord_2033475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033475).length < 2 ^ (prefixWord ++ tailWord_2033475).sum := by decide
  have hdescent : baseEnd_2033475 < baseStart_2033475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033507 : List Nat := [1, 1, 1, 5, 4, 1, 2, 1, 6]
def baseStart_2033507 : Nat := 118140960795 + 2033507 * 2 ^ 59
def prefixEnd_2033507 : Nat := 4983230072969 + 3 ^ 40 * 2033507 * 2
def baseEnd_2033507 : Nat := 232037001173884584046795

theorem tailTrace_2033507 : CollatzResearch.WordTrace tailWord_2033507 prefixEnd_2033507 232037001173884584046795 := by
  unfold tailWord_2033507
  simp only [CollatzResearch.WordTrace]
  refine ⟨74168093443958909191114775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49445395629305939460743183 74168093443958909191114775)
  ·
    refine ⟨111252140165938363786672163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74168093443958909191114775 111252140165938363786672163)
    ·
      refine ⟨166878210248907545680008245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111252140165938363786672163 166878210248907545680008245)
      ·
        refine ⟨15644832210835082407500773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166878210248907545680008245 15644832210835082407500773)
        ·
          refine ⟨2933406039531577951406395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15644832210835082407500773 2933406039531577951406395)
          ·
            refine ⟨4400109059297366927109593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933406039531577951406395 4400109059297366927109593)
            ·
              refine ⟨3300081794473025195332195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4400109059297366927109593 3300081794473025195332195)
              ·
                refine ⟨4950122691709537792998293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300081794473025195332195 4950122691709537792998293)
                ·
                  refine ⟨232037001173884584046795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4950122691709537792998293 232037001173884584046795)
                  ·
                    rfl

theorem cell22_2033507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 6].length) (baseStart_2033507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033507 prefixEnd_2033507 := by exact prefixLift 2033507
  have htrace : WordTrace (prefixWord ++ tailWord_2033507) baseStart_2033507 baseEnd_2033507 := by
    simpa [prefixWord, tailWord_2033507, baseEnd_2033507] using wordTrace_append hprefix tailTrace_2033507
  have hstable : (prefixWord ++ tailWord_2033507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033507).length < 2 ^ (prefixWord ++ tailWord_2033507).sum := by decide
  have hdescent : baseEnd_2033507 < baseStart_2033507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033526 : List Nat := [5, 1, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_2033526 : Nat := 118140960795 + 2033526 * 2 ^ 59
def prefixEnd_2033526 : Nat := 4983230072969 + 3 ^ 40 * 2033526 * 2
def baseEnd_2033526 : Nat := 696117507609944035915327

theorem tailTrace_2033526 : CollatzResearch.WordTrace tailWord_2033526 prefixEnd_2033526 696117507609944035915327 := by
  unfold tailWord_2033526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4635549151930629714753527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49445857620593383624037621 4635549151930629714753527)
  ·
    refine ⟨6953323727895944572130291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4635549151930629714753527 6953323727895944572130291)
    ·
      refine ⟨10429985591843916858195437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6953323727895944572130291 10429985591843916858195437)
      ·
        refine ⟨3911244596941468821823289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10429985591843916858195437 3911244596941468821823289)
        ·
          refine ⟨2933433447706101616367467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3911244596941468821823289 2933433447706101616367467)
          ·
            refine ⟨4400150171559152424551201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933433447706101616367467 4400150171559152424551201)
            ·
              refine ⟨3300112628669364318413401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4400150171559152424551201 3300112628669364318413401)
              ·
                refine ⟨2475084471502023238810051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3300112628669364318413401 2475084471502023238810051)
                ·
                  refine ⟨3712626707253034858215077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2475084471502023238810051 3712626707253034858215077)
                  ·
                    refine ⟨696117507609944035915327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3712626707253034858215077 696117507609944035915327)
                    ·
                      rfl

theorem cell22_2033526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_2033526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033526 prefixEnd_2033526 := by exact prefixLift 2033526
  have htrace : WordTrace (prefixWord ++ tailWord_2033526) baseStart_2033526 baseEnd_2033526 := by
    simpa [prefixWord, tailWord_2033526, baseEnd_2033526] using wordTrace_append hprefix tailTrace_2033526
  have hstable : (prefixWord ++ tailWord_2033526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033526).length < 2 ^ (prefixWord ++ tailWord_2033526).sum := by decide
  have hdescent : baseEnd_2033526 < baseStart_2033526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033554 : List Nat := [3, 2, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_2033554 : Nat := 118140960795 + 2033554 * 2 ^ 59
def prefixEnd_2033554 : Nat := 4983230072969 + 3 ^ 40 * 2033554 * 2
def baseEnd_2033554 : Nat := 696127092582161296215241

theorem tailTrace_2033554 : CollatzResearch.WordTrace tailWord_2033554 prefixEnd_2033554 696127092582161296215241 := by
  unfold tailWord_2033554
  simp only [CollatzResearch.WordTrace]
  refine ⟨18542451918697159054518929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49446538449859090812050477 18542451918697159054518929)
  ·
    refine ⟨13906838939022869290889197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18542451918697159054518929 13906838939022869290889197)
    ·
      refine ⟨5215064602133575984083449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13906838939022869290889197 5215064602133575984083449)
      ·
        refine ⟨3911298451600181988062587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5215064602133575984083449 3911298451600181988062587)
        ·
          refine ⟨5866947677400272982093881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3911298451600181988062587 5866947677400272982093881)
          ·
            refine ⟨4400210758050204736570411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5866947677400272982093881 4400210758050204736570411)
            ·
              refine ⟨6600316137075307104855617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4400210758050204736570411 6600316137075307104855617)
              ·
                refine ⟨4950237102806480328641713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6600316137075307104855617 4950237102806480328641713)
                ·
                  refine ⟨3712677827104860246481285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4950237102806480328641713 3712677827104860246481285)
                  ·
                    refine ⟨696127092582161296215241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3712677827104860246481285 696127092582161296215241)
                    ·
                      rfl

theorem cell22_2033554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_2033554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033554 prefixEnd_2033554 := by exact prefixLift 2033554
  have htrace : WordTrace (prefixWord ++ tailWord_2033554) baseStart_2033554 baseEnd_2033554 := by
    simpa [prefixWord, tailWord_2033554, baseEnd_2033554] using wordTrace_append hprefix tailTrace_2033554
  have hstable : (prefixWord ++ tailWord_2033554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033554).length < 2 ^ (prefixWord ++ tailWord_2033554).sum := by decide
  have hdescent : baseEnd_2033554 < baseStart_2033554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033558 : List Nat := [5, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_2033558 : Nat := 118140960795 + 2033558 * 2 ^ 59
def prefixEnd_2033558 : Nat := 4983230072969 + 3 ^ 40 * 2033558 * 2
def baseEnd_2033558 : Nat := 232042820621302206371743

theorem tailTrace_2033558 : CollatzResearch.WordTrace tailWord_2033558 prefixEnd_2033558 232042820621302206371743 := by
  unfold tailWord_2033558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4635622097923384056326333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49446635711182763267480885 4635622097923384056326333)
  ·
    refine ⟨1738358286721269021122375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4635622097923384056326333 1738358286721269021122375)
    ·
      refine ⟨2607537430081903531683563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1738358286721269021122375 2607537430081903531683563)
      ·
        refine ⟨3911306145122855297525345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2607537430081903531683563 3911306145122855297525345)
        ·
          refine ⟨2933479608842141473144009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3911306145122855297525345 2933479608842141473144009)
          ·
            refine ⟨2200109706631606104858007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2933479608842141473144009 2200109706631606104858007)
            ·
              refine ⟨3300164559947409157287011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200109706631606104858007 3300164559947409157287011)
              ·
                refine ⟨4950246839921113735930517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300164559947409157287011 4950246839921113735930517)
                ·
                  refine ⟨232042820621302206371743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4950246839921113735930517 232042820621302206371743)
                  ·
                    rfl

theorem cell22_2033558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_2033558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033558 prefixEnd_2033558 := by exact prefixLift 2033558
  have htrace : WordTrace (prefixWord ++ tailWord_2033558) baseStart_2033558 baseEnd_2033558 := by
    simpa [prefixWord, tailWord_2033558, baseEnd_2033558] using wordTrace_append hprefix tailTrace_2033558
  have hstable : (prefixWord ++ tailWord_2033558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033558).length < 2 ^ (prefixWord ++ tailWord_2033558).sum := by decide
  have hdescent : baseEnd_2033558 < baseStart_2033558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033618 : List Nat := [3, 2, 2, 3, 2, 1, 1, 4, 1, 3]
def baseStart_2033618 : Nat := 118140960795 + 2033618 * 2 ^ 59
def prefixEnd_2033618 : Nat := 4983230072969 + 3 ^ 40 * 2033618 * 2
def baseEnd_2033618 : Nat := 696149001090086462615045

theorem tailTrace_2033618 : CollatzResearch.WordTrace tailWord_2033618 prefixEnd_2033618 696149001090086462615045 := by
  unfold tailWord_2033618
  simp only [CollatzResearch.WordTrace]
  refine ⟨18543035486639193787101377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49448094631037850098937005 18543035486639193787101377)
  ·
    refine ⟨13907276614979395340326033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18543035486639193787101377 13907276614979395340326033)
    ·
      refine ⟨10430457461234546505244525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13907276614979395340326033 10430457461234546505244525)
      ·
        refine ⟨3911421547962954939466697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10430457461234546505244525 3911421547962954939466697)
        ·
          refine ⟨2933566160972216204600023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3911421547962954939466697 2933566160972216204600023)
          ·
            refine ⟨4400349241458324306900035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933566160972216204600023 4400349241458324306900035)
            ·
              refine ⟨6600523862187486460350053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4400349241458324306900035 6600523862187486460350053)
              ·
                refine ⟨1237598224160153711315635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6600523862187486460350053 1237598224160153711315635)
                ·
                  refine ⟨1856397336240230566973453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1237598224160153711315635 1856397336240230566973453)
                  ·
                    refine ⟨696149001090086462615045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1856397336240230566973453 696149001090086462615045)
                    ·
                      rfl

theorem cell22_2033618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_2033618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033618 prefixEnd_2033618 := by exact prefixLift 2033618
  have htrace : WordTrace (prefixWord ++ tailWord_2033618) baseStart_2033618 baseEnd_2033618 := by
    simpa [prefixWord, tailWord_2033618, baseEnd_2033618] using wordTrace_append hprefix tailTrace_2033618
  have hstable : (prefixWord ++ tailWord_2033618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033618).length < 2 ^ (prefixWord ++ tailWord_2033618).sum := by decide
  have hdescent : baseEnd_2033618 < baseStart_2033618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033629 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_2033629 : Nat := 118140960795 + 2033629 * 2 ^ 59
def prefixEnd_2033629 : Nat := 4983230072969 + 3 ^ 40 * 2033629 * 2
def baseEnd_2033629 : Nat := 696152766614886100590011

theorem tailTrace_2033629 : CollatzResearch.WordTrace tailWord_2033629 prefixEnd_2033629 696152766614886100590011 := by
  unfold tailWord_2033629
  simp only [CollatzResearch.WordTrace]
  refine ⟨74172543149516924027055941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49448362099677949351370627 74172543149516924027055941)
  ·
    refine ⟨13907351840534423255072989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74172543149516924027055941 13907351840534423255072989)
    ·
      refine ⟨5215256940200408720652371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13907351840534423255072989 5215256940200408720652371)
      ·
        refine ⟨7822885410300613080978557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5215256940200408720652371 7822885410300613080978557)
        ·
          refine ⟨2933582028862729905366959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7822885410300613080978557 2933582028862729905366959)
          ·
            refine ⟨4400373043294094858050439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933582028862729905366959 4400373043294094858050439)
            ·
              refine ⟨6600559564941142287075659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4400373043294094858050439 6600559564941142287075659)
              ·
                refine ⟨9900839347411713430613489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6600559564941142287075659 9900839347411713430613489)
                ·
                  refine ⟨7425629510558785072960117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9900839347411713430613489 7425629510558785072960117)
                  ·
                    refine ⟨696152766614886100590011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7425629510558785072960117 696152766614886100590011)
                    ·
                      rfl

theorem cell22_2033629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_2033629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033629 prefixEnd_2033629 := by exact prefixLift 2033629
  have htrace : WordTrace (prefixWord ++ tailWord_2033629) baseStart_2033629 baseEnd_2033629 := by
    simpa [prefixWord, tailWord_2033629, baseEnd_2033629] using wordTrace_append hprefix tailTrace_2033629
  have hstable : (prefixWord ++ tailWord_2033629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033629).length < 2 ^ (prefixWord ++ tailWord_2033629).sum := by decide
  have hdescent : baseEnd_2033629 < baseStart_2033629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033642 : List Nat := [3, 1, 3, 1, 2, 1, 3, 2, 6]
def baseStart_2033642 : Nat := 118140960795 + 2033642 * 2 ^ 59
def prefixEnd_2033642 : Nat := 4983230072969 + 3 ^ 40 * 2033642 * 2
def baseEnd_2033642 : Nat := 232052405593519466671657

theorem tailTrace_2033642 : CollatzResearch.WordTrace tailWord_2033642 prefixEnd_2033642 232052405593519466671657 := by
  unfold tailWord_2033642
  simp only [CollatzResearch.WordTrace]
  refine ⟨18543254324617456811819795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49448678198979884831519453 18543254324617456811819795)
  ·
    refine ⟨27814881486926185217729693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18543254324617456811819795 27814881486926185217729693)
    ·
      refine ⟨10430580557597319456648635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27814881486926185217729693 10430580557597319456648635)
      ·
        refine ⟨15645870836395979184972953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10430580557597319456648635 15645870836395979184972953)
        ·
          refine ⟨11734403127296984388729715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15645870836395979184972953 11734403127296984388729715)
          ·
            refine ⟨17601604690945476583094573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11734403127296984388729715 17601604690945476583094573)
            ·
              refine ⟨6600601759104553718660465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17601604690945476583094573 6600601759104553718660465)
              ·
                refine ⟨4950451319328415288995349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6600601759104553718660465 4950451319328415288995349)
                ·
                  refine ⟨232052405593519466671657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4950451319328415288995349 232052405593519466671657)
                  ·
                    rfl

theorem cell22_2033642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_2033642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033642 prefixEnd_2033642 := by exact prefixLift 2033642
  have htrace : WordTrace (prefixWord ++ tailWord_2033642) baseStart_2033642 baseEnd_2033642 := by
    simpa [prefixWord, tailWord_2033642, baseEnd_2033642] using wordTrace_append hprefix tailTrace_2033642
  have hstable : (prefixWord ++ tailWord_2033642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033642).length < 2 ^ (prefixWord ++ tailWord_2033642).sum := by decide
  have hdescent : baseEnd_2033642 < baseStart_2033642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033657 : List Nat := [1, 2, 1, 3, 1, 4, 2, 2, 1, 5]
def baseStart_2033657 : Nat := 118140960795 + 2033657 * 2 ^ 59
def prefixEnd_2033657 : Nat := 4983230072969 + 3 ^ 40 * 2033657 * 2
def baseEnd_2033657 : Nat := 696162351587103360889925

theorem tailTrace_2033657 : CollatzResearch.WordTrace tailWord_2033657 prefixEnd_2033657 696162351587103360889925 := by
  unfold tailWord_2033657
  simp only [CollatzResearch.WordTrace]
  refine ⟨74173564393415484809075225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49449042928943656539383483 74173564393415484809075225)
  ·
    refine ⟨55630173295061613606806419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74173564393415484809075225 55630173295061613606806419)
    ·
      refine ⟨83445259942592420410209629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55630173295061613606806419 83445259942592420410209629)
      ·
        refine ⟨31291972478472157653828611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83445259942592420410209629 31291972478472157653828611)
        ·
          refine ⟨46937958717708236480742917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31291972478472157653828611 46937958717708236480742917)
          ·
            refine ⟨8800867259570294340139297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46937958717708236480742917 8800867259570294340139297)
            ·
              refine ⟨6600650444677720755104473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8800867259570294340139297 6600650444677720755104473)
              ·
                refine ⟨4950487833508290566328355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6600650444677720755104473 4950487833508290566328355)
                ·
                  refine ⟨7425731750262435849492533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4950487833508290566328355 7425731750262435849492533)
                  ·
                    refine ⟨696162351587103360889925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7425731750262435849492533 696162351587103360889925)
                    ·
                      rfl

theorem cell22_2033657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_2033657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033657 prefixEnd_2033657 := by exact prefixLift 2033657
  have htrace : WordTrace (prefixWord ++ tailWord_2033657) baseStart_2033657 baseEnd_2033657 := by
    simpa [prefixWord, tailWord_2033657, baseEnd_2033657] using wordTrace_append hprefix tailTrace_2033657
  have hstable : (prefixWord ++ tailWord_2033657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033657).length < 2 ^ (prefixWord ++ tailWord_2033657).sum := by decide
  have hdescent : baseEnd_2033657 < baseStart_2033657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033672 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 4, 4]
def baseStart_2033672 : Nat := 118140960795 + 2033672 * 2 ^ 59
def prefixEnd_2033672 : Nat := 4983230072969 + 3 ^ 40 * 2033672 * 2
def baseEnd_2033672 : Nat := 696167486393648321764879

theorem tailTrace_2033672 : CollatzResearch.WordTrace tailWord_2033672 prefixEnd_2033672 696167486393648321764879 := by
  unfold tailWord_2033672
  simp only [CollatzResearch.WordTrace]
  refine ⟨37087055744180571185435635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49449407658907428247247513 37087055744180571185435635)
  ·
    refine ⟨55630583616270856778153453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37087055744180571185435635 55630583616270856778153453)
    ·
      refine ⟨20861468856101571291807545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55630583616270856778153453 20861468856101571291807545)
      ·
        refine ⟨15646101642076178468855659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20861468856101571291807545 15646101642076178468855659)
        ·
          refine ⟨23469152463114267703283489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15646101642076178468855659 23469152463114267703283489)
          ·
            refine ⟨17601864347335700777462617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23469152463114267703283489 17601864347335700777462617)
            ·
              refine ⟨13201398260501775583096963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17601864347335700777462617 13201398260501775583096963)
              ·
                refine ⟨19802097390752663374645445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13201398260501775583096963 19802097390752663374645445)
                ·
                  refine ⟨3712893260766124382746021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19802097390752663374645445 3712893260766124382746021)
                  ·
                    refine ⟨696167486393648321764879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3712893260766124382746021 696167486393648321764879)
                    ·
                      rfl

theorem cell22_2033672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_2033672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033672 prefixEnd_2033672 := by exact prefixLift 2033672
  have htrace : WordTrace (prefixWord ++ tailWord_2033672) baseStart_2033672 baseEnd_2033672 := by
    simpa [prefixWord, tailWord_2033672, baseEnd_2033672] using wordTrace_append hprefix tailTrace_2033672
  have hstable : (prefixWord ++ tailWord_2033672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033672).length < 2 ^ (prefixWord ++ tailWord_2033672).sum := by decide
  have hdescent : baseEnd_2033672 < baseStart_2033672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033749 : List Nat := [1, 3, 2, 2, 1, 4, 1, 3, 5]
def baseStart_2033749 : Nat := 118140960795 + 2033749 * 2 ^ 59
def prefixEnd_2033749 : Nat := 4983230072969 + 3 ^ 40 * 2033749 * 2
def baseEnd_2033749 : Nat := 232064615022415262529881

theorem tailTrace_2033749 : CollatzResearch.WordTrace tailWord_2033749 prefixEnd_2033749 232064615022415262529881 := by
  unfold tailWord_2033749
  simp only [CollatzResearch.WordTrace]
  refine ⟨74176919909082184521424301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49451279939388123014282867 74176919909082184521424301)
  ·
    refine ⟨27816344965905819195534113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74176919909082184521424301 27816344965905819195534113)
    ·
      refine ⟨20862258724429364396650585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27816344965905819195534113 20862258724429364396650585)
      ·
        refine ⟨15646694043322023297487939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20862258724429364396650585 15646694043322023297487939)
        ·
          refine ⟨23470041064983034946231909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15646694043322023297487939 23470041064983034946231909)
          ·
            refine ⟨4400632699684319052418483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23470041064983034946231909 4400632699684319052418483)
            ·
              refine ⟨6600949049526478578627725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4400632699684319052418483 6600949049526478578627725)
              ·
                refine ⟨2475355893572429466985397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6600949049526478578627725 2475355893572429466985397)
                ·
                  refine ⟨232064615022415262529881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2475355893572429466985397 232064615022415262529881)
                  ·
                    rfl

theorem cell22_2033749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_2033749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033749 prefixEnd_2033749 := by exact prefixLift 2033749
  have htrace : WordTrace (prefixWord ++ tailWord_2033749) baseStart_2033749 baseEnd_2033749 := by
    simpa [prefixWord, tailWord_2033749, baseEnd_2033749] using wordTrace_append hprefix tailTrace_2033749
  have hstable : (prefixWord ++ tailWord_2033749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033749).length < 2 ^ (prefixWord ++ tailWord_2033749).sum := by decide
  have hdescent : baseEnd_2033749 < baseStart_2033749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033792 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 5, 5]
def baseStart_2033792 : Nat := 118140960795 + 2033792 * 2 ^ 59
def prefixEnd_2033792 : Nat := 4983230072969 + 3 ^ 40 * 2033792 * 2
def baseEnd_2033792 : Nat := 696208564846008008764511

theorem tailTrace_2033792 : CollatzResearch.WordTrace tailWord_2033792 prefixEnd_2033792 696208564846008008764511 := by
  unfold tailWord_2033792
  simp only [CollatzResearch.WordTrace]
  refine ⟨37089244123963201432619815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49452325498617601910159753 37089244123963201432619815)
  ·
    refine ⟨55633866185944802148929723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37089244123963201432619815 55633866185944802148929723)
    ·
      refine ⟨83450799278917203223394585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55633866185944802148929723 83450799278917203223394585)
      ·
        refine ⟨62588099459187902417545939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83450799278917203223394585 62588099459187902417545939)
        ·
          refine ⟨93882149188781853626318909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62588099459187902417545939 93882149188781853626318909)
          ·
            refine ⟨35205805945793195109869591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93882149188781853626318909 35205805945793195109869591)
            ·
              refine ⟨52808708918689792664804387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35205805945793195109869591 52808708918689792664804387)
              ·
                refine ⟨79213063378034688997206581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52808708918689792664804387 79213063378034688997206581)
                ·
                  refine ⟨7426224691690752093488117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79213063378034688997206581 7426224691690752093488117)
                  ·
                    refine ⟨696208564846008008764511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7426224691690752093488117 696208564846008008764511)
                    ·
                      rfl

theorem cell22_2033792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_2033792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033792 prefixEnd_2033792 := by exact prefixLift 2033792
  have htrace : WordTrace (prefixWord ++ tailWord_2033792) baseStart_2033792 baseEnd_2033792 := by
    simpa [prefixWord, tailWord_2033792, baseEnd_2033792] using wordTrace_append hprefix tailTrace_2033792
  have hstable : (prefixWord ++ tailWord_2033792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033792).length < 2 ^ (prefixWord ++ tailWord_2033792).sum := by decide
  have hdescent : baseEnd_2033792 < baseStart_2033792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033824 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 1, 6]
def baseStart_2033824 : Nat := 118140960795 + 2033824 * 2 ^ 59
def prefixEnd_2033824 : Nat := 4983230072969 + 3 ^ 40 * 2033824 * 2
def baseEnd_2033824 : Nat := 696219519099970591964413

theorem tailTrace_2033824 : CollatzResearch.WordTrace tailWord_2033824 prefixEnd_2033824 696219519099970591964413 := by
  unfold tailWord_2033824
  simp only [CollatzResearch.WordTrace]
  refine ⟨37089827691905236165202263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49453103589206981553603017 37089827691905236165202263)
  ·
    refine ⟨55634741537857854247803395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37089827691905236165202263 55634741537857854247803395)
    ·
      refine ⟨83452112306786781371705093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55634741537857854247803395 83452112306786781371705093)
      ·
        refine ⟨15647271057522521507194705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83452112306786781371705093 15647271057522521507194705)
        ·
          refine ⟨11735453293141891130396029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15647271057522521507194705 11735453293141891130396029)
          ·
            refine ⟨4400794984928209173898511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11735453293141891130396029 4400794984928209173898511)
            ·
              refine ⟨6601192477392313760847767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4400794984928209173898511 6601192477392313760847767)
              ·
                refine ⟨9901788716088470641271651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6601192477392313760847767 9901788716088470641271651)
                ·
                  refine ⟨14852683074132705961907477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9901788716088470641271651 14852683074132705961907477)
                  ·
                    refine ⟨696219519099970591964413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14852683074132705961907477 696219519099970591964413)
                    ·
                      rfl

theorem cell22_2033824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_2033824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033824 prefixEnd_2033824 := by exact prefixLift 2033824
  have htrace : WordTrace (prefixWord ++ tailWord_2033824) baseStart_2033824 baseEnd_2033824 := by
    simpa [prefixWord, tailWord_2033824, baseEnd_2033824] using wordTrace_append hprefix tailTrace_2033824
  have hstable : (prefixWord ++ tailWord_2033824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033824).length < 2 ^ (prefixWord ++ tailWord_2033824).sum := by decide
  have hdescent : baseEnd_2033824 < baseStart_2033824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033826 : List Nat := [3, 3, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_2033826 : Nat := 118140960795 + 2033826 * 2 ^ 59
def prefixEnd_2033826 : Nat := 4983230072969 + 3 ^ 40 * 2033826 * 2
def baseEnd_2033826 : Nat := 696220203740843253414407

theorem tailTrace_2033826 : CollatzResearch.WordTrace tailWord_2033826 prefixEnd_2033826 696220203740843253414407 := by
  unfold tailWord_2033826
  simp only [CollatzResearch.WordTrace]
  refine ⟨18544932082450806667994333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49453152219868817781318221 18544932082450806667994333)
  ·
    refine ⟨6954349530919052500497875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18544932082450806667994333 6954349530919052500497875)
    ·
      refine ⟨10431524296378578750746813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6954349530919052500497875 10431524296378578750746813)
      ·
        refine ⟨3911821611141967031530055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10431524296378578750746813 3911821611141967031530055)
        ·
          refine ⟨5867732416712950547295083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3911821611141967031530055 5867732416712950547295083)
          ·
            refine ⟨8801598625069425820942625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5867732416712950547295083 8801598625069425820942625)
            ·
              refine ⟨6601198968802069365706969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8801598625069425820942625 6601198968802069365706969)
              ·
                refine ⟨4950899226601552024280227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6601198968802069365706969 4950899226601552024280227)
                ·
                  refine ⟨7426348839902328036420341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4950899226601552024280227 7426348839902328036420341)
                  ·
                    refine ⟨696220203740843253414407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7426348839902328036420341 696220203740843253414407)
                    ·
                      rfl

theorem cell22_2033826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_2033826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033826 prefixEnd_2033826 := by exact prefixLift 2033826
  have htrace : WordTrace (prefixWord ++ tailWord_2033826) baseStart_2033826 baseEnd_2033826 := by
    simpa [prefixWord, tailWord_2033826, baseEnd_2033826] using wordTrace_append hprefix tailTrace_2033826
  have hstable : (prefixWord ++ tailWord_2033826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033826).length < 2 ^ (prefixWord ++ tailWord_2033826).sum := by decide
  have hdescent : baseEnd_2033826 < baseStart_2033826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033828 : List Nat := [2, 3, 1, 2, 4, 1, 2, 3, 4]
def baseStart_2033828 : Nat := 118140960795 + 2033828 * 2 ^ 59
def prefixEnd_2033828 : Nat := 4983230072969 + 3 ^ 40 * 2033828 * 2
def baseEnd_2033828 : Nat := 232073629460571971621467

theorem tailTrace_2033828 : CollatzResearch.WordTrace tailWord_2033828 prefixEnd_2033828 232073629460571971621467 := by
  unfold tailWord_2033828
  simp only [CollatzResearch.WordTrace]
  refine ⟨37089900637897990506775069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49453200850530654009033425 37089900637897990506775069)
  ·
    refine ⟨13908712739211746440040651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37089900637897990506775069 13908712739211746440040651)
    ·
      refine ⟨20863069108817619660060977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13908712739211746440040651 20863069108817619660060977)
      ·
        refine ⟨15647301831613214745045733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20863069108817619660060977 15647301831613214745045733)
        ·
          refine ⟨2933869093427477764696075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15647301831613214745045733 2933869093427477764696075)
          ·
            refine ⟨4400803640141216647044113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933869093427477764696075 4400803640141216647044113)
            ·
              refine ⟨3300602730105912485283085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4400803640141216647044113 3300602730105912485283085)
              ·
                refine ⟨1237726023789717181981157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3300602730105912485283085 1237726023789717181981157)
                ·
                  refine ⟨232073629460571971621467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1237726023789717181981157 232073629460571971621467)
                  ·
                    rfl

theorem cell22_2033828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_2033828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033828 prefixEnd_2033828 := by exact prefixLift 2033828
  have htrace : WordTrace (prefixWord ++ tailWord_2033828) baseStart_2033828 baseEnd_2033828 := by
    simpa [prefixWord, tailWord_2033828, baseEnd_2033828] using wordTrace_append hprefix tailTrace_2033828
  have hstable : (prefixWord ++ tailWord_2033828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033828).length < 2 ^ (prefixWord ++ tailWord_2033828).sum := by decide
  have hdescent : baseEnd_2033828 < baseStart_2033828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033858 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_2033858 : Nat := 118140960795 + 2033858 * 2 ^ 59
def prefixEnd_2033858 : Nat := 4983230072969 + 3 ^ 40 * 2033858 * 2
def baseEnd_2033858 : Nat := 696231157994805836614309

theorem tailTrace_2033858 : CollatzResearch.WordTrace tailWord_2033858 prefixEnd_2033858 696231157994805836614309 := by
  unfold tailWord_2033858
  simp only [CollatzResearch.WordTrace]
  refine ⟨18545223866421824034285557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49453930310458197424761485 18545223866421824034285557)
  ·
    refine ⟨1738614737477046003214271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18545223866421824034285557 1738614737477046003214271)
    ·
      refine ⟨2607922106215569004821407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1738614737477046003214271 2607922106215569004821407)
      ·
        refine ⟨3911883159323353507232111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2607922106215569004821407 3911883159323353507232111)
        ·
          refine ⟨5867824738985030260848167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3911883159323353507232111 5867824738985030260848167)
          ·
            refine ⟨8801737108477545391272251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5867824738985030260848167 8801737108477545391272251)
            ·
              refine ⟨13202605662716318086908377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8801737108477545391272251 13202605662716318086908377)
              ·
                refine ⟨9901954247037238565181283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13202605662716318086908377 9901954247037238565181283)
                ·
                  refine ⟨14852931370555857847771925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9901954247037238565181283 14852931370555857847771925)
                  ·
                    refine ⟨696231157994805836614309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14852931370555857847771925 696231157994805836614309)
                    ·
                      rfl

theorem cell22_2033858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_2033858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033858 prefixEnd_2033858 := by exact prefixLift 2033858
  have htrace : WordTrace (prefixWord ++ tailWord_2033858) baseStart_2033858 baseEnd_2033858 := by
    simpa [prefixWord, tailWord_2033858, baseEnd_2033858] using wordTrace_append hprefix tailTrace_2033858
  have hstable : (prefixWord ++ tailWord_2033858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033858).length < 2 ^ (prefixWord ++ tailWord_2033858).sum := by decide
  have hdescent : baseEnd_2033858 < baseStart_2033858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033860 : List Nat := [2, 3, 3, 1, 2, 2, 3, 1, 2, 3]
def baseStart_2033860 : Nat := 118140960795 + 2033860 * 2 ^ 59
def prefixEnd_2033860 : Nat := 4983230072969 + 3 ^ 40 * 2033860 * 2
def baseEnd_2033860 : Nat := 696231842635678498064303

theorem tailTrace_2033860 : CollatzResearch.WordTrace tailWord_2033860 prefixEnd_2033860 696231842635678498064303 := by
  unfold tailWord_2033860
  simp only [CollatzResearch.WordTrace]
  refine ⟨37090484205840025239357517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49453978941120033652476689 37090484205840025239357517)
  ·
    refine ⟨13908931577190009464759069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37090484205840025239357517 13908931577190009464759069)
    ·
      refine ⟨5215849341446253549284651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13908931577190009464759069 5215849341446253549284651)
      ·
        refine ⟨7823774012169380323926977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5215849341446253549284651 7823774012169380323926977)
        ·
          refine ⟨5867830509127035242945233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7823774012169380323926977 5867830509127035242945233)
          ·
            refine ⟨4400872881845276432208925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5867830509127035242945233 4400872881845276432208925)
            ·
              refine ⟨1650327330691978662078347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4400872881845276432208925 1650327330691978662078347)
              ·
                refine ⟨2475490996037967993117521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650327330691978662078347 2475490996037967993117521)
                ·
                  refine ⟨1856618247028475994838141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2475490996037967993117521 1856618247028475994838141)
                  ·
                    refine ⟨696231842635678498064303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1856618247028475994838141 696231842635678498064303)
                    ·
                      rfl

theorem cell22_2033860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_2033860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033860 prefixEnd_2033860 := by exact prefixLift 2033860
  have htrace : WordTrace (prefixWord ++ tailWord_2033860) baseStart_2033860 baseEnd_2033860 := by
    simpa [prefixWord, tailWord_2033860, baseEnd_2033860] using wordTrace_append hprefix tailTrace_2033860
  have hstable : (prefixWord ++ tailWord_2033860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033860).length < 2 ^ (prefixWord ++ tailWord_2033860).sum := by decide
  have hdescent : baseEnd_2033860 < baseStart_2033860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033890 : List Nat := [3, 3, 4, 1, 1, 2, 8]
def baseStart_2033890 : Nat := 118140960795 + 2033890 * 2 ^ 59
def prefixEnd_2033890 : Nat := 4983230072969 + 3 ^ 40 * 2033890 * 2
def baseEnd_2033890 : Nat := 25786744898102534067193

theorem tailTrace_2033890 : CollatzResearch.WordTrace tailWord_2033890 prefixEnd_2033890 25786744898102534067193 := by
  unfold tailWord_2033890
  simp only [CollatzResearch.WordTrace]
  refine ⟨18545515650392841400576781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49454708401047577068204749 18545515650392841400576781)
  ·
    refine ⟨6954568368897315525216293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18545515650392841400576781 6954568368897315525216293)
    ·
      refine ⟨1303981569168246660978055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6954568368897315525216293 1303981569168246660978055)
      ·
        refine ⟨1955972353752369991467083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1303981569168246660978055 1955972353752369991467083)
        ·
          refine ⟨2933958530628554987200625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1955972353752369991467083 2933958530628554987200625)
          ·
            refine ⟨2200468897971416240400469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2933958530628554987200625 2200468897971416240400469)
            ·
              refine ⟨25786744898102534067193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2200468897971416240400469 25786744898102534067193)
              ·
                rfl

theorem cell22_2033890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 8].length) (baseStart_2033890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033890 prefixEnd_2033890 := by exact prefixLift 2033890
  have htrace : WordTrace (prefixWord ++ tailWord_2033890) baseStart_2033890 baseEnd_2033890 := by
    simpa [prefixWord, tailWord_2033890, baseEnd_2033890] using wordTrace_append hprefix tailTrace_2033890
  have hstable : (prefixWord ++ tailWord_2033890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033890).length < 2 ^ (prefixWord ++ tailWord_2033890).sum := by decide
  have hdescent : baseEnd_2033890 < baseStart_2033890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033978 : List Nat := [3, 1, 1, 1, 4, 2, 2, 3, 2, 3]
def baseStart_2033978 : Nat := 118140960795 + 2033978 * 2 ^ 59
def prefixEnd_2033978 : Nat := 4983230072969 + 3 ^ 40 * 2033978 * 2
def baseEnd_2033978 : Nat := 696272236447165523613941

theorem tailTrace_2033978 : CollatzResearch.WordTrace tailWord_2033978 prefixEnd_2033978 696272236447165523613941 := by
  unfold tailWord_2033978
  simp only [CollatzResearch.WordTrace]
  refine ⟨18546318056313139157877647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49456848150168371087673725 18546318056313139157877647)
  ·
    refine ⟨27819477084469708736816471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18546318056313139157877647 27819477084469708736816471)
    ·
      refine ⟨41729215626704563105224707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27819477084469708736816471 41729215626704563105224707)
      ·
        refine ⟨62593823440056844657837061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41729215626704563105224707 62593823440056844657837061)
        ·
          refine ⟨11736341895010658373344449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62593823440056844657837061 11736341895010658373344449)
          ·
            refine ⟨8802256421257993780008337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11736341895010658373344449 8802256421257993780008337)
            ·
              refine ⟨6601692315943495335006253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8802256421257993780008337 6601692315943495335006253)
              ·
                refine ⟨2475634618478810750627345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6601692315943495335006253 2475634618478810750627345)
                ·
                  refine ⟨1856725963859108062970509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2475634618478810750627345 1856725963859108062970509)
                  ·
                    refine ⟨696272236447165523613941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1856725963859108062970509 696272236447165523613941)
                    ·
                      rfl

theorem cell22_2033978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_2033978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033978 prefixEnd_2033978 := by exact prefixLift 2033978
  have htrace : WordTrace (prefixWord ++ tailWord_2033978) baseStart_2033978 baseEnd_2033978 := by
    simpa [prefixWord, tailWord_2033978, baseEnd_2033978] using wordTrace_append hprefix tailTrace_2033978
  have hstable : (prefixWord ++ tailWord_2033978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033978).length < 2 ^ (prefixWord ++ tailWord_2033978).sum := by decide
  have hdescent : baseEnd_2033978 < baseStart_2033978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033991 : List Nat := [1, 1, 4, 1, 2, 2, 5, 6]
def baseStart_2033991 : Nat := 118140960795 + 2033991 * 2 ^ 59
def prefixEnd_2033991 : Nat := 4983230072969 + 3 ^ 40 * 2033991 * 2
def baseEnd_2033991 : Nat := 77364076290315313670989

theorem tailTrace_2033991 : CollatzResearch.WordTrace tailWord_2033991 prefixEnd_2033991 77364076290315313670989 := by
  unfold tailWord_2033991
  simp only [CollatzResearch.WordTrace]
  refine ⟨74185746374205459851733827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49457164249470306567822551 74185746374205459851733827)
  ·
    refine ⟨111278619561308189777600741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74185746374205459851733827 111278619561308189777600741)
    ·
      refine ⟨20864741167745285583300139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111278619561308189777600741 20864741167745285583300139)
      ·
        refine ⟨31297111751617928374950209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20864741167745285583300139 31297111751617928374950209)
        ·
          refine ⟨23472833813713446281212657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31297111751617928374950209 23472833813713446281212657)
          ·
            refine ⟨17604625360285084710909493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23472833813713446281212657 17604625360285084710909493)
            ·
              refine ⟨1650433627526726691647765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17604625360285084710909493 1650433627526726691647765)
              ·
                refine ⟨77364076290315313670989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1650433627526726691647765 77364076290315313670989)
                ·
                  rfl

theorem cell22_2033991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 6].length) (baseStart_2033991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2033991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2033991 prefixEnd_2033991 := by exact prefixLift 2033991
  have htrace : WordTrace (prefixWord ++ tailWord_2033991) baseStart_2033991 baseEnd_2033991 := by
    simpa [prefixWord, tailWord_2033991, baseEnd_2033991] using wordTrace_append hprefix tailTrace_2033991
  have hstable : (prefixWord ++ tailWord_2033991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033991).length < 2 ^ (prefixWord ++ tailWord_2033991).sum := by decide
  have hdescent : baseEnd_2033991 < baseStart_2033991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034014 : List Nat := [4, 4, 2, 1, 1, 1, 2, 1, 6]
def baseStart_2034014 : Nat := 118140960795 + 2034014 * 2 ^ 59
def prefixEnd_2034014 : Nat := 4983230072969 + 3 ^ 40 * 2034014 * 2
def baseEnd_2034014 : Nat := 232094853327624476571277

theorem tailTrace_2034014 : CollatzResearch.WordTrace tailWord_2034014 prefixEnd_2034014 232094853327624476571277 := by
  unfold tailWord_2034014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9273323156640266847477637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49457723502081423186547397 9273323156640266847477637)
  ·
    refine ⟨1738748091870050033902057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9273323156640266847477637 1738748091870050033902057)
    ·
      refine ⟨1304061068902537525426543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1738748091870050033902057 1304061068902537525426543)
      ·
        refine ⟨1956091603353806288139815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1304061068902537525426543 1956091603353806288139815)
        ·
          refine ⟨2934137405030709432209723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1956091603353806288139815 2934137405030709432209723)
          ·
            refine ⟨4401206107546064148314585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2934137405030709432209723 4401206107546064148314585)
            ·
              refine ⟨3300904580659548111235939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4401206107546064148314585 3300904580659548111235939)
              ·
                refine ⟨4951356870989322166853909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300904580659548111235939 4951356870989322166853909)
                ·
                  refine ⟨232094853327624476571277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4951356870989322166853909 232094853327624476571277)
                  ·
                    rfl

theorem cell22_2034014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_2034014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034014 prefixEnd_2034014 := by exact prefixLift 2034014
  have htrace : WordTrace (prefixWord ++ tailWord_2034014) baseStart_2034014 baseEnd_2034014 := by
    simpa [prefixWord, tailWord_2034014, baseEnd_2034014] using wordTrace_append hprefix tailTrace_2034014
  have hstable : (prefixWord ++ tailWord_2034014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034014).length < 2 ^ (prefixWord ++ tailWord_2034014).sum := by decide
  have hdescent : baseEnd_2034014 < baseStart_2034014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034023 : List Nat := [1, 1, 5, 1, 3, 1, 1, 3, 3, 3]
def baseStart_2034023 : Nat := 118140960795 + 2034023 * 2 ^ 59
def prefixEnd_2034023 : Nat := 4983230072969 + 3 ^ 40 * 2034023 * 2
def baseEnd_2034023 : Nat := 696287640866800406238803

theorem tailTrace_2034023 : CollatzResearch.WordTrace tailWord_2034023 prefixEnd_2034023 696287640866800406238803 := by
  unfold tailWord_2034023
  simp only [CollatzResearch.WordTrace]
  refine ⟨74186913510089529316898723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49457942340059686211265815 74186913510089529316898723)
  ·
    refine ⟨111280370265134293975348085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74186913510089529316898723 111280370265134293975348085)
    ·
      refine ⟨10432534712356340060188883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111280370265134293975348085 10432534712356340060188883)
      ·
        refine ⟨15648802068534510090283325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10432534712356340060188883 15648802068534510090283325)
        ·
          refine ⟨5868300775700441283856247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15648802068534510090283325 5868300775700441283856247)
          ·
            refine ⟨8802451163550661925784371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5868300775700441283856247 8802451163550661925784371)
            ·
              refine ⟨13203676745325992888676557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8802451163550661925784371 13203676745325992888676557)
              ·
                refine ⟨4951378779497247333253709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13203676745325992888676557 4951378779497247333253709)
                ·
                  refine ⟨1856767042311467749970141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4951378779497247333253709 1856767042311467749970141)
                  ·
                    refine ⟨696287640866800406238803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1856767042311467749970141 696287640866800406238803)
                    ·
                      rfl

theorem cell22_2034023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_2034023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034023 prefixEnd_2034023 := by exact prefixLift 2034023
  have htrace : WordTrace (prefixWord ++ tailWord_2034023) baseStart_2034023 baseEnd_2034023 := by
    simpa [prefixWord, tailWord_2034023, baseEnd_2034023] using wordTrace_append hprefix tailTrace_2034023
  have hstable : (prefixWord ++ tailWord_2034023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034023).length < 2 ^ (prefixWord ++ tailWord_2034023).sum := by decide
  have hdescent : baseEnd_2034023 < baseStart_2034023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034057 : List Nat := [1, 2, 1, 1, 6, 3, 1, 3, 1, 3]
def baseStart_2034057 : Nat := 118140960795 + 2034057 * 2 ^ 59
def prefixEnd_2034057 : Nat := 4983230072969 + 3 ^ 40 * 2034057 * 2
def baseEnd_2034057 : Nat := 696299279761635650888699

theorem tailTrace_2034057 : CollatzResearch.WordTrace tailWord_2034057 prefixEnd_2034057 696299279761635650888699 := by
  unfold tailWord_2034057
  simp only [CollatzResearch.WordTrace]
  refine ⟨74188153591966353123636425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49458769061310902082424283 74188153591966353123636425)
  ·
    refine ⟨55641115193974764842727319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74188153591966353123636425 55641115193974764842727319)
    ·
      refine ⟨83461672790962147264090979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55641115193974764842727319 83461672790962147264090979)
      ·
        refine ⟨125192509186443220896136469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83461672790962147264090979 125192509186443220896136469)
        ·
          refine ⟨5868398868114525979506397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125192509186443220896136469 5868398868114525979506397)
          ·
            refine ⟨2200649575542947242314899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5868398868114525979506397 2200649575542947242314899)
            ·
              refine ⟨3300974363314420863472349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200649575542947242314899 3300974363314420863472349)
              ·
                refine ⟨1237865386242907823802131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3300974363314420863472349 1237865386242907823802131)
                ·
                  refine ⟨1856798079364361735703197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1237865386242907823802131 1856798079364361735703197)
                  ·
                    refine ⟨696299279761635650888699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1856798079364361735703197 696299279761635650888699)
                    ·
                      rfl

theorem cell22_2034057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 1, 3].length) (baseStart_2034057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034057 prefixEnd_2034057 := by exact prefixLift 2034057
  have htrace : WordTrace (prefixWord ++ tailWord_2034057) baseStart_2034057 baseEnd_2034057 := by
    simpa [prefixWord, tailWord_2034057, baseEnd_2034057] using wordTrace_append hprefix tailTrace_2034057
  have hstable : (prefixWord ++ tailWord_2034057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034057).length < 2 ^ (prefixWord ++ tailWord_2034057).sum := by decide
  have hdescent : baseEnd_2034057 < baseStart_2034057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034132 : List Nat := [2, 4, 1, 2, 2, 1, 4, 2, 4]
def baseStart_2034132 : Nat := 118140960795 + 2034132 * 2 ^ 59
def prefixEnd_2034132 : Nat := 4983230072969 + 3 ^ 40 * 2034132 * 2
def baseEnd_2034132 : Nat := 232108317931453485087823

theorem tailTrace_2034132 : CollatzResearch.WordTrace tailWord_2034132 prefixEnd_2034132 232108317931453485087823 := by
  unfold tailWord_2034132
  simp only [CollatzResearch.WordTrace]
  refine ⟨37095444533347320466308325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49460592711129760621744433 37095444533347320466308325)
  ·
    refine ⟨6955395850002622587432811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37095444533347320466308325 6955395850002622587432811)
    ·
      refine ⟨10433093775003933881149217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6955395850002622587432811 10433093775003933881149217)
      ·
        refine ⟨7824820331252950410861913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10433093775003933881149217 7824820331252950410861913)
        ·
          refine ⟨5868615248439712808146435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7824820331252950410861913 5868615248439712808146435)
          ·
            refine ⟨8802922872659569212219653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5868615248439712808146435 8802922872659569212219653)
            ·
              refine ⟨1650548038623669227291185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8802922872659569212219653 1650548038623669227291185)
              ·
                refine ⟨1237911028967751920468389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1650548038623669227291185 1237911028967751920468389)
                ·
                  refine ⟨232108317931453485087823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1237911028967751920468389 232108317931453485087823)
                  ·
                    rfl

theorem cell22_2034132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_2034132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034132 prefixEnd_2034132 := by exact prefixLift 2034132
  have htrace : WordTrace (prefixWord ++ tailWord_2034132) baseStart_2034132 baseEnd_2034132 := by
    simpa [prefixWord, tailWord_2034132, baseEnd_2034132] using wordTrace_append hprefix tailTrace_2034132
  have hstable : (prefixWord ++ tailWord_2034132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034132).length < 2 ^ (prefixWord ++ tailWord_2034132).sum := by decide
  have hdescent : baseEnd_2034132 < baseStart_2034132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034143 : List Nat := [1, 1, 2, 3, 3, 4, 1, 7]
def baseStart_2034143 : Nat := 118140960795 + 2034143 * 2 ^ 59
def prefixEnd_2034143 : Nat := 4983230072969 + 3 ^ 40 * 2034143 * 2
def baseEnd_2034143 : Nat := 77369857702128899248715

theorem tailTrace_2034143 : CollatzResearch.WordTrace tailWord_2034143 prefixEnd_2034143 77369857702128899248715 := by
  unfold tailWord_2034143
  simp only [CollatzResearch.WordTrace]
  refine ⟨74191290269654789811267083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49460860179769859874178055 74191290269654789811267083)
  ·
    refine ⟨111286935404482184716900625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74191290269654789811267083 111286935404482184716900625)
    ·
      refine ⟨83465201553361638537675469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111286935404482184716900625 83465201553361638537675469)
      ·
        refine ⟨31299450582510614451628301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83465201553361638537675469 31299450582510614451628301)
        ·
          refine ⟨11737293968441480419360613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31299450582510614451628301 11737293968441480419360613)
          ·
            refine ⟨2200742619082777578630115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11737293968441480419360613 2200742619082777578630115)
            ·
              refine ⟨3301113928624166367945173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200742619082777578630115 3301113928624166367945173)
              ·
                refine ⟨77369857702128899248715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3301113928624166367945173 77369857702128899248715)
                ·
                  rfl

theorem cell22_2034143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 7].length) (baseStart_2034143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034143 prefixEnd_2034143 := by exact prefixLift 2034143
  have htrace : WordTrace (prefixWord ++ tailWord_2034143) baseStart_2034143 baseEnd_2034143 := by
    simpa [prefixWord, tailWord_2034143, baseEnd_2034143] using wordTrace_append hprefix tailTrace_2034143
  have hstable : (prefixWord ++ tailWord_2034143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034143).length < 2 ^ (prefixWord ++ tailWord_2034143).sum := by decide
  have hdescent : baseEnd_2034143 < baseStart_2034143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034156 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 2, 6]
def baseStart_2034156 : Nat := 118140960795 + 2034156 * 2 ^ 59
def prefixEnd_2034156 : Nat := 4983230072969 + 3 ^ 40 * 2034156 * 2
def baseEnd_2034156 : Nat := 696333169484832392663395

theorem tailTrace_2034156 : CollatzResearch.WordTrace tailWord_2034156 prefixEnd_2034156 696333169484832392663395 := by
  unfold tailWord_2034156
  simp only [CollatzResearch.WordTrace]
  refine ⟨37095882209303846515745161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49461176279071795354326881 37095882209303846515745161)
  ·
    refine ⟨27821911656977884886808871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37095882209303846515745161 27821911656977884886808871)
    ·
      refine ⟨41732867485466827330213307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27821911656977884886808871 41732867485466827330213307)
      ·
        refine ⟨62599301228200240995319961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41732867485466827330213307 62599301228200240995319961)
        ·
          refine ⟨46949475921150180746489971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62599301228200240995319961 46949475921150180746489971)
          ·
            refine ⟨70424213881725271119734957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46949475921150180746489971 70424213881725271119734957)
            ·
              refine ⟨26409080205646976669900609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70424213881725271119734957 26409080205646976669900609)
              ·
                refine ⟨19806810154235232502425457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26409080205646976669900609 19806810154235232502425457)
                ·
                  refine ⟨14855107615676424376819093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19806810154235232502425457 14855107615676424376819093)
                  ·
                    refine ⟨696333169484832392663395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14855107615676424376819093 696333169484832392663395)
                    ·
                      rfl

theorem cell22_2034156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_2034156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034156 prefixEnd_2034156 := by exact prefixLift 2034156
  have htrace : WordTrace (prefixWord ++ tailWord_2034156) baseStart_2034156 baseEnd_2034156 := by
    simpa [prefixWord, tailWord_2034156, baseEnd_2034156] using wordTrace_append hprefix tailTrace_2034156
  have hstable : (prefixWord ++ tailWord_2034156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034156).length < 2 ^ (prefixWord ++ tailWord_2034156).sum := by decide
  have hdescent : baseEnd_2034156 < baseStart_2034156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034162 : List Nat := [3, 2, 1, 4, 2, 2, 1, 1, 2, 4]
def baseStart_2034162 : Nat := 118140960795 + 2034162 * 2 ^ 59
def prefixEnd_2034162 : Nat := 4983230072969 + 3 ^ 40 * 2034162 * 2
def baseEnd_2034162 : Nat := 696335223407450377013377

theorem tailTrace_2034162 : CollatzResearch.WordTrace tailWord_2034162 prefixEnd_2034162 696335223407450377013377 := by
  unfold tailWord_2034162
  simp only [CollatzResearch.WordTrace]
  refine ⟨18547995814146489014052185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49461322171057304037472493 18547995814146489014052185)
  ·
    refine ⟨13910996860609866760539139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18547995814146489014052185 13910996860609866760539139)
    ·
      refine ⟨20866495290914800140808709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13910996860609866760539139 20866495290914800140808709)
      ·
        refine ⟨3912467867046525026401633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20866495290914800140808709 3912467867046525026401633)
        ·
          refine ⟨2934350900284893769801225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3912467867046525026401633 2934350900284893769801225)
          ·
            refine ⟨2200763175213670327350919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2934350900284893769801225 2200763175213670327350919)
            ·
              refine ⟨3301144762820505491026379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200763175213670327350919 3301144762820505491026379)
              ·
                refine ⟨4951717144230758236539569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3301144762820505491026379 4951717144230758236539569)
                ·
                  refine ⟨3713787858173068677404677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4951717144230758236539569 3713787858173068677404677)
                  ·
                    refine ⟨696335223407450377013377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3713787858173068677404677 696335223407450377013377)
                    ·
                      rfl

theorem cell22_2034162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_2034162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034162 prefixEnd_2034162 := by exact prefixLift 2034162
  have htrace : WordTrace (prefixWord ++ tailWord_2034162) baseStart_2034162 baseEnd_2034162 := by
    simpa [prefixWord, tailWord_2034162, baseEnd_2034162] using wordTrace_append hprefix tailTrace_2034162
  have hstable : (prefixWord ++ tailWord_2034162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034162).length < 2 ^ (prefixWord ++ tailWord_2034162).sum := by decide
  have hdescent : baseEnd_2034162 < baseStart_2034162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034188 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 7]
def baseStart_2034188 : Nat := 118140960795 + 2034188 * 2 ^ 59
def prefixEnd_2034188 : Nat := 4983230072969 + 3 ^ 40 * 2034188 * 2
def baseEnd_2034188 : Nat := 232114707912931658621099

theorem tailTrace_2034188 : CollatzResearch.WordTrace tailWord_2034188 prefixEnd_2034188 232114707912931658621099 := by
  unfold tailWord_2034188
  simp only [CollatzResearch.WordTrace]
  refine ⟨37096465777245881248327609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49461954369661174997770145 37096465777245881248327609)
  ·
    refine ⟨27822349332934410936245707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37096465777245881248327609 27822349332934410936245707)
    ·
      refine ⟨41733523999401616404368561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27822349332934410936245707 41733523999401616404368561)
      ·
        refine ⟨31300142999551212303276421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41733523999401616404368561 31300142999551212303276421)
        ·
          refine ⟨5868776812415852306864329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31300142999551212303276421 5868776812415852306864329)
          ·
            refine ⟨4401582609311889230148247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5868776812415852306864329 4401582609311889230148247)
            ·
              refine ⟨6602373913967833845222371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4401582609311889230148247 6602373913967833845222371)
              ·
                refine ⟨9903560870951750767833557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6602373913967833845222371 9903560870951750767833557)
                ·
                  refine ⟨232114707912931658621099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9903560870951750767833557 232114707912931658621099)
                  ·
                    rfl

theorem cell22_2034188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_2034188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034188 prefixEnd_2034188 := by exact prefixLift 2034188
  have htrace : WordTrace (prefixWord ++ tailWord_2034188) baseStart_2034188 baseEnd_2034188 := by
    simpa [prefixWord, tailWord_2034188, baseEnd_2034188] using wordTrace_append hprefix tailTrace_2034188
  have hstable : (prefixWord ++ tailWord_2034188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034188).length < 2 ^ (prefixWord ++ tailWord_2034188).sum := by decide
  have hdescent : baseEnd_2034188 < baseStart_2034188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034250 : List Nat := [3, 1, 2, 1, 1, 6, 1, 1, 6]
def baseStart_2034250 : Nat := 118140960795 + 2034250 * 2 ^ 59
def prefixEnd_2034250 : Nat := 4983230072969 + 3 ^ 40 * 2034250 * 2
def baseEnd_2034250 : Nat := 232121782535282493604369

theorem tailTrace_2034250 : CollatzResearch.WordTrace tailWord_2034250 prefixEnd_2034250 232121782535282493604369 := by
  unfold tailWord_2034250
  simp only [CollatzResearch.WordTrace]
  refine ⟨18548798220066786771353051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49463461920178098056941469 18548798220066786771353051)
  ·
    refine ⟨27823197330100180157029577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18548798220066786771353051 27823197330100180157029577)
    ·
      refine ⟨20867397997575135117772183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27823197330100180157029577 20867397997575135117772183)
      ·
        refine ⟨31301096996362702676658275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20867397997575135117772183 31301096996362702676658275)
        ·
          refine ⟨46951645494544054014987413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31301096996362702676658275 46951645494544054014987413)
          ·
            refine ⟨2200858382556752531952535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46951645494544054014987413 2200858382556752531952535)
            ·
              refine ⟨3301287573835128797928803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200858382556752531952535 3301287573835128797928803)
              ·
                refine ⟨4951931360752693196893205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3301287573835128797928803 4951931360752693196893205)
                ·
                  refine ⟨232121782535282493604369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4951931360752693196893205 232121782535282493604369)
                  ·
                    rfl

theorem cell22_2034250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_2034250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034250 prefixEnd_2034250 := by exact prefixLift 2034250
  have htrace : WordTrace (prefixWord ++ tailWord_2034250) baseStart_2034250 baseEnd_2034250 := by
    simpa [prefixWord, tailWord_2034250, baseEnd_2034250] using wordTrace_append hprefix tailTrace_2034250
  have hstable : (prefixWord ++ tailWord_2034250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034250).length < 2 ^ (prefixWord ++ tailWord_2034250).sum := by decide
  have hdescent : baseEnd_2034250 < baseStart_2034250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034263 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 4, 4]
def baseStart_2034263 : Nat := 118140960795 + 2034263 * 2 ^ 59
def prefixEnd_2034263 : Nat := 4983230072969 + 3 ^ 40 * 2034263 * 2
def baseEnd_2034263 : Nat := 696369797771519780238067

theorem tailTrace_2034263 : CollatzResearch.WordTrace tailWord_2034263 prefixEnd_2034263 696369797771519780238067 := by
  unfold tailWord_2034263
  simp only [CollatzResearch.WordTrace]
  refine ⟨74195667029220050305635443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49463778019480033537090295 74195667029220050305635443)
  ·
    refine ⟨111293500543830075458453165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74195667029220050305635443 111293500543830075458453165)
    ·
      refine ⟨41735062703936278296919937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111293500543830075458453165 41735062703936278296919937)
      ·
        refine ⟨31301297027952208722689953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41735062703936278296919937 31301297027952208722689953)
        ·
          refine ⟨23475972770964156542017465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31301297027952208722689953 23475972770964156542017465)
          ·
            refine ⟨17606979578223117406513099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23475972770964156542017465 17606979578223117406513099)
            ·
              refine ⟨26410469367334676109769649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17606979578223117406513099 26410469367334676109769649)
              ·
                refine ⟨19807852025501007082327237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26410469367334676109769649 19807852025501007082327237)
                ·
                  refine ⟨3713972254781438827936357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19807852025501007082327237 3713972254781438827936357)
                  ·
                    refine ⟨696369797771519780238067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3713972254781438827936357 696369797771519780238067)
                    ·
                      rfl

theorem cell22_2034263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_2034263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034263 prefixEnd_2034263 := by exact prefixLift 2034263
  have htrace : WordTrace (prefixWord ++ tailWord_2034263) baseStart_2034263 baseEnd_2034263 := by
    simpa [prefixWord, tailWord_2034263, baseEnd_2034263] using wordTrace_append hprefix tailTrace_2034263
  have hstable : (prefixWord ++ tailWord_2034263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034263).length < 2 ^ (prefixWord ++ tailWord_2034263).sum := by decide
  have hdescent : baseEnd_2034263 < baseStart_2034263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034301 : List Nat := [1, 4, 1, 1, 6, 1, 2, 2, 4]
def baseStart_2034301 : Nat := 118140960795 + 2034301 * 2 ^ 59
def prefixEnd_2034301 : Nat := 4983230072969 + 3 ^ 40 * 2034301 * 2
def baseEnd_2034301 : Nat := 232127601982700115929317

theorem tailTrace_2034301 : CollatzResearch.WordTrace tailWord_2034301 prefixEnd_2034301 232127601982700115929317 := by
  unfold tailWord_2034301
  simp only [CollatzResearch.WordTrace]
  refine ⟨74197053003082382795518757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49464702002054921863679171 74197053003082382795518757)
  ·
    refine ⟨13911947438077946774159767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74197053003082382795518757 13911947438077946774159767)
    ·
      refine ⟨20867921157116920161239651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13911947438077946774159767 20867921157116920161239651)
      ·
        refine ⟨31301881735675380241859477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20867921157116920161239651 31301881735675380241859477)
        ·
          refine ⟨1467275706359783448837163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31301881735675380241859477 1467275706359783448837163)
          ·
            refine ⟨2200913559539675173255745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1467275706359783448837163 2200913559539675173255745)
            ·
              refine ⟨1650685169654756379941809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2200913559539675173255745 1650685169654756379941809)
              ·
                refine ⟨1238013877241067284956357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1650685169654756379941809 1238013877241067284956357)
                ·
                  refine ⟨232127601982700115929317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1238013877241067284956357 232127601982700115929317)
                  ·
                    rfl

theorem cell22_2034301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_2034301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034301 prefixEnd_2034301 := by exact prefixLift 2034301
  have htrace : WordTrace (prefixWord ++ tailWord_2034301) baseStart_2034301 baseEnd_2034301 := by
    simpa [prefixWord, tailWord_2034301, baseEnd_2034301] using wordTrace_append hprefix tailTrace_2034301
  have hstable : (prefixWord ++ tailWord_2034301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034301).length < 2 ^ (prefixWord ++ tailWord_2034301).sum := by decide
  have hdescent : baseEnd_2034301 < baseStart_2034301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034357 : List Nat := [1, 3, 3, 3, 1, 1, 3, 2, 5]
def baseStart_2034357 : Nat := 118140960795 + 2034357 * 2 ^ 59
def prefixEnd_2034357 : Nat := 4983230072969 + 3 ^ 40 * 2034357 * 2
def baseEnd_2034357 : Nat := 232133991964178289462593

theorem tailTrace_2034357 : CollatzResearch.WordTrace tailWord_2034357 prefixEnd_2034357 232133991964178289462593 := by
  unfold tailWord_2034357
  simp only [CollatzResearch.WordTrace]
  refine ⟨74199095490879504359557325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49466063660586336239704883 74199095490879504359557325)
  ·
    refine ⟨27824660809079814134833997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74199095490879504359557325 27824660809079814134833997)
    ·
      refine ⟨10434247803404930300562749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27824660809079814134833997 10434247803404930300562749)
      ·
        refine ⟨3912842926276848862711031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10434247803404930300562749 3912842926276848862711031)
        ·
          refine ⟨5869264389415273294066547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3912842926276848862711031 5869264389415273294066547)
          ·
            refine ⟨8803896584122909941099821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5869264389415273294066547 8803896584122909941099821)
            ·
              refine ⟨3301461219046091227912433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8803896584122909941099821 3301461219046091227912433)
              ·
                refine ⟨2476095914284568420934325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3301461219046091227912433 2476095914284568420934325)
                ·
                  refine ⟨232133991964178289462593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2476095914284568420934325 232133991964178289462593)
                  ·
                    rfl

theorem cell22_2034357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_2034357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034357 prefixEnd_2034357 := by exact prefixLift 2034357
  have htrace : WordTrace (prefixWord ++ tailWord_2034357) baseStart_2034357 baseEnd_2034357 := by
    simpa [prefixWord, tailWord_2034357, baseEnd_2034357] using wordTrace_append hprefix tailTrace_2034357
  have hstable : (prefixWord ++ tailWord_2034357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034357).length < 2 ^ (prefixWord ++ tailWord_2034357).sum := by decide
  have hdescent : baseEnd_2034357 < baseStart_2034357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034415 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 4, 4]
def baseStart_2034415 : Nat := 118140960795 + 2034415 * 2 ^ 59
def prefixEnd_2034415 : Nat := 4983230072969 + 3 ^ 40 * 2034415 * 2
def baseEnd_2034415 : Nat := 696421830477842050437601

theorem tailTrace_2034415 : CollatzResearch.WordTrace tailWord_2034415 prefixEnd_2034415 696421830477842050437601 := by
  unfold tailWord_2034415
  simp only [CollatzResearch.WordTrace]
  refine ⟨74201210924669380265168699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49467473949779586843445799 74201210924669380265168699)
  ·
    refine ⟨111301816387004070397753049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74201210924669380265168699 111301816387004070397753049)
    ·
      refine ⟨83476362290253052798314787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111301816387004070397753049 83476362290253052798314787)
      ·
        refine ⟨125214543435379579197472181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83476362290253052798314787 125214543435379579197472181)
        ·
          refine ⟨11738863447066835549763017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125214543435379579197472181 11738863447066835549763017)
          ·
            refine ⟨8804147585300126662322263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11738863447066835549763017 8804147585300126662322263)
            ·
              refine ⟨13206221377950189993483395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8804147585300126662322263 13206221377950189993483395)
              ·
                refine ⟨19809332066925284990225093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13206221377950189993483395 19809332066925284990225093)
                ·
                  refine ⟨3714249762548490935667205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19809332066925284990225093 3714249762548490935667205)
                  ·
                    refine ⟨696421830477842050437601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3714249762548490935667205 696421830477842050437601)
                    ·
                      rfl

theorem cell22_2034415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_2034415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034415 prefixEnd_2034415 := by exact prefixLift 2034415
  have htrace : WordTrace (prefixWord ++ tailWord_2034415) baseStart_2034415 baseEnd_2034415 := by
    simpa [prefixWord, tailWord_2034415, baseEnd_2034415] using wordTrace_append hprefix tailTrace_2034415
  have hstable : (prefixWord ++ tailWord_2034415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034415).length < 2 ^ (prefixWord ++ tailWord_2034415).sum := by decide
  have hdescent : baseEnd_2034415 < baseStart_2034415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034417 : List Nat := [1, 2, 2, 2, 2, 2, 2, 4, 2, 3]
def baseStart_2034417 : Nat := 118140960795 + 2034417 * 2 ^ 59
def prefixEnd_2034417 : Nat := 4983230072969 + 3 ^ 40 * 2034417 * 2
def baseEnd_2034417 : Nat := 696422515118714711887595

theorem tailTrace_2034417 : CollatzResearch.WordTrace tailWord_2034417 prefixEnd_2034417 696422515118714711887595 := by
  unfold tailWord_2034417
  simp only [CollatzResearch.WordTrace]
  refine ⟨74201283870662134606741505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49467522580441423071161003 74201283870662134606741505)
  ·
    refine ⟨55650962902996600955056129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74201283870662134606741505 55650962902996600955056129)
    ·
      refine ⟨41738222177247450716292097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55650962902996600955056129 41738222177247450716292097)
      ·
        refine ⟨31303666632935588037219073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41738222177247450716292097 31303666632935588037219073)
        ·
          refine ⟨23477749974701691027914305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31303666632935588037219073 23477749974701691027914305)
          ·
            refine ⟨17608312481026268270935729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23477749974701691027914305 17608312481026268270935729)
            ·
              refine ⟨13206234360769701203201797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17608312481026268270935729 13206234360769701203201797)
              ·
                refine ⟨2476168942644318975600337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13206234360769701203201797 2476168942644318975600337)
                ·
                  refine ⟨1857126706983239231700253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2476168942644318975600337 1857126706983239231700253)
                  ·
                    refine ⟨696422515118714711887595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1857126706983239231700253 696422515118714711887595)
                    ·
                      rfl

theorem cell22_2034417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_2034417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034417 prefixEnd_2034417 := by exact prefixLift 2034417
  have htrace : WordTrace (prefixWord ++ tailWord_2034417) baseStart_2034417 baseEnd_2034417 := by
    simpa [prefixWord, tailWord_2034417, baseEnd_2034417] using wordTrace_append hprefix tailTrace_2034417
  have hstable : (prefixWord ++ tailWord_2034417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034417).length < 2 ^ (prefixWord ++ tailWord_2034417).sum := by decide
  have hdescent : baseEnd_2034417 < baseStart_2034417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034475 : List Nat := [1, 1, 1, 1, 2, 1, 2, 8, 5]
def baseStart_2034475 : Nat := 118140960795 + 2034475 * 2 ^ 59
def prefixEnd_2034475 : Nat := 4983230072969 + 3 ^ 40 * 2034475 * 2
def baseEnd_2034475 : Nat := 232147456568007297979139

theorem tailTrace_2034475 : CollatzResearch.WordTrace tailWord_2034475 prefixEnd_2034475 232147456568007297979139 := by
  unfold tailWord_2034475
  simp only [CollatzResearch.WordTrace]
  refine ⟨74203399304452010512352879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49468932869634673674901919 74203399304452010512352879)
  ·
    refine ⟨111305098956678015768529319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74203399304452010512352879 111305098956678015768529319)
    ·
      refine ⟨166957648435017023652793979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111305098956678015768529319 166957648435017023652793979)
      ·
        refine ⟨250436472652525535479190969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166957648435017023652793979 250436472652525535479190969)
        ·
          refine ⟨187827354489394151609393227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250436472652525535479190969 187827354489394151609393227)
          ·
            refine ⟨281741031734091227414089841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187827354489394151609393227 281741031734091227414089841)
            ·
              refine ⟨211305773800568420560567381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281741031734091227414089841 211305773800568420560567381)
              ·
                refine ⟨2476239536725411178444149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 211305773800568420560567381 2476239536725411178444149)
                ·
                  refine ⟨232147456568007297979139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2476239536725411178444149 232147456568007297979139)
                  ·
                    rfl

theorem cell22_2034475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 5].length) (baseStart_2034475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034475 prefixEnd_2034475 := by exact prefixLift 2034475
  have htrace : WordTrace (prefixWord ++ tailWord_2034475) baseStart_2034475 baseEnd_2034475 := by
    simpa [prefixWord, tailWord_2034475, baseEnd_2034475] using wordTrace_append hprefix tailTrace_2034475
  have hstable : (prefixWord ++ tailWord_2034475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034475).length < 2 ^ (prefixWord ++ tailWord_2034475).sum := by decide
  have hdescent : baseEnd_2034475 < baseStart_2034475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034567 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 1, 6]
def baseStart_2034567 : Nat := 118140960795 + 2034567 * 2 ^ 59
def prefixEnd_2034567 : Nat := 4983230072969 + 3 ^ 40 * 2034567 * 2
def baseEnd_2034567 : Nat := 696473863184164320637135

theorem tailTrace_2034567 : CollatzResearch.WordTrace tailWord_2034567 prefixEnd_2034567 696473863184164320637135 := by
  unfold tailWord_2034567
  simp only [CollatzResearch.WordTrace]
  refine ⟨74206754820118710224701955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49471169880079140149801303 74206754820118710224701955)
  ·
    refine ⟨111310132230178065337052933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74206754820118710224701955 111310132230178065337052933)
    ·
      refine ⟨20870649793158387250697425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111310132230178065337052933 20870649793158387250697425)
      ·
        refine ⟨15652987344868790438023069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20870649793158387250697425 15652987344868790438023069)
        ·
          refine ⟨5869870254325796414258651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15652987344868790438023069 5869870254325796414258651)
          ·
            refine ⟨8804805381488694621387977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5869870254325796414258651 8804805381488694621387977)
            ·
              refine ⟨6603604036116520966040983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8804805381488694621387977 6603604036116520966040983)
              ·
                refine ⟨9905406054174781449061475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6603604036116520966040983 9905406054174781449061475)
                ·
                  refine ⟨14858109081262172173592213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9905406054174781449061475 14858109081262172173592213)
                  ·
                    refine ⟨696473863184164320637135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14858109081262172173592213 696473863184164320637135)
                    ·
                      rfl

theorem cell22_2034567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_2034567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034567 prefixEnd_2034567 := by exact prefixLift 2034567
  have htrace : WordTrace (prefixWord ++ tailWord_2034567) baseStart_2034567 baseEnd_2034567 := by
    simpa [prefixWord, tailWord_2034567, baseEnd_2034567] using wordTrace_append hprefix tailTrace_2034567
  have hstable : (prefixWord ++ tailWord_2034567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034567).length < 2 ^ (prefixWord ++ tailWord_2034567).sum := by decide
  have hdescent : baseEnd_2034567 < baseStart_2034567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034588 : List Nat := [2, 2, 3, 3, 2, 1, 3, 2, 4]
def baseStart_2034588 : Nat := 118140960795 + 2034588 * 2 ^ 59
def prefixEnd_2034588 : Nat := 4983230072969 + 3 ^ 40 * 2034588 * 2
def baseEnd_2034588 : Nat := 232160350637775755287357

theorem tailTrace_2034588 : CollatzResearch.WordTrace tailWord_2034588 prefixEnd_2034588 232160350637775755287357 := by
  unfold tailWord_2034588
  simp only [CollatzResearch.WordTrace]
  refine ⟨37103760376521315405608209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49471680502028420540810945 37103760376521315405608209)
  ·
    refine ⟨27827820282390986554206157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37103760376521315405608209 27827820282390986554206157)
    ·
      refine ⟨10435432605896619957827309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27827820282390986554206157 10435432605896619957827309)
      ·
        refine ⟨3913287227211232484185241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10435432605896619957827309 3913287227211232484185241)
        ·
          refine ⟨2934965420408424363138931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3913287227211232484185241 2934965420408424363138931)
          ·
            refine ⟨4402448130612636544708397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2934965420408424363138931 4402448130612636544708397)
            ·
              refine ⟨1650918048979738704265649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4402448130612636544708397 1650918048979738704265649)
              ·
                refine ⟨1238188536734804028199237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1650918048979738704265649 1238188536734804028199237)
                ·
                  refine ⟨232160350637775755287357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1238188536734804028199237 232160350637775755287357)
                  ·
                    rfl

theorem cell22_2034588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_2034588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034588 prefixEnd_2034588 := by exact prefixLift 2034588
  have htrace : WordTrace (prefixWord ++ tailWord_2034588) baseStart_2034588 baseEnd_2034588 := by
    simpa [prefixWord, tailWord_2034588, baseEnd_2034588] using wordTrace_append hprefix tailTrace_2034588
  have hstable : (prefixWord ++ tailWord_2034588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034588).length < 2 ^ (prefixWord ++ tailWord_2034588).sum := by decide
  have hdescent : baseEnd_2034588 < baseStart_2034588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034599 : List Nat := [1, 1, 6, 1, 3, 1, 2, 7]
def baseStart_2034599 : Nat := 118140960795 + 2034599 * 2 ^ 59
def prefixEnd_2034599 : Nat := 4983230072969 + 3 ^ 40 * 2034599 * 2
def baseEnd_2034599 : Nat := 77387201937569655981893

theorem tailTrace_2034599 : CollatzResearch.WordTrace tailWord_2034599 prefixEnd_2034599 77387201937569655981893 := by
  unfold tailWord_2034599
  simp only [CollatzResearch.WordTrace]
  refine ⟨74207921956002779689866851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49471947970668519793244567 74207921956002779689866851)
  ·
    refine ⟨111311882934004169534800277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74207921956002779689866851 111311882934004169534800277)
    ·
      refine ⟨5217744512531445446943763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111311882934004169534800277 5217744512531445446943763)
      ·
        refine ⟨7826616768797168170415645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5217744512531445446943763 7826616768797168170415645)
        ·
          refine ⟨2934981288298938063905867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7826616768797168170415645 2934981288298938063905867)
          ·
            refine ⟨4402471932448407095858801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2934981288298938063905867 4402471932448407095858801)
            ·
              refine ⟨3301853949336305321894101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4402471932448407095858801 3301853949336305321894101)
              ·
                refine ⟨77387201937569655981893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3301853949336305321894101 77387201937569655981893)
                ·
                  rfl

theorem cell22_2034599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 7].length) (baseStart_2034599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034599 prefixEnd_2034599 := by exact prefixLift 2034599
  have htrace : WordTrace (prefixWord ++ tailWord_2034599) baseStart_2034599 baseEnd_2034599 := by
    simpa [prefixWord, tailWord_2034599, baseEnd_2034599] using wordTrace_append hprefix tailTrace_2034599
  have hstable : (prefixWord ++ tailWord_2034599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034599).length < 2 ^ (prefixWord ++ tailWord_2034599).sum := by decide
  have hdescent : baseEnd_2034599 < baseStart_2034599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034637 : List Nat := [1, 6, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_2034637 : Nat := 118140960795 + 2034637 * 2 ^ 59
def prefixEnd_2034637 : Nat := 4983230072969 + 3 ^ 40 * 2034637 * 2
def baseEnd_2034637 : Nat := 696497825614707471386921

theorem tailTrace_2034637 : CollatzResearch.WordTrace tailWord_2034637 prefixEnd_2034637 696497825614707471386921 := by
  unfold tailWord_2034637
  simp only [CollatzResearch.WordTrace]
  refine ⟨74209307929865112179750165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49472871953243408119833443 74209307929865112179750165)
  ·
    refine ⟨3478561309212427133425789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74209307929865112179750165 3478561309212427133425789)
    ·
      refine ⟨1304460490954660175034671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3478561309212427133425789 1304460490954660175034671)
      ·
        refine ⟨1956690736431990262552007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1304460490954660175034671 1956690736431990262552007)
        ·
          refine ⟨2935036104647985393828011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1956690736431990262552007 2935036104647985393828011)
          ·
            refine ⟨4402554156971978090742017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2935036104647985393828011 4402554156971978090742017)
            ·
              refine ⟨3301915617728983568056513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4402554156971978090742017 3301915617728983568056513)
              ·
                refine ⟨2476436713296737676042385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3301915617728983568056513 2476436713296737676042385)
                ·
                  refine ⟨1857327534972553257031789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2476436713296737676042385 1857327534972553257031789)
                  ·
                    refine ⟨696497825614707471386921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1857327534972553257031789 696497825614707471386921)
                    ·
                      rfl

theorem cell22_2034637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_2034637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034637 prefixEnd_2034637 := by exact prefixLift 2034637
  have htrace : WordTrace (prefixWord ++ tailWord_2034637) baseStart_2034637 baseEnd_2034637 := by
    simpa [prefixWord, tailWord_2034637, baseEnd_2034637] using wordTrace_append hprefix tailTrace_2034637
  have hstable : (prefixWord ++ tailWord_2034637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034637).length < 2 ^ (prefixWord ++ tailWord_2034637).sum := by decide
  have hdescent : baseEnd_2034637 < baseStart_2034637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034644 : List Nat := [2, 4, 1, 2, 1, 2, 1, 4, 5]
def baseStart_2034644 : Nat := 118140960795 + 2034644 * 2 ^ 59
def prefixEnd_2034644 : Nat := 4983230072969 + 3 ^ 40 * 2034644 * 2
def baseEnd_2034644 : Nat := 232166740619253928820633

theorem tailTrace_2034644 : CollatzResearch.WordTrace tailWord_2034644 prefixEnd_2034644 232166740619253928820633 := by
  unfold tailWord_2034644
  simp only [CollatzResearch.WordTrace]
  refine ⟨37104781620419876187627493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49473042160559834916836657 37104781620419876187627493)
  ·
    refine ⟨6957146553828726785180155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37104781620419876187627493 6957146553828726785180155)
    ·
      refine ⟨10435719830743090177770233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6957146553828726785180155 10435719830743090177770233)
      ·
        refine ⟨7826789873057317633327675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10435719830743090177770233 7826789873057317633327675)
        ·
          refine ⟨11740184809585976449991513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7826789873057317633327675 11740184809585976449991513)
          ·
            refine ⟨8805138607189482337493635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11740184809585976449991513 8805138607189482337493635)
            ·
              refine ⟨13207707910784223506240453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8805138607189482337493635 13207707910784223506240453)
              ·
                refine ⟨2476445233272041907420085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13207707910784223506240453 2476445233272041907420085)
                ·
                  refine ⟨232166740619253928820633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2476445233272041907420085 232166740619253928820633)
                  ·
                    rfl

theorem cell22_2034644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_2034644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034644 prefixEnd_2034644 := by exact prefixLift 2034644
  have htrace : WordTrace (prefixWord ++ tailWord_2034644) baseStart_2034644 baseEnd_2034644 := by
    simpa [prefixWord, tailWord_2034644, baseEnd_2034644] using wordTrace_append hprefix tailTrace_2034644
  have hstable : (prefixWord ++ tailWord_2034644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034644).length < 2 ^ (prefixWord ++ tailWord_2034644).sum := by decide
  have hdescent : baseEnd_2034644 < baseStart_2034644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034648 : List Nat := [2, 1, 2, 2, 2, 3, 4, 2, 1, 3]
def baseStart_2034648 : Nat := 118140960795 + 2034648 * 2 ^ 59
def prefixEnd_2034648 : Nat := 4983230072969 + 3 ^ 40 * 2034648 * 2
def baseEnd_2034648 : Nat := 696501591139507109361887

theorem tailTrace_2034648 : CollatzResearch.WordTrace tailWord_2034648 prefixEnd_2034648 696501591139507109361887 := by
  unfold tailWord_2034648
  simp only [CollatzResearch.WordTrace]
  refine ⟨37104854566412630529200299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49473139421883507372267065 37104854566412630529200299)
  ·
    refine ⟨55657281849618945793800449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37104854566412630529200299 55657281849618945793800449)
    ·
      refine ⟨41742961387214209345350337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55657281849618945793800449 41742961387214209345350337)
      ·
        refine ⟨31307221040410657009012753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41742961387214209345350337 31307221040410657009012753)
        ·
          refine ⟨23480415780307992756759565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31307221040410657009012753 23480415780307992756759565)
          ·
            refine ⟨8805155917615497283784837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23480415780307992756759565 8805155917615497283784837)
            ·
              refine ⟨1650966734552905740709657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8805155917615497283784837 1650966734552905740709657)
              ·
                refine ⟨1238225050914679305532243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1650966734552905740709657 1238225050914679305532243)
                ·
                  refine ⟨1857337576372018958298365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1238225050914679305532243 1857337576372018958298365)
                  ·
                    refine ⟨696501591139507109361887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1857337576372018958298365 696501591139507109361887)
                    ·
                      rfl

theorem cell22_2034648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 1, 3].length) (baseStart_2034648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034648 prefixEnd_2034648 := by exact prefixLift 2034648
  have htrace : WordTrace (prefixWord ++ tailWord_2034648) baseStart_2034648 baseEnd_2034648 := by
    simpa [prefixWord, tailWord_2034648, baseEnd_2034648] using wordTrace_append hprefix tailTrace_2034648
  have hstable : (prefixWord ++ tailWord_2034648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034648).length < 2 ^ (prefixWord ++ tailWord_2034648).sum := by decide
  have hdescent : baseEnd_2034648 < baseStart_2034648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034721 : List Nat := [1, 2, 3, 2, 3, 3, 1, 1, 1, 5]
def baseStart_2034721 : Nat := 118140960795 + 2034721 * 2 ^ 59
def prefixEnd_2034721 : Nat := 4983230072969 + 3 ^ 40 * 2034721 * 2
def baseEnd_2034721 : Nat := 696526580531359252286663

theorem tailTrace_2034721 : CollatzResearch.WordTrace tailWord_2034721 prefixEnd_2034721 696526580531359252286663 := by
  unfold tailWord_2034721
  simp only [CollatzResearch.WordTrace]
  refine ⟨74212371661560794525808017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49474914441040529683872011 74212371661560794525808017)
  ·
    refine ⟨55659278746170595894356013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74212371661560794525808017 55659278746170595894356013)
    ·
      refine ⟨20872229529813973460383505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55659278746170595894356013 20872229529813973460383505)
      ·
        refine ⟨15654172147360480095287629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20872229529813973460383505 15654172147360480095287629)
        ·
          refine ⟨5870314555260180035732861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15654172147360480095287629 5870314555260180035732861)
          ·
            refine ⟨2201367958222567513399823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5870314555260180035732861 2201367958222567513399823)
            ·
              refine ⟨3302051937333851270099735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2201367958222567513399823 3302051937333851270099735)
              ·
                refine ⟨4953077906000776905149603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3302051937333851270099735 4953077906000776905149603)
                ·
                  refine ⟨7429616859001165357724405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4953077906000776905149603 7429616859001165357724405)
                  ·
                    refine ⟨696526580531359252286663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7429616859001165357724405 696526580531359252286663)
                    ·
                      rfl

theorem cell22_2034721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_2034721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034721 prefixEnd_2034721 := by exact prefixLift 2034721
  have htrace : WordTrace (prefixWord ++ tailWord_2034721) baseStart_2034721 baseEnd_2034721 := by
    simpa [prefixWord, tailWord_2034721, baseEnd_2034721] using wordTrace_append hprefix tailTrace_2034721
  have hstable : (prefixWord ++ tailWord_2034721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034721).length < 2 ^ (prefixWord ++ tailWord_2034721).sum := by decide
  have hdescent : baseEnd_2034721 < baseStart_2034721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034732 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 2, 7]
def baseStart_2034732 : Nat := 118140960795 + 2034732 * 2 ^ 59
def prefixEnd_2034732 : Nat := 4983230072969 + 3 ^ 40 * 2034732 * 2
def baseEnd_2034732 : Nat := 696530346056158890261629

theorem tailTrace_2034732 : CollatzResearch.WordTrace tailWord_2034732 prefixEnd_2034732 696530346056158890261629 := by
  unfold tailWord_2034732
  simp only [CollatzResearch.WordTrace]
  refine ⟨37106386432260471702229225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49475181909680628936305633 37106386432260471702229225)
  ·
    refine ⟨27829789824195353776671919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37106386432260471702229225 27829789824195353776671919)
    ·
      refine ⟨41744684736293030665007879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27829789824195353776671919 41744684736293030665007879)
      ·
        refine ⟨62617027104439545997511819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41744684736293030665007879 62617027104439545997511819)
        ·
          refine ⟨93925540656659318996267729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62617027104439545997511819 93925540656659318996267729)
          ·
            refine ⟨70444155492494489247200797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93925540656659318996267729 70444155492494489247200797)
            ·
              refine ⟨26416558309685433467700299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70444155492494489247200797 26416558309685433467700299)
              ·
                refine ⟨39624837464528150201550449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26416558309685433467700299 39624837464528150201550449)
                ·
                  refine ⟨29718628098396112651162837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39624837464528150201550449 29718628098396112651162837)
                  ·
                    refine ⟨696530346056158890261629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29718628098396112651162837 696530346056158890261629)
                    ·
                      rfl

theorem cell22_2034732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_2034732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034732 prefixEnd_2034732 := by exact prefixLift 2034732
  have htrace : WordTrace (prefixWord ++ tailWord_2034732) baseStart_2034732 baseEnd_2034732 := by
    simpa [prefixWord, tailWord_2034732, baseEnd_2034732] using wordTrace_append hprefix tailTrace_2034732
  have hstable : (prefixWord ++ tailWord_2034732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034732).length < 2 ^ (prefixWord ++ tailWord_2034732).sum := by decide
  have hdescent : baseEnd_2034732 < baseStart_2034732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034734 : List Nat := [4, 1, 3, 1, 1, 1, 3, 8]
def baseStart_2034734 : Nat := 118140960795 + 2034734 * 2 ^ 59
def prefixEnd_2034734 : Nat := 4983230072969 + 3 ^ 40 * 2034734 * 2
def baseEnd_2034734 : Nat := 77392336744114616856847

theorem tailTrace_2034734 : CollatzResearch.WordTrace tailWord_2034734 prefixEnd_2034734 77392336744114616856847 := by
  unfold tailWord_2034734
  simp only [CollatzResearch.WordTrace]
  refine ⟨9276605726314212218253907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49475230540342465164020837 9276605726314212218253907)
  ·
    refine ⟨13914908589471318327380861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9276605726314212218253907 13914908589471318327380861)
    ·
      refine ⟨5218090721051744372767823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13914908589471318327380861 5218090721051744372767823)
      ·
        refine ⟨7827136081577616559151735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5218090721051744372767823 7827136081577616559151735)
        ·
          refine ⟨11740704122366424838727603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7827136081577616559151735 11740704122366424838727603)
          ·
            refine ⟨17611056183549637258091405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11740704122366424838727603 17611056183549637258091405)
            ·
              refine ⟨6604146068831113971784277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17611056183549637258091405 6604146068831113971784277)
              ·
                refine ⟨77392336744114616856847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6604146068831113971784277 77392336744114616856847)
                ·
                  rfl

theorem cell22_2034734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_2034734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034734 prefixEnd_2034734 := by exact prefixLift 2034734
  have htrace : WordTrace (prefixWord ++ tailWord_2034734) baseStart_2034734 baseEnd_2034734 := by
    simpa [prefixWord, tailWord_2034734, baseEnd_2034734] using wordTrace_append hprefix tailTrace_2034734
  have hstable : (prefixWord ++ tailWord_2034734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034734).length < 2 ^ (prefixWord ++ tailWord_2034734).sum := by decide
  have hdescent : baseEnd_2034734 < baseStart_2034734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034740 : List Nat := [2, 5, 1, 2, 1, 3, 1, 3, 4]
def baseStart_2034740 : Nat := 118140960795 + 2034740 * 2 ^ 59
def prefixEnd_2034740 : Nat := 4983230072969 + 3 ^ 40 * 2034740 * 2
def baseEnd_2034740 : Nat := 232177694873216512020535

theorem tailTrace_2034740 : CollatzResearch.WordTrace tailWord_2034740 prefixEnd_2034740 232177694873216512020535 := by
  unfold tailWord_2034740
  simp only [CollatzResearch.WordTrace]
  refine ⟨37106532324245980385374837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49475376432327973847166449 37106532324245980385374837)
  ·
    refine ⟨3478737405398060661128891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37106532324245980385374837 3478737405398060661128891)
    ·
      refine ⟨5218106108097090991693337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3478737405398060661128891 5218106108097090991693337)
      ·
        refine ⟨3913579581072818243770003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5218106108097090991693337 3913579581072818243770003)
        ·
          refine ⟨5870369371609227365655005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3913579581072818243770003 5870369371609227365655005)
          ·
            refine ⟨2201388514353460262120627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5870369371609227365655005 2201388514353460262120627)
            ·
              refine ⟨3302082771530190393180941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2201388514353460262120627 3302082771530190393180941)
              ·
                refine ⟨1238281039323821397442853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3302082771530190393180941 1238281039323821397442853)
                ·
                  refine ⟨232177694873216512020535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1238281039323821397442853 232177694873216512020535)
                  ·
                    rfl

theorem cell22_2034740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_2034740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034740 prefixEnd_2034740 := by exact prefixLift 2034740
  have htrace : WordTrace (prefixWord ++ tailWord_2034740) baseStart_2034740 baseEnd_2034740 := by
    simpa [prefixWord, tailWord_2034740, baseEnd_2034740] using wordTrace_append hprefix tailTrace_2034740
  have hstable : (prefixWord ++ tailWord_2034740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034740).length < 2 ^ (prefixWord ++ tailWord_2034740).sum := by decide
  have hdescent : baseEnd_2034740 < baseStart_2034740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034817 : List Nat := [1, 2, 4, 2, 2, 3, 2, 2, 1, 3]
def baseStart_2034817 : Nat := 118140960795 + 2034817 * 2 ^ 59
def prefixEnd_2034817 : Nat := 4983230072969 + 3 ^ 40 * 2034817 * 2
def baseEnd_2034817 : Nat := 696559443293247001886369

theorem tailTrace_2034817 : CollatzResearch.WordTrace tailWord_2034817 prefixEnd_2034817 696559443293247001886369 := by
  unfold tailWord_2034817
  simp only [CollatzResearch.WordTrace]
  refine ⟨74215873069213002921302705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49477248712808668614201803 74215873069213002921302705)
  ·
    refine ⟨55661904801909752190977029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74215873069213002921302705 55661904801909752190977029)
    ·
      refine ⟨10436607150358078535808193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55661904801909752190977029 10436607150358078535808193)
      ·
        refine ⟨7827455362768558901856145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10436607150358078535808193 7827455362768558901856145)
        ·
          refine ⟨5870591522076419176392109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7827455362768558901856145 5870591522076419176392109)
          ·
            refine ⟨2201471820778657191147041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5870591522076419176392109 2201471820778657191147041)
            ·
              refine ⟨1651103865583992893360281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2201471820778657191147041 1651103865583992893360281)
              ·
                refine ⟨1238327899187994670020211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1651103865583992893360281 1238327899187994670020211)
                ·
                  refine ⟨1857491848781992005030317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1238327899187994670020211 1857491848781992005030317)
                  ·
                    refine ⟨696559443293247001886369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1857491848781992005030317 696559443293247001886369)
                    ·
                      rfl

theorem cell22_2034817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_2034817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034817 prefixEnd_2034817 := by exact prefixLift 2034817
  have htrace : WordTrace (prefixWord ++ tailWord_2034817) baseStart_2034817 baseEnd_2034817 := by
    simpa [prefixWord, tailWord_2034817, baseEnd_2034817] using wordTrace_append hprefix tailTrace_2034817
  have hstable : (prefixWord ++ tailWord_2034817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034817).length < 2 ^ (prefixWord ++ tailWord_2034817).sum := by decide
  have hdescent : baseEnd_2034817 < baseStart_2034817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034873 : List Nat := [1, 2, 1, 4, 1, 3, 3, 2, 2, 3]
def baseStart_2034873 : Nat := 118140960795 + 2034873 * 2 ^ 59
def prefixEnd_2034873 : Nat := 4983230072969 + 3 ^ 40 * 2034873 * 2
def baseEnd_2034873 : Nat := 696578613237681522486197

theorem tailTrace_2034873 : CollatzResearch.WordTrace tailWord_2034873 prefixEnd_2034873 696578613237681522486197 := by
  unfold tailWord_2034873
  simp only [CollatzResearch.WordTrace]
  refine ⟨74217915557010124485341273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49478610371340082990227515 74217915557010124485341273)
  ·
    refine ⟨55663436667757593364005955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74217915557010124485341273 55663436667757593364005955)
    ·
      refine ⟨83495155001636390046008933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55663436667757593364005955 83495155001636390046008933)
      ·
        refine ⟨15655341562806823133626675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83495155001636390046008933 15655341562806823133626675)
        ·
          refine ⟨23483012344210234700440013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15655341562806823133626675 23483012344210234700440013)
          ·
            refine ⟨8806129629078838012665005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23483012344210234700440013 8806129629078838012665005)
            ·
              refine ⟨3302298610904564254749377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8806129629078838012665005 3302298610904564254749377)
              ·
                refine ⟨2476723958178423191062033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3302298610904564254749377 2476723958178423191062033)
                ·
                  refine ⟨1857542968633817393296525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2476723958178423191062033 1857542968633817393296525)
                  ·
                    refine ⟨696578613237681522486197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1857542968633817393296525 696578613237681522486197)
                    ·
                      rfl

theorem cell22_2034873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 3].length) (baseStart_2034873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034873 prefixEnd_2034873 := by exact prefixLift 2034873
  have htrace : WordTrace (prefixWord ++ tailWord_2034873) baseStart_2034873 baseEnd_2034873 := by
    simpa [prefixWord, tailWord_2034873, baseEnd_2034873] using wordTrace_append hprefix tailTrace_2034873
  have hstable : (prefixWord ++ tailWord_2034873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034873).length < 2 ^ (prefixWord ++ tailWord_2034873).sum := by decide
  have hdescent : baseEnd_2034873 < baseStart_2034873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034890 : List Nat := [3, 1, 2, 1, 3, 3, 3, 1, 2, 3]
def baseStart_2034890 : Nat := 118140960795 + 2034890 * 2 ^ 59
def prefixEnd_2034890 : Nat := 4983230072969 + 3 ^ 40 * 2034890 * 2
def baseEnd_2034890 : Nat := 696584432685099144811145

theorem tailTrace_2034890 : CollatzResearch.WordTrace tailWord_2034890 prefixEnd_2034890 696584432685099144811145 := by
  unfold tailWord_2034890
  simp only [CollatzResearch.WordTrace]
  refine ⟨18554633899487134097177531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49479023731965690925806749 18554633899487134097177531)
  ·
    refine ⟨27831950849230701145766297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18554633899487134097177531 27831950849230701145766297)
    ·
      refine ⟨20873963136923025859324723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27831950849230701145766297 20873963136923025859324723)
      ·
        refine ⟨31310944705384538788987085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20873963136923025859324723 31310944705384538788987085)
        ·
          refine ⟨11741604264519202045870157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31310944705384538788987085 11741604264519202045870157)
          ·
            refine ⟨4403101599194700767201309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11741604264519202045870157 4403101599194700767201309)
            ·
              refine ⟨1651163099698012787700491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4403101599194700767201309 1651163099698012787700491)
              ·
                refine ⟨2476744649547019181550737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1651163099698012787700491 2476744649547019181550737)
                ·
                  refine ⟨1857558487160264386163053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2476744649547019181550737 1857558487160264386163053)
                  ·
                    refine ⟨696584432685099144811145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1857558487160264386163053 696584432685099144811145)
                    ·
                      rfl

theorem cell22_2034890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_2034890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034890 prefixEnd_2034890 := by exact prefixLift 2034890
  have htrace : WordTrace (prefixWord ++ tailWord_2034890) baseStart_2034890 baseEnd_2034890 := by
    simpa [prefixWord, tailWord_2034890, baseEnd_2034890] using wordTrace_append hprefix tailTrace_2034890
  have hstable : (prefixWord ++ tailWord_2034890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034890).length < 2 ^ (prefixWord ++ tailWord_2034890).sum := by decide
  have hdescent : baseEnd_2034890 < baseStart_2034890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034944 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 2, 8]
def baseStart_2034944 : Nat := 118140960795 + 2034944 * 2 ^ 59
def prefixEnd_2034944 : Nat := 4983230072969 + 3 ^ 40 * 2034944 * 2
def baseEnd_2034944 : Nat := 696602917988661003960979

theorem tailTrace_2034944 : CollatzResearch.WordTrace tailWord_2034944 prefixEnd_2034944 696602917988661003960979 := by
  unfold tailWord_2034944
  simp only [CollatzResearch.WordTrace]
  refine ⟨37110252569876451805587943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49480336759835269074117257 37110252569876451805587943)
  ·
    refine ⟨55665378854814677708381915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37110252569876451805587943 55665378854814677708381915)
    ·
      refine ⟨83498068282222016562572873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55665378854814677708381915 83498068282222016562572873)
      ·
        refine ⟨62623551211666512421929655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83498068282222016562572873 62623551211666512421929655)
        ·
          refine ⟨93935326817499768632894483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62623551211666512421929655 93935326817499768632894483)
          ·
            refine ⟨140902990226249652949341725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93935326817499768632894483 140902990226249652949341725)
            ·
              refine ⟨52838621334843619856003147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140902990226249652949341725 52838621334843619856003147)
              ·
                refine ⟨79257932002265429784004721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52838621334843619856003147 79257932002265429784004721)
                ·
                  refine ⟨59443449001699072338003541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79257932002265429784004721 59443449001699072338003541)
                  ·
                    refine ⟨696602917988661003960979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59443449001699072338003541 696602917988661003960979)
                    ·
                      rfl

theorem cell22_2034944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_2034944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034944 prefixEnd_2034944 := by exact prefixLift 2034944
  have htrace : WordTrace (prefixWord ++ tailWord_2034944) baseStart_2034944 baseEnd_2034944 := by
    simpa [prefixWord, tailWord_2034944, baseEnd_2034944] using wordTrace_append hprefix tailTrace_2034944
  have hstable : (prefixWord ++ tailWord_2034944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034944).length < 2 ^ (prefixWord ++ tailWord_2034944).sum := by decide
  have hdescent : baseEnd_2034944 < baseStart_2034944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034948 : List Nat := [2, 3, 2, 2, 2, 2, 1, 3, 5]
def baseStart_2034948 : Nat := 118140960795 + 2034948 * 2 ^ 59
def prefixEnd_2034948 : Nat := 4983230072969 + 3 ^ 40 * 2034948 * 2
def baseEnd_2034948 : Nat := 232201429090135442286989

theorem tailTrace_2034948 : CollatzResearch.WordTrace tailWord_2034948 prefixEnd_2034948 232201429090135442286989 := by
  unfold tailWord_2034948
  simp only [CollatzResearch.WordTrace]
  refine ⟨37110325515869206147160749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49480434021158941529547665 37110325515869206147160749)
  ·
    refine ⟨13916372068450952305185281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37110325515869206147160749 13916372068450952305185281)
    ·
      refine ⟨10437279051338214228888961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13916372068450952305185281 10437279051338214228888961)
      ·
        refine ⟨7827959288503660671666721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10437279051338214228888961 7827959288503660671666721)
        ·
          refine ⟨5870969466377745503750041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7827959288503660671666721 5870969466377745503750041)
          ·
            refine ⟨4403227099783309127812531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5870969466377745503750041 4403227099783309127812531)
            ·
              refine ⟨6604840649674963691718797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4403227099783309127812531 6604840649674963691718797)
              ·
                refine ⟨2476815243628111384394549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6604840649674963691718797 2476815243628111384394549)
                ·
                  refine ⟨232201429090135442286989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2476815243628111384394549 232201429090135442286989)
                  ·
                    rfl

theorem cell22_2034948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_2034948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034948 prefixEnd_2034948 := by exact prefixLift 2034948
  have htrace : WordTrace (prefixWord ++ tailWord_2034948) baseStart_2034948 baseEnd_2034948 := by
    simpa [prefixWord, tailWord_2034948, baseEnd_2034948] using wordTrace_append hprefix tailTrace_2034948
  have hstable : (prefixWord ++ tailWord_2034948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034948).length < 2 ^ (prefixWord ++ tailWord_2034948).sum := by decide
  have hdescent : baseEnd_2034948 < baseStart_2034948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034961 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 3, 4]
def baseStart_2034961 : Nat := 118140960795 + 2034961 * 2 ^ 59
def prefixEnd_2034961 : Nat := 4983230072969 + 3 ^ 40 * 2034961 * 2
def baseEnd_2034961 : Nat := 696608737436078626285927

theorem tailTrace_2034961 : CollatzResearch.WordTrace tailWord_2034961 prefixEnd_2034961 696608737436078626285927 := by
  unfold tailWord_2034961
  simp only [CollatzResearch.WordTrace]
  refine ⟨74221125180691315514544737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49480750120460877009696491 74221125180691315514544737)
  ·
    refine ⟨55665843885518486635908553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74221125180691315514544737 55665843885518486635908553)
    ·
      refine ⟨41749382914138864976931415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55665843885518486635908553 41749382914138864976931415)
      ·
        refine ⟨62624074371208297465397123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41749382914138864976931415 62624074371208297465397123)
        ·
          refine ⟨93936111556812446198095685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62624074371208297465397123 93936111556812446198095685)
          ·
            refine ⟨17613020916902333662142941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93936111556812446198095685 17613020916902333662142941)
            ·
              refine ⟨6604882843838375123303603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17613020916902333662142941 6604882843838375123303603)
              ·
                refine ⟨9907324265757562684955405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6604882843838375123303603 9907324265757562684955405)
                ·
                  refine ⟨3715246599659086006858277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9907324265757562684955405 3715246599659086006858277)
                  ·
                    refine ⟨696608737436078626285927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3715246599659086006858277 696608737436078626285927)
                    ·
                      rfl

theorem cell22_2034961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_2034961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2034961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2034961 prefixEnd_2034961 := by exact prefixLift 2034961
  have htrace : WordTrace (prefixWord ++ tailWord_2034961) baseStart_2034961 baseEnd_2034961 := by
    simpa [prefixWord, tailWord_2034961, baseEnd_2034961] using wordTrace_append hprefix tailTrace_2034961
  have hstable : (prefixWord ++ tailWord_2034961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034961).length < 2 ^ (prefixWord ++ tailWord_2034961).sum := by decide
  have hdescent : baseEnd_2034961 < baseStart_2034961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035008 : List Nat := [2, 1, 1, 2, 2, 1, 3, 5, 2, 3]
def baseStart_2035008 : Nat := 118140960795 + 2035008 * 2 ^ 59
def prefixEnd_2035008 : Nat := 4983230072969 + 3 ^ 40 * 2035008 * 2
def baseEnd_2035008 : Nat := 696624826496586170360783

theorem tailTrace_2035008 : CollatzResearch.WordTrace tailWord_2035008 prefixEnd_2035008 696624826496586170360783 := by
  unfold tailWord_2035008
  simp only [CollatzResearch.WordTrace]
  refine ⟨37111419705760521270752839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49481892941014028361003785 37111419705760521270752839)
  ·
    refine ⟨55667129558640781906129259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37111419705760521270752839 55667129558640781906129259)
    ·
      refine ⟨83500694337961172859193889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55667129558640781906129259 83500694337961172859193889)
      ·
        refine ⟨62625520753470879644395417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83500694337961172859193889 62625520753470879644395417)
        ·
          refine ⟨46969140565103159733296563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62625520753470879644395417 46969140565103159733296563)
          ·
            refine ⟨70453710847654739599944845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46969140565103159733296563 70453710847654739599944845)
            ·
              refine ⟨26420141567870527349979317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70453710847654739599944845 26420141567870527349979317)
              ·
                refine ⟨2476888271987861939060561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26420141567870527349979317 2476888271987861939060561)
                ·
                  refine ⟨1857666203990896454295421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2476888271987861939060561 1857666203990896454295421)
                  ·
                    refine ⟨696624826496586170360783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1857666203990896454295421 696624826496586170360783)
                    ·
                      rfl

theorem cell22_2035008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 2, 3].length) (baseStart_2035008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035008 prefixEnd_2035008 := by exact prefixLift 2035008
  have htrace : WordTrace (prefixWord ++ tailWord_2035008) baseStart_2035008 baseEnd_2035008 := by
    simpa [prefixWord, tailWord_2035008, baseEnd_2035008] using wordTrace_append hprefix tailTrace_2035008
  have hstable : (prefixWord ++ tailWord_2035008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035008).length < 2 ^ (prefixWord ++ tailWord_2035008).sum := by decide
  have hdescent : baseEnd_2035008 < baseStart_2035008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035117 : List Nat := [1, 5, 2, 2, 1, 1, 4, 1, 5]
def baseStart_2035117 : Nat := 118140960795 + 2035117 * 2 ^ 59
def prefixEnd_2035117 : Nat := 4983230072969 + 3 ^ 40 * 2035117 * 2
def baseEnd_2035117 : Nat := 232220713141382073128483

theorem tailTrace_2035117 : CollatzResearch.WordTrace tailWord_2035117 prefixEnd_2035117 232220713141382073128483 := by
  unfold tailWord_2035117
  simp only [CollatzResearch.WordTrace]
  refine ⟨74226814968126154157223605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49484543312084102771482403 74226814968126154157223605)
  ·
    refine ⟨6958763903261826952239713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74226814968126154157223605 6958763903261826952239713)
    ·
      refine ⟨5219072927446370214179785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6958763903261826952239713 5219072927446370214179785)
      ·
        refine ⟨3914304695584777660634839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5219072927446370214179785 3914304695584777660634839)
        ·
          refine ⟨5871457043377166490952259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3914304695584777660634839 5871457043377166490952259)
          ·
            refine ⟨8807185565065749736428389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5871457043377166490952259 8807185565065749736428389)
            ·
              refine ⟨1651347293449828075580323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8807185565065749736428389 1651347293449828075580323)
              ·
                refine ⟨2477020940174742113370485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1651347293449828075580323 2477020940174742113370485)
                ·
                  refine ⟨232220713141382073128483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2477020940174742113370485 232220713141382073128483)
                  ·
                    rfl

theorem cell22_2035117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_2035117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035117 prefixEnd_2035117 := by exact prefixLift 2035117
  have htrace : WordTrace (prefixWord ++ tailWord_2035117) baseStart_2035117 baseEnd_2035117 := by
    simpa [prefixWord, tailWord_2035117, baseEnd_2035117] using wordTrace_append hprefix tailTrace_2035117
  have hstable : (prefixWord ++ tailWord_2035117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035117).length < 2 ^ (prefixWord ++ tailWord_2035117).sum := by decide
  have hdescent : baseEnd_2035117 < baseStart_2035117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035143 : List Nat := [1, 1, 4, 1, 1, 3, 3, 2, 1, 5]
def baseStart_2035143 : Nat := 118140960795 + 2035143 * 2 ^ 59
def prefixEnd_2035143 : Nat := 4983230072969 + 3 ^ 40 * 2035143 * 2
def baseEnd_2035143 : Nat := 696671039755490818235369

theorem tailTrace_2035143 : CollatzResearch.WordTrace tailWord_2035143 prefixEnd_2035143 696671039755490818235369 := by
  unfold tailWord_2035143
  simp only [CollatzResearch.WordTrace]
  refine ⟨74227763266031960597670083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49485175510687973731780055 74227763266031960597670083)
  ·
    refine ⟨111341644899047940896505125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74227763266031960597670083 111341644899047940896505125)
    ·
      refine ⟨20876558418571488918094711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111341644899047940896505125 20876558418571488918094711)
      ·
        refine ⟨31314837627857233377142067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20876558418571488918094711 31314837627857233377142067)
        ·
          refine ⟨46972256441785850065713101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31314837627857233377142067 46972256441785850065713101)
          ·
            refine ⟨17614596165669693774642413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46972256441785850065713101 17614596165669693774642413)
            ·
              refine ⟨6605473562126135165490905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17614596165669693774642413 6605473562126135165490905)
              ·
                refine ⟨4954105171594601374118179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6605473562126135165490905 4954105171594601374118179)
                ·
                  refine ⟨7431157757391902061177269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4954105171594601374118179 7431157757391902061177269)
                  ·
                    refine ⟨696671039755490818235369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7431157757391902061177269 696671039755490818235369)
                    ·
                      rfl

theorem cell22_2035143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_2035143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035143 prefixEnd_2035143 := by exact prefixLift 2035143
  have htrace : WordTrace (prefixWord ++ tailWord_2035143) baseStart_2035143 baseEnd_2035143 := by
    simpa [prefixWord, tailWord_2035143, baseEnd_2035143] using wordTrace_append hprefix tailTrace_2035143
  have hstable : (prefixWord ++ tailWord_2035143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035143).length < 2 ^ (prefixWord ++ tailWord_2035143).sum := by decide
  have hdescent : baseEnd_2035143 < baseStart_2035143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035160 : List Nat := [2, 1, 2, 2, 2, 1, 3, 4, 2, 3]
def baseStart_2035160 : Nat := 118140960795 + 2035160 * 2 ^ 59
def prefixEnd_2035160 : Nat := 4983230072969 + 3 ^ 40 * 2035160 * 2
def baseEnd_2035160 : Nat := 696676859202908440560317

theorem tailTrace_2035160 : CollatzResearch.WordTrace tailWord_2035160 prefixEnd_2035160 696676859202908440560317 := by
  unfold tailWord_2035160
  simp only [CollatzResearch.WordTrace]
  refine ⟨37114191653485186250519467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49485588871313581667359289 37114191653485186250519467)
  ·
    refine ⟨55671287480227779375779201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37114191653485186250519467 55671287480227779375779201)
    ·
      refine ⟨41753465610170834531834401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55671287480227779375779201 41753465610170834531834401)
      ·
        refine ⟨31315099207628125898875801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41753465610170834531834401 31315099207628125898875801)
        ·
          refine ⟨23486324405721094424156851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31315099207628125898875801 23486324405721094424156851)
          ·
            refine ⟨35229486608581641636235277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23486324405721094424156851 35229486608581641636235277)
            ·
              refine ⟨13211057478218115613588229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35229486608581641636235277 13211057478218115613588229)
              ·
                refine ⟨2477073277165896677547793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13211057478218115613588229 2477073277165896677547793)
                ·
                  refine ⟨1857804957874422508160845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2477073277165896677547793 1857804957874422508160845)
                  ·
                    refine ⟨696676859202908440560317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1857804957874422508160845 696676859202908440560317)
                    ·
                      rfl

theorem cell22_2035160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_2035160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035160 prefixEnd_2035160 := by exact prefixLift 2035160
  have htrace : WordTrace (prefixWord ++ tailWord_2035160) baseStart_2035160 baseEnd_2035160 := by
    simpa [prefixWord, tailWord_2035160, baseEnd_2035160] using wordTrace_append hprefix tailTrace_2035160
  have hstable : (prefixWord ++ tailWord_2035160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035160).length < 2 ^ (prefixWord ++ tailWord_2035160).sum := by decide
  have hdescent : baseEnd_2035160 < baseStart_2035160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035162 : List Nat := [3, 1, 1, 2, 3, 2, 4, 2, 4]
def baseStart_2035162 : Nat := 118140960795 + 2035162 * 2 ^ 59
def prefixEnd_2035162 : Nat := 4983230072969 + 3 ^ 40 * 2035162 * 2
def baseEnd_2035162 : Nat := 232225847947927034003437

theorem tailTrace_2035162 : CollatzResearch.WordTrace tailWord_2035162 prefixEnd_2035162 232225847947927034003437 := by
  unfold tailWord_2035162
  simp only [CollatzResearch.WordTrace]
  refine ⟨18557114063240781710652935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49485637501975417895074493 18557114063240781710652935)
  ·
    refine ⟨27835671094861172565979403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18557114063240781710652935 27835671094861172565979403)
    ·
      refine ⟨41753506642291758848969105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27835671094861172565979403 41753506642291758848969105)
      ·
        refine ⟨31315129981718819136726829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41753506642291758848969105 31315129981718819136726829)
        ·
          refine ⟨11743173743144557176272561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31315129981718819136726829 11743173743144557176272561)
          ·
            refine ⟨8807380307358417882204421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11743173743144557176272561 8807380307358417882204421)
            ·
              refine ⟨1651383807629703352913329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8807380307358417882204421 1651383807629703352913329)
              ·
                refine ⟨1238537855722277514684997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1651383807629703352913329 1238537855722277514684997)
                ·
                  refine ⟨232225847947927034003437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1238537855722277514684997 232225847947927034003437)
                  ·
                    rfl

theorem cell22_2035162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_2035162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035162 prefixEnd_2035162 := by exact prefixLift 2035162
  have htrace : WordTrace (prefixWord ++ tailWord_2035162) baseStart_2035162 baseEnd_2035162 := by
    simpa [prefixWord, tailWord_2035162, baseEnd_2035162] using wordTrace_append hprefix tailTrace_2035162
  have hstable : (prefixWord ++ tailWord_2035162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035162).length < 2 ^ (prefixWord ++ tailWord_2035162).sum := by decide
  have hdescent : baseEnd_2035162 < baseStart_2035162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035198 : List Nat := [4, 2, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_2035198 : Nat := 118140960795 + 2035198 * 2 ^ 59
def prefixEnd_2035198 : Nat := 4983230072969 + 3 ^ 40 * 2035198 * 2
def baseEnd_2035198 : Nat := 696689867379489008110201

theorem tailTrace_2035198 : CollatzResearch.WordTrace tailWord_2035198 prefixEnd_2035198 696689867379489008110201 := by
  unfold tailWord_2035198
  simp only [CollatzResearch.WordTrace]
  refine ⟨9278721160104088123865281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49486512853888469993948165 9278721160104088123865281)
  ·
    refine ⟨6959040870078066092898961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9278721160104088123865281 6959040870078066092898961)
    ·
      refine ⟨5219280652558549569674221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6959040870078066092898961 5219280652558549569674221)
      ·
        refine ⟨1957230244709456088627833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5219280652558549569674221 1957230244709456088627833)
        ·
          refine ⟨1467922683532092066470875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1957230244709456088627833 1467922683532092066470875)
          ·
            refine ⟨2201884025298138099706313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1467922683532092066470875 2201884025298138099706313)
            ·
              refine ⟨1651413018973603574779735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2201884025298138099706313 1651413018973603574779735)
              ·
                refine ⟨2477119528460405362169603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1651413018973603574779735 2477119528460405362169603)
                ·
                  refine ⟨3715679292690608043254405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2477119528460405362169603 3715679292690608043254405)
                  ·
                    refine ⟨696689867379489008110201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3715679292690608043254405 696689867379489008110201)
                    ·
                      rfl

theorem cell22_2035198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_2035198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035198 prefixEnd_2035198 := by exact prefixLift 2035198
  have htrace : WordTrace (prefixWord ++ tailWord_2035198) baseStart_2035198 baseEnd_2035198 := by
    simpa [prefixWord, tailWord_2035198, baseEnd_2035198] using wordTrace_append hprefix tailTrace_2035198
  have hstable : (prefixWord ++ tailWord_2035198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035198).length < 2 ^ (prefixWord ++ tailWord_2035198).sum := by decide
  have hdescent : baseEnd_2035198 < baseStart_2035198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035286 : List Nat := [5, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_2035286 : Nat := 118140960795 + 2035286 * 2 ^ 59
def prefixEnd_2035286 : Nat := 4983230072969 + 3 ^ 40 * 2035286 * 2
def baseEnd_2035286 : Nat := 232239997192628703969977

theorem tailTrace_2035286 : CollatzResearch.WordTrace tailWord_2035286 prefixEnd_2035286 232239997192628703969977 := by
  unfold tailWord_2035286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4639561181532118501257857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49488652603009264013417141 4639561181532118501257857)
  ·
    refine ⟨3479670886149088875943393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4639561181532118501257857 3479670886149088875943393)
    ·
      refine ⟨2609753164611816656957545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3479670886149088875943393 2609753164611816656957545)
      ·
        refine ⟨1957314873458862492718159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2609753164611816656957545 1957314873458862492718159)
        ·
          refine ⟨2935972310188293739077239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1957314873458862492718159 2935972310188293739077239)
          ·
            refine ⟨4403958465282440608615859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2935972310188293739077239 4403958465282440608615859)
            ·
              refine ⟨6605937697923660912923789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4403958465282440608615859 6605937697923660912923789)
              ·
                refine ⟨2477226636721372842346421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6605937697923660912923789 2477226636721372842346421)
                ·
                  refine ⟨232239997192628703969977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2477226636721372842346421 232239997192628703969977)
                  ·
                    rfl

theorem cell22_2035286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_2035286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035286 prefixEnd_2035286 := by exact prefixLift 2035286
  have htrace : WordTrace (prefixWord ++ tailWord_2035286) baseStart_2035286 baseEnd_2035286 := by
    simpa [prefixWord, tailWord_2035286, baseEnd_2035286] using wordTrace_append hprefix tailTrace_2035286
  have hstable : (prefixWord ++ tailWord_2035286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035286).length < 2 ^ (prefixWord ++ tailWord_2035286).sum := by decide
  have hdescent : baseEnd_2035286 < baseStart_2035286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035329 : List Nat := [1, 2, 4, 2, 1, 3, 2, 2, 2, 3]
def baseStart_2035329 : Nat := 118140960795 + 2035329 * 2 ^ 59
def prefixEnd_2035329 : Nat := 4983230072969 + 3 ^ 40 * 2035329 * 2
def baseEnd_2035329 : Nat := 696734711356648333084799

theorem tailTrace_2035329 : CollatzResearch.WordTrace tailWord_2035329 prefixEnd_2035329 696734711356648333084799 := by
  unfold tailWord_2035329
  simp only [CollatzResearch.WordTrace]
  refine ⟨74234547243358114363941041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49489698162238742909294027 74234547243358114363941041)
  ·
    refine ⟨55675910432518585772955781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74234547243358114363941041 55675910432518585772955781)
    ·
      refine ⟨10439233206097234832429209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55675910432518585772955781 10439233206097234832429209)
      ·
        refine ⟨7829424904572926124321907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10439233206097234832429209 7829424904572926124321907)
        ·
          refine ⟨11744137356859389186482861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7829424904572926124321907 11744137356859389186482861)
          ·
            refine ⟨4404051508822270944931073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11744137356859389186482861 4404051508822270944931073)
            ·
              refine ⟨3303038631616703208698305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4404051508822270944931073 3303038631616703208698305)
              ·
                refine ⟨2477278973712527406523729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3303038631616703208698305 2477278973712527406523729)
                ·
                  refine ⟨1857959230284395554892797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2477278973712527406523729 1857959230284395554892797)
                  ·
                    refine ⟨696734711356648333084799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1857959230284395554892797 696734711356648333084799)
                    ·
                      rfl

theorem cell22_2035329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_2035329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035329 prefixEnd_2035329 := by exact prefixLift 2035329
  have htrace : WordTrace (prefixWord ++ tailWord_2035329) baseStart_2035329 baseEnd_2035329 := by
    simpa [prefixWord, tailWord_2035329, baseEnd_2035329] using wordTrace_append hprefix tailTrace_2035329
  have hstable : (prefixWord ++ tailWord_2035329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035329).length < 2 ^ (prefixWord ++ tailWord_2035329).sum := by decide
  have hdescent : baseEnd_2035329 < baseStart_2035329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035342 : List Nat := [4, 1, 1, 3, 1, 4, 1, 7]
def baseStart_2035342 : Nat := 118140960795 + 2035342 * 2 ^ 59
def prefixEnd_2035342 : Nat := 4983230072969 + 3 ^ 40 * 2035342 * 2
def baseEnd_2035342 : Nat := 77415462391368959167751

theorem tailTrace_2035342 : CollatzResearch.WordTrace tailWord_2035342 prefixEnd_2035342 77415462391368959167751 := by
  unfold tailWord_2035342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9279377674038877198020535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49490014261540678389442853 9279377674038877198020535)
  ·
    refine ⟨13919066511058315797030803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9279377674038877198020535 13919066511058315797030803)
    ·
      refine ⟨20878599766587473695546205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13919066511058315797030803 20878599766587473695546205)
      ·
        refine ⟨7829474912470302635829827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20878599766587473695546205 7829474912470302635829827)
        ·
          refine ⟨11744212368705453953744741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7829474912470302635829827 11744212368705453953744741)
          ·
            refine ⟨2202039819132272616327139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11744212368705453953744741 2202039819132272616327139)
            ·
              refine ⟨3303059728698408924490709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2202039819132272616327139 3303059728698408924490709)
              ·
                refine ⟨77415462391368959167751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3303059728698408924490709 77415462391368959167751)
                ·
                  rfl

theorem cell22_2035342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_2035342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035342 prefixEnd_2035342 := by exact prefixLift 2035342
  have htrace : WordTrace (prefixWord ++ tailWord_2035342) baseStart_2035342 baseEnd_2035342 := by
    simpa [prefixWord, tailWord_2035342, baseEnd_2035342] using wordTrace_append hprefix tailTrace_2035342
  have hstable : (prefixWord ++ tailWord_2035342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035342).length < 2 ^ (prefixWord ++ tailWord_2035342).sum := by decide
  have hdescent : baseEnd_2035342 < baseStart_2035342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035359 : List Nat := [1, 1, 2, 7, 1, 1, 3, 6]
def baseStart_2035359 : Nat := 118140960795 + 2035359 * 2 ^ 59
def prefixEnd_2035359 : Nat := 4983230072969 + 3 ^ 40 * 2035359 * 2
def baseEnd_2035359 : Nat := 77416108996637583870523

theorem tailTrace_2035359 : CollatzResearch.WordTrace tailWord_2035359 prefixEnd_2035359 77416108996637583870523 := by
  unfold tailWord_2035359
  simp only [CollatzResearch.WordTrace]
  refine ⟨74235641433249429487533131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49490427622166286325022087 74235641433249429487533131)
  ·
    refine ⟨111353462149874144231299697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74235641433249429487533131 111353462149874144231299697)
    ·
      refine ⟨83515096612405608173474773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111353462149874144231299697 83515096612405608173474773)
      ·
        refine ⟨1957385076853256441565815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 83515096612405608173474773 1957385076853256441565815)
        ·
          refine ⟨2936077615279884662348723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1957385076853256441565815 2936077615279884662348723)
          ·
            refine ⟨4404116422919826993523085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936077615279884662348723 4404116422919826993523085)
            ·
              refine ⟨1651543658594935122571157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4404116422919826993523085 1651543658594935122571157)
              ·
                refine ⟨77416108996637583870523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1651543658594935122571157 77416108996637583870523)
                ·
                  rfl

theorem cell22_2035359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 6].length) (baseStart_2035359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035359 prefixEnd_2035359 := by exact prefixLift 2035359
  have htrace : WordTrace (prefixWord ++ tailWord_2035359) baseStart_2035359 baseEnd_2035359 := by
    simpa [prefixWord, tailWord_2035359, baseEnd_2035359] using wordTrace_append hprefix tailTrace_2035359
  have hstable : (prefixWord ++ tailWord_2035359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035359).length < 2 ^ (prefixWord ++ tailWord_2035359).sum := by decide
  have hdescent : baseEnd_2035359 < baseStart_2035359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035385 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 2, 5]
def baseStart_2035385 : Nat := 118140960795 + 2035385 * 2 ^ 59
def prefixEnd_2035385 : Nat := 4983230072969 + 3 ^ 40 * 2035385 * 2
def baseEnd_2035385 : Nat := 696753881301082853684627

theorem tailTrace_2035385 : CollatzResearch.WordTrace tailWord_2035385 prefixEnd_2035385 696753881301082853684627 := by
  unfold tailWord_2035385
  simp only [CollatzResearch.WordTrace]
  refine ⟨74236589731155235927979609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49491059820770157285319739 74236589731155235927979609)
  ·
    refine ⟨55677442298366426945984707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74236589731155235927979609 55677442298366426945984707)
    ·
      refine ⟨83516163447549640418977061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55677442298366426945984707 83516163447549640418977061)
      ·
        refine ⟨15659280646415557578558199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83516163447549640418977061 15659280646415557578558199)
        ·
          refine ⟨23488920969623336367837299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15659280646415557578558199 23488920969623336367837299)
          ·
            refine ⟨35233381454435004551755949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23488920969623336367837299 35233381454435004551755949)
            ·
              refine ⟨13212518045413126706908481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35233381454435004551755949 13212518045413126706908481)
              ·
                refine ⟨9909388534059845030181361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13212518045413126706908481 9909388534059845030181361)
                ·
                  refine ⟨7432041400544883772636021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9909388534059845030181361 7432041400544883772636021)
                  ·
                    refine ⟨696753881301082853684627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7432041400544883772636021 696753881301082853684627)
                    ·
                      rfl

theorem cell22_2035385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_2035385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035385 prefixEnd_2035385 := by exact prefixLift 2035385
  have htrace : WordTrace (prefixWord ++ tailWord_2035385) baseStart_2035385 baseEnd_2035385 := by
    simpa [prefixWord, tailWord_2035385, baseEnd_2035385] using wordTrace_append hprefix tailTrace_2035385
  have hstable : (prefixWord ++ tailWord_2035385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035385).length < 2 ^ (prefixWord ++ tailWord_2035385).sum := by decide
  have hdescent : baseEnd_2035385 < baseStart_2035385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035415 : List Nat := [1, 1, 3, 2, 1, 3, 1, 4, 6]
def baseStart_2035415 : Nat := 118140960795 + 2035415 * 2 ^ 59
def prefixEnd_2035415 : Nat := 4983230072969 + 3 ^ 40 * 2035415 * 2
def baseEnd_2035415 : Nat := 232254716971390925144845

theorem tailTrace_2035415 : CollatzResearch.WordTrace tailWord_2035415 prefixEnd_2035415 232254716971390925144845 := by
  unfold tailWord_2035415
  simp only [CollatzResearch.WordTrace]
  refine ⟨74237683921046551051571699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49491789280697700701047799 74237683921046551051571699)
  ·
    refine ⟨111356525881569826577357549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74237683921046551051571699 111356525881569826577357549)
    ·
      refine ⟨41758697205588684966509081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111356525881569826577357549 41758697205588684966509081)
      ·
        refine ⟨31319022904191513724881811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41758697205588684966509081 31319022904191513724881811)
        ·
          refine ⟨46978534356287270587322717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31319022904191513724881811 46978534356287270587322717)
          ·
            refine ⟨17616950383607726470246019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46978534356287270587322717 17616950383607726470246019)
            ·
              refine ⟨26425425575411589705369029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17616950383607726470246019 26425425575411589705369029)
              ·
                refine ⟨4954767295389673069756693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26425425575411589705369029 4954767295389673069756693)
                ·
                  refine ⟨232254716971390925144845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4954767295389673069756693 232254716971390925144845)
                  ·
                    rfl

theorem cell22_2035415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 6].length) (baseStart_2035415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035415 prefixEnd_2035415 := by exact prefixLift 2035415
  have htrace : WordTrace (prefixWord ++ tailWord_2035415) baseStart_2035415 baseEnd_2035415 := by
    simpa [prefixWord, tailWord_2035415, baseEnd_2035415] using wordTrace_append hprefix tailTrace_2035415
  have hstable : (prefixWord ++ tailWord_2035415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035415).length < 2 ^ (prefixWord ++ tailWord_2035415).sum := by decide
  have hdescent : baseEnd_2035415 < baseStart_2035415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035417 : List Nat := [1, 2, 1, 2, 3, 3, 1, 4, 1, 4]
def baseStart_2035417 : Nat := 118140960795 + 2035417 * 2 ^ 59
def prefixEnd_2035417 : Nat := 4983230072969 + 3 ^ 40 * 2035417 * 2
def baseEnd_2035417 : Nat := 696764835555045436884529

theorem tailTrace_2035417 : CollatzResearch.WordTrace tailWord_2035417 prefixEnd_2035417 696764835555045436884529 := by
  unfold tailWord_2035417
  simp only [CollatzResearch.WordTrace]
  refine ⟨74237756867039305393144505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49491837911359536928763003 74237756867039305393144505)
  ·
    refine ⟨55678317650279479044858379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74237756867039305393144505 55678317650279479044858379)
    ·
      refine ⟨83517476475419218567287569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55678317650279479044858379 83517476475419218567287569)
      ·
        refine ⟨62638107356564413925465677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83517476475419218567287569 62638107356564413925465677)
        ·
          refine ⟨23489290258711655222049629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62638107356564413925465677 23489290258711655222049629)
          ·
            refine ⟨8808483847016870708268611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23489290258711655222049629 8808483847016870708268611)
            ·
              refine ⟨13212725770525306062402917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8808483847016870708268611 13212725770525306062402917)
              ·
                refine ⟨2477386081973494886700547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13212725770525306062402917 2477386081973494886700547)
                ·
                  refine ⟨3716079122960242330050821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2477386081973494886700547 3716079122960242330050821)
                  ·
                    refine ⟨696764835555045436884529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3716079122960242330050821 696764835555045436884529)
                    ·
                      rfl

theorem cell22_2035417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 4].length) (baseStart_2035417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035417 prefixEnd_2035417 := by exact prefixLift 2035417
  have htrace : WordTrace (prefixWord ++ tailWord_2035417) baseStart_2035417 baseEnd_2035417 := by
    simpa [prefixWord, tailWord_2035417, baseEnd_2035417] using wordTrace_append hprefix tailTrace_2035417
  have hstable : (prefixWord ++ tailWord_2035417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035417).length < 2 ^ (prefixWord ++ tailWord_2035417).sum := by decide
  have hdescent : baseEnd_2035417 < baseStart_2035417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035447 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 4, 3]
def baseStart_2035447 : Nat := 118140960795 + 2035447 * 2 ^ 59
def prefixEnd_2035447 : Nat := 4983230072969 + 3 ^ 40 * 2035447 * 2
def baseEnd_2035447 : Nat := 696775105168135358634437

theorem tailTrace_2035447 : CollatzResearch.WordTrace tailWord_2035447 prefixEnd_2035447 696775105168135358634437 := by
  unfold tailWord_2035447
  simp only [CollatzResearch.WordTrace]
  refine ⟨74238851056930620516736595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49492567371287080344491063 74238851056930620516736595)
  ·
    refine ⟨111358276585395930775104893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74238851056930620516736595 111358276585395930775104893)
    ·
      refine ⟨41759353719523474040664335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111358276585395930775104893 41759353719523474040664335)
      ·
        refine ⟨62639030579285211060996503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41759353719523474040664335 62639030579285211060996503)
        ·
          refine ⟨93958545868927816591494755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62639030579285211060996503 93958545868927816591494755)
          ·
            refine ⟨140937818803391724887242133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93958545868927816591494755 140937818803391724887242133)
            ·
              refine ⟨6606460256408987104089475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 140937818803391724887242133 6606460256408987104089475)
              ·
                refine ⟨9909690384613480656134213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6606460256408987104089475 9909690384613480656134213)
                ·
                  refine ⟨1858066947115027623025165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9909690384613480656134213 1858066947115027623025165)
                  ·
                    refine ⟨696775105168135358634437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1858066947115027623025165 696775105168135358634437)
                    ·
                      rfl

theorem cell22_2035447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_2035447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035447 prefixEnd_2035447 := by exact prefixLift 2035447
  have htrace : WordTrace (prefixWord ++ tailWord_2035447) baseStart_2035447 baseEnd_2035447 := by
    simpa [prefixWord, tailWord_2035447, baseEnd_2035447] using wordTrace_append hprefix tailTrace_2035447
  have hstable : (prefixWord ++ tailWord_2035447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035447).length < 2 ^ (prefixWord ++ tailWord_2035447).sum := by decide
  have hdescent : baseEnd_2035447 < baseStart_2035447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035464 : List Nat := [2, 1, 3, 2, 2, 1, 3, 3, 2, 3]
def baseStart_2035464 : Nat := 118140960795 + 2035464 * 2 ^ 59
def prefixEnd_2035464 : Nat := 4983230072969 + 3 ^ 40 * 2035464 * 2
def baseEnd_2035464 : Nat := 696780924615552980959385

theorem tailTrace_2035464 : CollatzResearch.WordTrace tailWord_2035464 prefixEnd_2035464 696780924615552980959385 := by
  unfold tailWord_2035464
  simp only [CollatzResearch.WordTrace]
  refine ⟨37119735548934516210052723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49492980731912688280070297 37119735548934516210052723)
  ·
    refine ⟨55679603323401774315079085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37119735548934516210052723 55679603323401774315079085)
    ·
      refine ⟨20879851246275665368154657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55679603323401774315079085 20879851246275665368154657)
      ·
        refine ⟨15659888434706749026115993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20879851246275665368154657 15659888434706749026115993)
        ·
          refine ⟨11744916326030061769586995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15659888434706749026115993 11744916326030061769586995)
          ·
            refine ⟨17617374489045092654380493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11744916326030061769586995 17617374489045092654380493)
            ·
              refine ⟨6606515433391909745392685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17617374489045092654380493 6606515433391909745392685)
              ·
                refine ⟨2477443287521966154522257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6606515433391909745392685 2477443287521966154522257)
                ·
                  refine ⟨1858082465641474615891693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2477443287521966154522257 1858082465641474615891693)
                  ·
                    refine ⟨696780924615552980959385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1858082465641474615891693 696780924615552980959385)
                    ·
                      rfl

theorem cell22_2035464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_2035464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035464 prefixEnd_2035464 := by exact prefixLift 2035464
  have htrace : WordTrace (prefixWord ++ tailWord_2035464) baseStart_2035464 baseEnd_2035464 := by
    simpa [prefixWord, tailWord_2035464, baseEnd_2035464] using wordTrace_append hprefix tailTrace_2035464
  have hstable : (prefixWord ++ tailWord_2035464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035464).length < 2 ^ (prefixWord ++ tailWord_2035464).sum := by decide
  have hdescent : baseEnd_2035464 < baseStart_2035464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035479 : List Nat := [1, 1, 3, 4, 2, 2, 2, 1, 2, 4]
def baseStart_2035479 : Nat := 118140960795 + 2035479 * 2 ^ 59
def prefixEnd_2035479 : Nat := 4983230072969 + 3 ^ 40 * 2035479 * 2
def baseEnd_2035479 : Nat := 696786059422097941834339

theorem tailTrace_2035479 : CollatzResearch.WordTrace tailWord_2035479 prefixEnd_2035479 696786059422097941834339 := by
  unfold tailWord_2035479
  simp only [CollatzResearch.WordTrace]
  refine ⟨74240018192814689981901491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49493345461876459987934327 74240018192814689981901491)
  ·
    refine ⟨111360027289222034972852237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74240018192814689981901491 111360027289222034972852237)
    ·
      refine ⟨41760010233458263114819589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111360027289222034972852237 41760010233458263114819589)
      ·
        refine ⟨7830001918773424334028673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41760010233458263114819589 7830001918773424334028673)
        ·
          refine ⟨5872501439080068250521505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7830001918773424334028673 5872501439080068250521505)
          ·
            refine ⟨4404376079310051187891129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5872501439080068250521505 4404376079310051187891129)
            ·
              refine ⟨3303282059482538390918347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4404376079310051187891129 3303282059482538390918347)
              ·
                refine ⟨4954923089223807586377521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3303282059482538390918347 4954923089223807586377521)
                ·
                  refine ⟨3716192316917855689783141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4954923089223807586377521 3716192316917855689783141)
                  ·
                    refine ⟨696786059422097941834339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3716192316917855689783141 696786059422097941834339)
                    ·
                      rfl

theorem cell22_2035479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_2035479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035479 prefixEnd_2035479 := by exact prefixLift 2035479
  have htrace : WordTrace (prefixWord ++ tailWord_2035479) baseStart_2035479 baseEnd_2035479 := by
    simpa [prefixWord, tailWord_2035479, baseEnd_2035479] using wordTrace_append hprefix tailTrace_2035479
  have hstable : (prefixWord ++ tailWord_2035479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035479).length < 2 ^ (prefixWord ++ tailWord_2035479).sum := by decide
  have hdescent : baseEnd_2035479 < baseStart_2035479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035543 : List Nat := [1, 1, 3, 2, 5, 1, 2, 3, 1, 3]
def baseStart_2035543 : Nat := 118140960795 + 2035543 * 2 ^ 59
def prefixEnd_2035543 : Nat := 4983230072969 + 3 ^ 40 * 2035543 * 2
def baseEnd_2035543 : Nat := 696807967930023108234143

theorem tailTrace_2035543 : CollatzResearch.WordTrace tailWord_2035543 prefixEnd_2035543 696807967930023108234143 := by
  unfold tailWord_2035543
  simp only [CollatzResearch.WordTrace]
  refine ⟨74242352464582828912231283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49494901643055219274820855 74242352464582828912231283)
  ·
    refine ⟨111363528696874243368346925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74242352464582828912231283 111363528696874243368346925)
    ·
      refine ⟨41761323261327841263130097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111363528696874243368346925 41761323261327841263130097)
      ·
        refine ⟨31320992445995880947347573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41761323261327841263130097 31320992445995880947347573)
        ·
          refine ⟨2936343041812113838813835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31320992445995880947347573 2936343041812113838813835)
          ·
            refine ⟨4404514562718170758220753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936343041812113838813835 4404514562718170758220753)
            ·
              refine ⟨3303385922038628068665565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4404514562718170758220753 3303385922038628068665565)
              ·
                refine ⟨1238769720764485525749587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3303385922038628068665565 1238769720764485525749587)
                ·
                  refine ⟨1858154581146728288624381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1238769720764485525749587 1858154581146728288624381)
                  ·
                    refine ⟨696807967930023108234143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1858154581146728288624381 696807967930023108234143)
                    ·
                      rfl

theorem cell22_2035543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 1, 3].length) (baseStart_2035543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035543 prefixEnd_2035543 := by exact prefixLift 2035543
  have htrace : WordTrace (prefixWord ++ tailWord_2035543) baseStart_2035543 baseEnd_2035543 := by
    simpa [prefixWord, tailWord_2035543, baseEnd_2035543] using wordTrace_append hprefix tailTrace_2035543
  have hstable : (prefixWord ++ tailWord_2035543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035543).length < 2 ^ (prefixWord ++ tailWord_2035543).sum := by decide
  have hdescent : baseEnd_2035543 < baseStart_2035543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035554 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_2035554 : Nat := 118140960795 + 2035554 * 2 ^ 59
def prefixEnd_2035554 : Nat := 4983230072969 + 3 ^ 40 * 2035554 * 2
def baseEnd_2035554 : Nat := 696811733454822746209109

theorem tailTrace_2035554 : CollatzResearch.WordTrace tailWord_2035554 prefixEnd_2035554 696811733454822746209109 := by
  unfold tailWord_2035554
  simp only [CollatzResearch.WordTrace]
  refine ⟨18560688416885744447720429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49495169111695318527254477 18560688416885744447720429)
  ·
    refine ⟨6960258156332154167895161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18560688416885744447720429 6960258156332154167895161)
    ·
      refine ⟨5220193617249115625921371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6960258156332154167895161 5220193617249115625921371)
      ·
        refine ⟨7830290425873673438882057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5220193617249115625921371 7830290425873673438882057)
        ·
          refine ⟨5872717819405255079161543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7830290425873673438882057 5872717819405255079161543)
          ·
            refine ⟨8809076729107882618742315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5872717819405255079161543 8809076729107882618742315)
            ·
              refine ⟨13213615093661823928113473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8809076729107882618742315 13213615093661823928113473)
              ·
                refine ⟨9910211320246367946085105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13213615093661823928113473 9910211320246367946085105)
                ·
                  refine ⟨7432658490184775959563829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9910211320246367946085105 7432658490184775959563829)
                  ·
                    refine ⟨696811733454822746209109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7432658490184775959563829 696811733454822746209109)
                    ·
                      rfl

theorem cell22_2035554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_2035554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035554 prefixEnd_2035554 := by exact prefixLift 2035554
  have htrace : WordTrace (prefixWord ++ tailWord_2035554) baseStart_2035554 baseEnd_2035554 := by
    simpa [prefixWord, tailWord_2035554, baseEnd_2035554] using wordTrace_append hprefix tailTrace_2035554
  have hstable : (prefixWord ++ tailWord_2035554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035554).length < 2 ^ (prefixWord ++ tailWord_2035554).sum := by decide
  have hdescent : baseEnd_2035554 < baseStart_2035554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035556 : List Nat := [2, 3, 1, 1, 5, 2, 1, 2, 5]
def baseStart_2035556 : Nat := 118140960795 + 2035556 * 2 ^ 59
def prefixEnd_2035556 : Nat := 4983230072969 + 3 ^ 40 * 2035556 * 2
def baseEnd_2035556 : Nat := 232270806031898469219701

theorem tailTrace_2035556 : CollatzResearch.WordTrace tailWord_2035556 prefixEnd_2035556 232270806031898469219701 := by
  unfold tailWord_2035556
  simp only [CollatzResearch.WordTrace]
  refine ⟨37121413306767866066227261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49495217742357154754969681 37121413306767866066227261)
  ·
    refine ⟨13920529990037949774835223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37121413306767866066227261 13920529990037949774835223)
    ·
      refine ⟨20880794985056924662252835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13920529990037949774835223 20880794985056924662252835)
      ·
        refine ⟨31321192477585386993379253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20880794985056924662252835 31321192477585386993379253)
        ·
          refine ⟨2936361794773630030629305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31321192477585386993379253 2936361794773630030629305)
          ·
            refine ⟨2202271346080222522971979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2936361794773630030629305 2202271346080222522971979)
            ·
              refine ⟨3303407019120333784457969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2202271346080222522971979 3303407019120333784457969)
              ·
                refine ⟨2477555264340250338343477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3303407019120333784457969 2477555264340250338343477)
                ·
                  refine ⟨232270806031898469219701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2477555264340250338343477 232270806031898469219701)
                  ·
                    rfl

theorem cell22_2035556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_2035556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035556 prefixEnd_2035556 := by exact prefixLift 2035556
  have htrace : WordTrace (prefixWord ++ tailWord_2035556) baseStart_2035556 baseEnd_2035556 := by
    simpa [prefixWord, tailWord_2035556, baseEnd_2035556] using wordTrace_append hprefix tailTrace_2035556
  have hstable : (prefixWord ++ tailWord_2035556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035556).length < 2 ^ (prefixWord ++ tailWord_2035556).sum := by decide
  have hdescent : baseEnd_2035556 < baseStart_2035556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035618 : List Nat := [3, 3, 1, 2, 4, 1, 1, 1, 6]
def baseStart_2035618 : Nat := 118140960795 + 2035618 * 2 ^ 59
def prefixEnd_2035618 : Nat := 4983230072969 + 3 ^ 40 * 2035618 * 2
def baseEnd_2035618 : Nat := 232277880654249304202971

theorem tailTrace_2035618 : CollatzResearch.WordTrace tailWord_2035618 prefixEnd_2035618 232277880654249304202971 := by
  unfold tailWord_2035618
  simp only [CollatzResearch.WordTrace]
  refine ⟨18561271984827779180302877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49496725292874077814141005 18561271984827779180302877)
  ·
    refine ⟨6960476994310417192613579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18561271984827779180302877 6960476994310417192613579)
    ·
      refine ⟨10440715491465625788920369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6960476994310417192613579 10440715491465625788920369)
      ·
        refine ⟨7830536618599219341690277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10440715491465625788920369 7830536618599219341690277)
        ·
          refine ⟨1468225615987353626566927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7830536618599219341690277 1468225615987353626566927)
          ·
            refine ⟨2202338423981030439850391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468225615987353626566927 2202338423981030439850391)
            ·
              refine ⟨3303507635971545659775587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2202338423981030439850391 3303507635971545659775587)
              ·
                refine ⟨4955261453957318489663381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3303507635971545659775587 4955261453957318489663381)
                ·
                  refine ⟨232277880654249304202971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4955261453957318489663381 232277880654249304202971)
                  ·
                    rfl

theorem cell22_2035618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_2035618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035618 prefixEnd_2035618 := by exact prefixLift 2035618
  have htrace : WordTrace (prefixWord ++ tailWord_2035618) baseStart_2035618 baseEnd_2035618 := by
    simpa [prefixWord, tailWord_2035618, baseEnd_2035618] using wordTrace_append hprefix tailTrace_2035618
  have hstable : (prefixWord ++ tailWord_2035618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035618).length < 2 ^ (prefixWord ++ tailWord_2035618).sum := by decide
  have hdescent : baseEnd_2035618 < baseStart_2035618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035633 : List Nat := [1, 2, 2, 4, 2, 1, 4, 1, 2, 3]
def baseStart_2035633 : Nat := 118140960795 + 2035633 * 2 ^ 59
def prefixEnd_2035633 : Nat := 4983230072969 + 3 ^ 40 * 2035633 * 2
def baseEnd_2035633 : Nat := 696838776769292873483867

theorem tailTrace_2035633 : CollatzResearch.WordTrace tailWord_2035633 prefixEnd_2035633 696838776769292873483867 := by
  unfold tailWord_2035633
  simp only [CollatzResearch.WordTrace]
  refine ⟨74245635034256774283007553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49497090022837849522005035 74245635034256774283007553)
  ·
    refine ⟨55684226275692580712255665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74245635034256774283007553 55684226275692580712255665)
    ·
      refine ⟨41763169706769435534191749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55684226275692580712255665 41763169706769435534191749)
      ·
        refine ⟨7830594320019269162660953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41763169706769435534191749 7830594320019269162660953)
        ·
          refine ⟨5872945740014451871995715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7830594320019269162660953 5872945740014451871995715)
          ·
            refine ⟨8809418610021677807993573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5872945740014451871995715 8809418610021677807993573)
            ·
              refine ⟨1651765989379064588998795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8809418610021677807993573 1651765989379064588998795)
              ·
                refine ⟨2477648984068596883498193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1651765989379064588998795 2477648984068596883498193)
                ·
                  refine ⟨1858236738051447662623645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2477648984068596883498193 1858236738051447662623645)
                  ·
                    refine ⟨696838776769292873483867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1858236738051447662623645 696838776769292873483867)
                    ·
                      rfl

theorem cell22_2035633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 2, 3].length) (baseStart_2035633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035633 prefixEnd_2035633 := by exact prefixLift 2035633
  have htrace : WordTrace (prefixWord ++ tailWord_2035633) baseStart_2035633 baseEnd_2035633 := by
    simpa [prefixWord, tailWord_2035633, baseEnd_2035633] using wordTrace_append hprefix tailTrace_2035633
  have hstable : (prefixWord ++ tailWord_2035633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035633).length < 2 ^ (prefixWord ++ tailWord_2035633).sum := by decide
  have hdescent : baseEnd_2035633 < baseStart_2035633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035642 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 4, 6]
def baseStart_2035642 : Nat := 118140960795 + 2035642 * 2 ^ 59
def prefixEnd_2035642 : Nat := 4983230072969 + 3 ^ 40 * 2035642 * 2
def baseEnd_2035642 : Nat := 696841857653219850008839

theorem tailTrace_2035642 : CollatzResearch.WordTrace tailWord_2035642 prefixEnd_2035642 696841857653219850008839 := by
  unfold tailWord_2035642
  simp only [CollatzResearch.WordTrace]
  refine ⟨18561490822806042205021295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49497308860816112546723453 18561490822806042205021295)
  ·
    refine ⟨27842236234209063307531943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18561490822806042205021295 27842236234209063307531943)
    ·
      refine ⟨41763354351313594961297915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27842236234209063307531943 41763354351313594961297915)
      ·
        refine ⟨62645031526970392441946873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41763354351313594961297915 62645031526970392441946873)
        ·
          refine ⟨46983773645227794331460155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62645031526970392441946873 46983773645227794331460155)
          ·
            refine ⟨70475660467841691497190233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46983773645227794331460155 70475660467841691497190233)
            ·
              refine ⟨52856745350881268622892675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70475660467841691497190233 52856745350881268622892675)
              ·
                refine ⟨79285118026321902934339013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52856745350881268622892675 79285118026321902934339013)
                ·
                  refine ⟨14865959629935356800188565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79285118026321902934339013 14865959629935356800188565)
                  ·
                    refine ⟨696841857653219850008839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14865959629935356800188565 696841857653219850008839)
                    ·
                      rfl

theorem cell22_2035642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_2035642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035642 prefixEnd_2035642 := by exact prefixLift 2035642
  have htrace : WordTrace (prefixWord ++ tailWord_2035642) baseStart_2035642 baseEnd_2035642 := by
    simpa [prefixWord, tailWord_2035642, baseEnd_2035642] using wordTrace_append hprefix tailTrace_2035642
  have hstable : (prefixWord ++ tailWord_2035642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035642).length < 2 ^ (prefixWord ++ tailWord_2035642).sum := by decide
  have hdescent : baseEnd_2035642 < baseStart_2035642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035704 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 3, 4]
def baseStart_2035704 : Nat := 118140960795 + 2035704 * 2 ^ 59
def prefixEnd_2035704 : Nat := 4983230072969 + 3 ^ 40 * 2035704 * 2
def baseEnd_2035704 : Nat := 696863081520272354958649

theorem tailTrace_2035704 : CollatzResearch.WordTrace tailWord_2035704 prefixEnd_2035704 696863081520272354958649 := by
  unfold tailWord_2035704
  simp only [CollatzResearch.WordTrace]
  refine ⟨37124112308499776704421083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49498816411333035605894777 37124112308499776704421083)
  ·
    refine ⟨55686168462749665056631625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37124112308499776704421083 55686168462749665056631625)
    ·
      refine ⟨41764626347062248792473719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55686168462749665056631625 41764626347062248792473719)
      ·
        refine ⟨62646939520593373188710579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41764626347062248792473719 62646939520593373188710579)
        ·
          refine ⟨93970409280890059783065869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62646939520593373188710579 93970409280890059783065869)
          ·
            refine ⟨35238903480333772418649701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93970409280890059783065869 35238903480333772418649701)
            ·
              refine ⟨6607294402562582328496819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35238903480333772418649701 6607294402562582328496819)
              ·
                refine ⟨9910941603843873492745229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6607294402562582328496819 9910941603843873492745229)
                ·
                  refine ⟨3716603101441452559779461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9910941603843873492745229 3716603101441452559779461)
                  ·
                    refine ⟨696863081520272354958649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3716603101441452559779461 696863081520272354958649)
                    ·
                      rfl

theorem cell22_2035704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_2035704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035704 prefixEnd_2035704 := by exact prefixLift 2035704
  have htrace : WordTrace (prefixWord ++ tailWord_2035704) baseStart_2035704 baseEnd_2035704 := by
    simpa [prefixWord, tailWord_2035704, baseEnd_2035704] using wordTrace_append hprefix tailTrace_2035704
  have hstable : (prefixWord ++ tailWord_2035704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035704).length < 2 ^ (prefixWord ++ tailWord_2035704).sum := by decide
  have hdescent : baseEnd_2035704 < baseStart_2035704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035725 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 7]
def baseStart_2035725 : Nat := 118140960795 + 2035725 * 2 ^ 59
def prefixEnd_2035725 : Nat := 4983230072969 + 3 ^ 40 * 2035725 * 2
def baseEnd_2035725 : Nat := 232290090083145100061195

theorem tailTrace_2035725 : CollatzResearch.WordTrace tailWord_2035725 prefixEnd_2035725 232290090083145100061195 := by
  unfold tailWord_2035725
  simp only [CollatzResearch.WordTrace]
  refine ⟨74248990549923473995356629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49499327033282315996904419 74248990549923473995356629)
  ·
    refine ⟨1740210716013831421766171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 74248990549923473995356629 1740210716013831421766171)
    ·
      refine ⟨2610316074020747132649257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1740210716013831421766171 2610316074020747132649257)
      ·
        refine ⟨1957737055515560349486943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2610316074020747132649257 1957737055515560349486943)
        ·
          refine ⟨2936605583273340524230415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1957737055515560349486943 2936605583273340524230415)
          ·
            refine ⟨4404908374910010786345623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936605583273340524230415 4404908374910010786345623)
            ·
              refine ⟨6607362562365016179518435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404908374910010786345623 6607362562365016179518435)
              ·
                refine ⟨9911043843547524269277653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6607362562365016179518435 9911043843547524269277653)
                ·
                  refine ⟨232290090083145100061195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9911043843547524269277653 232290090083145100061195)
                  ·
                    rfl

theorem cell22_2035725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_2035725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035725 prefixEnd_2035725 := by exact prefixLift 2035725
  have htrace : WordTrace (prefixWord ++ tailWord_2035725) baseStart_2035725 baseEnd_2035725 := by
    simpa [prefixWord, tailWord_2035725, baseEnd_2035725] using wordTrace_append hprefix tailTrace_2035725
  have hstable : (prefixWord ++ tailWord_2035725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035725).length < 2 ^ (prefixWord ++ tailWord_2035725).sum := by decide
  have hdescent : baseEnd_2035725 < baseStart_2035725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035736 : List Nat := [2, 1, 2, 3, 2, 1, 1, 6, 4]
def baseStart_2035736 : Nat := 118140960795 + 2035736 * 2 ^ 59
def prefixEnd_2035736 : Nat := 4983230072969 + 3 ^ 40 * 2035736 * 2
def baseEnd_2035736 : Nat := 232291345258078312719517

theorem tailTrace_2035736 : CollatzResearch.WordTrace tailWord_2035736 prefixEnd_2035736 232291345258078312719517 := by
  unfold tailWord_2035736
  simp only [CollatzResearch.WordTrace]
  refine ⟨37124695876441811437003531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49499594501922415249338041 37124695876441811437003531)
  ·
    refine ⟨55687043814662717155505297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37124695876441811437003531 55687043814662717155505297)
    ·
      refine ⟨41765282860997037866628973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55687043814662717155505297 41765282860997037866628973)
      ·
        refine ⟨15661981072873889199985865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41765282860997037866628973 15661981072873889199985865)
        ·
          refine ⟨11746485804655416899989399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15661981072873889199985865 11746485804655416899989399)
          ·
            refine ⟨17619728706983125349984099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11746485804655416899989399 17619728706983125349984099)
            ·
              refine ⟨26429593060474688024976149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17619728706983125349984099 26429593060474688024976149)
              ·
                refine ⟨1238887174709751001170757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26429593060474688024976149 1238887174709751001170757)
                ·
                  refine ⟨232291345258078312719517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1238887174709751001170757 232291345258078312719517)
                  ·
                    rfl

theorem cell22_2035736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 4].length) (baseStart_2035736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035736 prefixEnd_2035736 := by exact prefixLift 2035736
  have htrace : WordTrace (prefixWord ++ tailWord_2035736) baseStart_2035736 baseEnd_2035736 := by
    simpa [prefixWord, tailWord_2035736, baseEnd_2035736] using wordTrace_append hprefix tailTrace_2035736
  have hstable : (prefixWord ++ tailWord_2035736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035736).length < 2 ^ (prefixWord ++ tailWord_2035736).sum := by decide
  have hdescent : baseEnd_2035736 < baseStart_2035736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035749 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 1, 6]
def baseStart_2035749 : Nat := 118140960795 + 2035749 * 2 ^ 59
def prefixEnd_2035749 : Nat := 4983230072969 + 3 ^ 40 * 2035749 * 2
def baseEnd_2035749 : Nat := 696878485939907237583511

theorem tailTrace_2035749 : CollatzResearch.WordTrace tailWord_2035749 prefixEnd_2035749 696878485939907237583511 := by
  unfold tailWord_2035749
  simp only [CollatzResearch.WordTrace]
  refine ⟨74249865901836526094230301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49499910601224350729486867 74249865901836526094230301)
  ·
    refine ⟨27843699713188697285336363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74249865901836526094230301 27843699713188697285336363)
    ·
      refine ⟨41765549569783045928004545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27843699713188697285336363 41765549569783045928004545)
      ·
        refine ⟨31324162177337284446003409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41765549569783045928004545 31324162177337284446003409)
        ·
          refine ⟨23493121633002963334502557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31324162177337284446003409 23493121633002963334502557)
          ·
            refine ⟨8809920612376111250438459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23493121633002963334502557 8809920612376111250438459)
            ·
              refine ⟨13214880918564166875657689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8809920612376111250438459 13214880918564166875657689)
              ·
                refine ⟨9911160688923125156743267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13214880918564166875657689 9911160688923125156743267)
                ·
                  refine ⟨14866741033384687735114901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9911160688923125156743267 14866741033384687735114901)
                  ·
                    refine ⟨696878485939907237583511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14866741033384687735114901 696878485939907237583511)
                    ·
                      rfl

theorem cell22_2035749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_2035749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035749 prefixEnd_2035749 := by exact prefixLift 2035749
  have htrace : WordTrace (prefixWord ++ tailWord_2035749) baseStart_2035749 baseEnd_2035749 := by
    simpa [prefixWord, tailWord_2035749, baseEnd_2035749] using wordTrace_append hprefix tailTrace_2035749
  have hstable : (prefixWord ++ tailWord_2035749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035749).length < 2 ^ (prefixWord ++ tailWord_2035749).sum := by decide
  have hdescent : baseEnd_2035749 < baseStart_2035749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035766 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_2035766 : Nat := 118140960795 + 2035766 * 2 ^ 59
def prefixEnd_2035766 : Nat := 4983230072969 + 3 ^ 40 * 2035766 * 2
def baseEnd_2035766 : Nat := 696884305387324859908459

theorem tailTrace_2035766 : CollatzResearch.WordTrace tailWord_2035766 prefixEnd_2035766 696884305387324859908459 := by
  unfold tailWord_2035766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4640655371423433624849947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49500323961849958665066101 4640655371423433624849947)
  ·
    refine ⟨6960983057135150437274921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4640655371423433624849947 6960983057135150437274921)
    ·
      refine ⟨5220737292851362827956191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6960983057135150437274921 5220737292851362827956191)
      ·
        refine ⟨7831105939277044241934287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5220737292851362827956191 7831105939277044241934287)
        ·
          refine ⟨11746658908915566362901431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7831105939277044241934287 11746658908915566362901431)
          ·
            refine ⟨17619988363373349544352147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11746658908915566362901431 17619988363373349544352147)
            ·
              refine ⟨26429982545060024316528221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17619988363373349544352147 26429982545060024316528221)
              ·
                refine ⟨9911243454397509118698083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26429982545060024316528221 9911243454397509118698083)
                ·
                  refine ⟨14866865181596263678047125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9911243454397509118698083 14866865181596263678047125)
                  ·
                    refine ⟨696884305387324859908459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14866865181596263678047125 696884305387324859908459)
                    ·
                      rfl

theorem cell22_2035766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_2035766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035766 prefixEnd_2035766 := by exact prefixLift 2035766
  have htrace : WordTrace (prefixWord ++ tailWord_2035766) baseStart_2035766 baseEnd_2035766 := by
    simpa [prefixWord, tailWord_2035766, baseEnd_2035766] using wordTrace_append hprefix tailTrace_2035766
  have hstable : (prefixWord ++ tailWord_2035766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035766).length < 2 ^ (prefixWord ++ tailWord_2035766).sum := by decide
  have hdescent : baseEnd_2035766 < baseStart_2035766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035798 : List Nat := [5, 2, 2, 1, 1, 1, 1, 9]
def baseStart_2035798 : Nat := 118140960795 + 2035798 * 2 ^ 59
def prefixEnd_2035798 : Nat := 4983230072969 + 3 ^ 40 * 2035798 * 2
def baseEnd_2035798 : Nat := 77432806626809715900929

theorem tailTrace_2035798 : CollatzResearch.WordTrace tailWord_2035798 prefixEnd_2035798 77432806626809715900929 := by
  unfold tailWord_2035798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4640728317416187966422753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49501102052439338308509365 4640728317416187966422753)
  ·
    refine ⟨3480546238062140974817065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4640728317416187966422753 3480546238062140974817065)
    ·
      refine ⟨2610409678546605731112799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3480546238062140974817065 2610409678546605731112799)
      ·
        refine ⟨3915614517819908596669199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2610409678546605731112799 3915614517819908596669199)
        ·
          refine ⟨5873421776729862895003799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3915614517819908596669199 5873421776729862895003799)
          ·
            refine ⟨8810132665094794342505699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5873421776729862895003799 8810132665094794342505699)
            ·
              refine ⟨13215198997642191513758549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8810132665094794342505699 13215198997642191513758549)
              ·
                refine ⟨77432806626809715900929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13215198997642191513758549 77432806626809715900929)
                ·
                  rfl

theorem cell22_2035798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_2035798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035798 prefixEnd_2035798 := by exact prefixLift 2035798
  have htrace : WordTrace (prefixWord ++ tailWord_2035798) baseStart_2035798 baseEnd_2035798 := by
    simpa [prefixWord, tailWord_2035798, baseEnd_2035798] using wordTrace_append hprefix tailTrace_2035798
  have hstable : (prefixWord ++ tailWord_2035798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035798).length < 2 ^ (prefixWord ++ tailWord_2035798).sum := by decide
  have hdescent : baseEnd_2035798 < baseStart_2035798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035871 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 8]
def baseStart_2035871 : Nat := 118140960795 + 2035871 * 2 ^ 59
def prefixEnd_2035871 : Nat := 4983230072969 + 3 ^ 40 * 2035871 * 2
def baseEnd_2035871 : Nat := 232306749677713195344379

theorem tailTrace_2035871 : CollatzResearch.WordTrace tailWord_2035871 prefixEnd_2035871 232306749677713195344379 := by
  unfold tailWord_2035871
  simp only [CollatzResearch.WordTrace]
  refine ⟨74254315607394540930171467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49502877071596360620114311 74254315607394540930171467)
  ·
    refine ⟨111381473411091811395257201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74254315607394540930171467 111381473411091811395257201)
    ·
      refine ⟨83536105058318858546442901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111381473411091811395257201 83536105058318858546442901)
      ·
        refine ⟨3915754924608696494364511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83536105058318858546442901 3915754924608696494364511)
        ·
          refine ⟨5873632386913044741546767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3915754924608696494364511 5873632386913044741546767)
          ·
            refine ⟨8810448580369567112320151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5873632386913044741546767 8810448580369567112320151)
            ·
              refine ⟨13215672870554350668480227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8810448580369567112320151 13215672870554350668480227)
              ·
                refine ⟨19823509305831526002720341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13215672870554350668480227 19823509305831526002720341)
                ·
                  refine ⟨232306749677713195344379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19823509305831526002720341 232306749677713195344379)
                  ·
                    rfl

theorem cell22_2035871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 8].length) (baseStart_2035871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035871 prefixEnd_2035871 := by exact prefixLift 2035871
  have htrace : WordTrace (prefixWord ++ tailWord_2035871) baseStart_2035871 baseEnd_2035871 := by
    simpa [prefixWord, tailWord_2035871, baseEnd_2035871] using wordTrace_append hprefix tailTrace_2035871
  have hstable : (prefixWord ++ tailWord_2035871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035871).length < 2 ^ (prefixWord ++ tailWord_2035871).sum := by decide
  have hdescent : baseEnd_2035871 < baseStart_2035871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035899 : List Nat := [1, 1, 1, 1, 1, 2, 15]
def baseStart_2035899 : Nat := 118140960795 + 2035899 * 2 ^ 59
def prefixEnd_2035899 : Nat := 4983230072969 + 3 ^ 40 * 2035899 * 2
def baseEnd_2035899 : Nat := 25812216074272475790113

theorem tailTrace_2035899 : CollatzResearch.WordTrace tailWord_2035899 prefixEnd_2035899 25812216074272475790113 := by
  unfold tailWord_2035899
  simp only [CollatzResearch.WordTrace]
  refine ⟨74255336851293101712190751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49503557900862067808127167 74255336851293101712190751)
  ·
    refine ⟨111383005276939652568286127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74255336851293101712190751 111383005276939652568286127)
    ·
      refine ⟨167074507915409478852429191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111383005276939652568286127 167074507915409478852429191)
      ·
        refine ⟨250611761873114218278643787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167074507915409478852429191 250611761873114218278643787)
        ·
          refine ⟨375917642809671327417965681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250611761873114218278643787 375917642809671327417965681)
          ·
            refine ⟨281938232107253495563474261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375917642809671327417965681 281938232107253495563474261)
            ·
              refine ⟨25812216074272475790113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 281938232107253495563474261 25812216074272475790113)
              ·
                rfl

theorem cell22_2035899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 15].length) (baseStart_2035899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035899 prefixEnd_2035899 := by exact prefixLift 2035899
  have htrace : WordTrace (prefixWord ++ tailWord_2035899) baseStart_2035899 baseEnd_2035899 := by
    simpa [prefixWord, tailWord_2035899, baseEnd_2035899] using wordTrace_append hprefix tailTrace_2035899
  have hstable : (prefixWord ++ tailWord_2035899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035899).length < 2 ^ (prefixWord ++ tailWord_2035899).sum := by decide
  have hdescent : baseEnd_2035899 < baseStart_2035899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035901 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_2035901 : Nat := 118140960795 + 2035901 * 2 ^ 59
def prefixEnd_2035901 : Nat := 4983230072969 + 3 ^ 40 * 2035901 * 2
def baseEnd_2035901 : Nat := 696930518646229507783045

theorem tailTrace_2035901 : CollatzResearch.WordTrace tailWord_2035901 prefixEnd_2035901 696930518646229507783045 := by
  unfold tailWord_2035901
  simp only [CollatzResearch.WordTrace]
  refine ⟨74255409797285856053763557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49503606531523904035842371 74255409797285856053763557)
  ·
    refine ⟨13922889336991098010080667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74255409797285856053763557 13922889336991098010080667)
    ·
      refine ⟨20884334005486647015121001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13922889336991098010080667 20884334005486647015121001)
      ·
        refine ⟨15663250504114985261340751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20884334005486647015121001 15663250504114985261340751)
        ·
          refine ⟨23494875756172477892011127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15663250504114985261340751 23494875756172477892011127)
          ·
            refine ⟨35242313634258716838016691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23494875756172477892011127 35242313634258716838016691)
            ·
              refine ⟨52863470451388075257025037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35242313634258716838016691 52863470451388075257025037)
              ·
                refine ⟨19823801419270528221384389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52863470451388075257025037 19823801419270528221384389)
                ·
                  refine ⟨3716962766113224041509573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19823801419270528221384389 3716962766113224041509573)
                  ·
                    refine ⟨696930518646229507783045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3716962766113224041509573 696930518646229507783045)
                    ·
                      rfl

theorem cell22_2035901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_2035901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035901 prefixEnd_2035901 := by exact prefixLift 2035901
  have htrace : WordTrace (prefixWord ++ tailWord_2035901) baseStart_2035901 baseEnd_2035901 := by
    simpa [prefixWord, tailWord_2035901, baseEnd_2035901] using wordTrace_append hprefix tailTrace_2035901
  have hstable : (prefixWord ++ tailWord_2035901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035901).length < 2 ^ (prefixWord ++ tailWord_2035901).sum := by decide
  have hdescent : baseEnd_2035901 < baseStart_2035901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035905 : List Nat := [1, 2, 6, 1, 2, 1, 2, 1, 6]
def baseStart_2035905 : Nat := 118140960795 + 2035905 * 2 ^ 59
def prefixEnd_2035905 : Nat := 4983230072969 + 3 ^ 40 * 2035905 * 2
def baseEnd_2035905 : Nat := 232310629309324943561011

theorem tailTrace_2035905 : CollatzResearch.WordTrace tailWord_2035905 prefixEnd_2035905 232310629309324943561011 := by
  unfold tailWord_2035905
  simp only [CollatzResearch.WordTrace]
  refine ⟨74255555689271364736909169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49503703792847576491272779 74255555689271364736909169)
  ·
    refine ⟨55691666766953523552681877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74255555689271364736909169 55691666766953523552681877)
    ·
      refine ⟨2610546879700946416531963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55691666766953523552681877 2610546879700946416531963)
      ·
        refine ⟨3915820319551419624797945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2610546879700946416531963 3915820319551419624797945)
        ·
          refine ⟨2936865239663564718598459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3915820319551419624797945 2936865239663564718598459)
          ·
            refine ⟨4405297859495347077897689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936865239663564718598459 4405297859495347077897689)
            ·
              refine ⟨3303973394621510308423267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4405297859495347077897689 3303973394621510308423267)
              ·
                refine ⟨4955960091932265462634901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3303973394621510308423267 4955960091932265462634901)
                ·
                  refine ⟨232310629309324943561011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4955960091932265462634901 232310629309324943561011)
                  ·
                    rfl

theorem cell22_2035905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 6].length) (baseStart_2035905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035905 prefixEnd_2035905 := by exact prefixLift 2035905
  have htrace : WordTrace (prefixWord ++ tailWord_2035905) baseStart_2035905 baseEnd_2035905 := by
    simpa [prefixWord, tailWord_2035905, baseEnd_2035905] using wordTrace_append hprefix tailTrace_2035905
  have hstable : (prefixWord ++ tailWord_2035905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035905).length < 2 ^ (prefixWord ++ tailWord_2035905).sum := by decide
  have hdescent : baseEnd_2035905 < baseStart_2035905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035933 : List Nat := [1, 4, 3, 2, 1, 2, 1, 8]
def baseStart_2035933 : Nat := 118140960795 + 2035933 * 2 ^ 59
def prefixEnd_2035933 : Nat := 4983230072969 + 3 ^ 40 * 2035933 * 2
def baseEnd_2035933 : Nat := 77437941433354676775883

theorem tailTrace_2035933 : CollatzResearch.WordTrace tailWord_2035933 prefixEnd_2035933 77437941433354676775883 := by
  unfold tailWord_2035933
  simp only [CollatzResearch.WordTrace]
  refine ⟨74256576933169925518928453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49504384622113283679285635 74256576933169925518928453)
  ·
    refine ⟨13923108174969361034799085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74256576933169925518928453 13923108174969361034799085)
    ·
      refine ⟨5221165565613510388049657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13923108174969361034799085 5221165565613510388049657)
      ·
        refine ⟨3915874174210132791037243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5221165565613510388049657 3915874174210132791037243)
        ·
          refine ⟨5873811261315199186555865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3915874174210132791037243 5873811261315199186555865)
          ·
            refine ⟨4405358445986399389916899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5873811261315199186555865 4405358445986399389916899)
            ·
              refine ⟨6608037668979599084875349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4405358445986399389916899 6608037668979599084875349)
              ·
                refine ⟨77437941433354676775883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6608037668979599084875349 77437941433354676775883)
                ·
                  rfl

theorem cell22_2035933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 8].length) (baseStart_2035933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035933 prefixEnd_2035933 := by exact prefixLift 2035933
  have htrace : WordTrace (prefixWord ++ tailWord_2035933) baseStart_2035933 baseEnd_2035933 := by
    simpa [prefixWord, tailWord_2035933, baseEnd_2035933] using wordTrace_append hprefix tailTrace_2035933
  have hstable : (prefixWord ++ tailWord_2035933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035933).length < 2 ^ (prefixWord ++ tailWord_2035933).sum := by decide
  have hdescent : baseEnd_2035933 < baseStart_2035933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035939 : List Nat := [1, 1, 1, 8, 2, 1, 1, 3, 4]
def baseStart_2035939 : Nat := 118140960795 + 2035939 * 2 ^ 59
def prefixEnd_2035939 : Nat := 4983230072969 + 3 ^ 40 * 2035939 * 2
def baseEnd_2035939 : Nat := 232314508940936691777643

theorem tailTrace_2035939 : CollatzResearch.WordTrace tailWord_2035939 prefixEnd_2035939 232314508940936691777643 := by
  unfold tailWord_2035939
  simp only [CollatzResearch.WordTrace]
  refine ⟨74256795771148188543646871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49504530514098792362431247 74256795771148188543646871)
  ·
    refine ⟨111385193656722282815470307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74256795771148188543646871 111385193656722282815470307)
    ·
      refine ⟨167077790485083424223205461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111385193656722282815470307 167077790485083424223205461)
      ·
        refine ⟨1957942857247071377615689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 167077790485083424223205461 1957942857247071377615689)
        ·
          refine ⟨1468457142935303533211767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1957942857247071377615689 1468457142935303533211767)
          ·
            refine ⟨2202685714402955299817651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468457142935303533211767 2202685714402955299817651)
            ·
              refine ⟨3304028571604432949726477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2202685714402955299817651 3304028571604432949726477)
              ·
                refine ⟨1239010714351662356147429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3304028571604432949726477 1239010714351662356147429)
                ·
                  refine ⟨232314508940936691777643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1239010714351662356147429 232314508940936691777643)
                  ·
                    rfl

theorem cell22_2035939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 4].length) (baseStart_2035939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035939 prefixEnd_2035939 := by exact prefixLift 2035939
  have htrace : WordTrace (prefixWord ++ tailWord_2035939) baseStart_2035939 baseEnd_2035939 := by
    simpa [prefixWord, tailWord_2035939, baseEnd_2035939] using wordTrace_append hprefix tailTrace_2035939
  have hstable : (prefixWord ++ tailWord_2035939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035939).length < 2 ^ (prefixWord ++ tailWord_2035939).sum := by decide
  have hdescent : baseEnd_2035939 < baseStart_2035939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035965 : List Nat := [1, 4, 1, 1, 1, 1, 1, 8, 1, 3]
def baseStart_2035965 : Nat := 118140960795 + 2035965 * 2 ^ 59
def prefixEnd_2035965 : Nat := 4983230072969 + 3 ^ 40 * 2035965 * 2
def baseEnd_2035965 : Nat := 696952427154154674182849

theorem tailTrace_2035965 : CollatzResearch.WordTrace tailWord_2035965 prefixEnd_2035965 696952427154154674182849 := by
  unfold tailWord_2035965
  simp only [CollatzResearch.WordTrace]
  refine ⟨74257744069053994984093349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49505162712702663322728899 74257744069053994984093349)
  ·
    refine ⟨13923327012947624059517503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74257744069053994984093349 13923327012947624059517503)
    ·
      refine ⟨20884990519421436089276255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13923327012947624059517503 20884990519421436089276255)
      ·
        refine ⟨31327485779132154133914383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20884990519421436089276255 31327485779132154133914383)
        ·
          refine ⟨46991228668698231200871575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31327485779132154133914383 46991228668698231200871575)
          ·
            refine ⟨70486843003047346801307363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46991228668698231200871575 70486843003047346801307363)
            ·
              refine ⟨105730264504571020201961045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70486843003047346801307363 105730264504571020201961045)
              ·
                refine ⟨1239026537162941642991731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 105730264504571020201961045 1239026537162941642991731)
                ·
                  refine ⟨1858539805744412464487597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239026537162941642991731 1858539805744412464487597)
                  ·
                    refine ⟨696952427154154674182849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1858539805744412464487597 696952427154154674182849)
                    ·
                      rfl

theorem cell22_2035965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_2035965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2035965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2035965 prefixEnd_2035965 := by exact prefixLift 2035965
  have htrace : WordTrace (prefixWord ++ tailWord_2035965) baseStart_2035965 baseEnd_2035965 := by
    simpa [prefixWord, tailWord_2035965, baseEnd_2035965] using wordTrace_append hprefix tailTrace_2035965
  have hstable : (prefixWord ++ tailWord_2035965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035965).length < 2 ^ (prefixWord ++ tailWord_2035965).sum := by decide
  have hdescent : baseEnd_2035965 < baseStart_2035965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036072 : List Nat := [2, 1, 4, 2, 2, 1, 3, 2, 2, 3]
def baseStart_2036072 : Nat := 118140960795 + 2036072 * 2 ^ 59
def prefixEnd_2036072 : Nat := 4983230072969 + 3 ^ 40 * 2036072 * 2
def baseEnd_2036072 : Nat := 696989055440842061757521

theorem tailTrace_2036072 : CollatzResearch.WordTrace tailWord_2036072 prefixEnd_2036072 696989055440842061757521 := by
  unfold tailWord_2036072
  simp only [CollatzResearch.WordTrace]
  refine ⟨37130823339833176129119235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49507764453110901505492313 37130823339833176129119235)
  ·
    refine ⟨55696235009749764193678853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37130823339833176129119235 55696235009749764193678853)
    ·
      refine ⟨10443044064328080786314785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55696235009749764193678853 10443044064328080786314785)
      ·
        refine ⟨7832283048246060589736089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10443044064328080786314785 7832283048246060589736089)
        ·
          refine ⟨5874212286184545442302067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7832283048246060589736089 5874212286184545442302067)
          ·
            refine ⟨8811318429276818163453101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5874212286184545442302067 8811318429276818163453101)
            ·
              refine ⟨3304244410978806811294913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8811318429276818163453101 3304244410978806811294913)
              ·
                refine ⟨2478183308234105108471185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3304244410978806811294913 2478183308234105108471185)
                ·
                  refine ⟨1858637481175578831353389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2478183308234105108471185 1858637481175578831353389)
                  ·
                    refine ⟨696989055440842061757521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1858637481175578831353389 696989055440842061757521)
                    ·
                      rfl

theorem cell22_2036072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_2036072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036072 prefixEnd_2036072 := by exact prefixLift 2036072
  have htrace : WordTrace (prefixWord ++ tailWord_2036072) baseStart_2036072 baseEnd_2036072 := by
    simpa [prefixWord, tailWord_2036072, baseEnd_2036072] using wordTrace_append hprefix tailTrace_2036072
  have hstable : (prefixWord ++ tailWord_2036072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036072).length < 2 ^ (prefixWord ++ tailWord_2036072).sum := by decide
  have hdescent : baseEnd_2036072 < baseStart_2036072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036083 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 7, 3]
def baseStart_2036083 : Nat := 118140960795 + 2036083 * 2 ^ 59
def prefixEnd_2036083 : Nat := 4983230072969 + 3 ^ 40 * 2036083 * 2
def baseEnd_2036083 : Nat := 696992820965641699732487

theorem tailTrace_2036083 : CollatzResearch.WordTrace tailWord_2036083 prefixEnd_2036083 696992820965641699732487 := by
  unfold tailWord_2036083
  simp only [CollatzResearch.WordTrace]
  refine ⟨74262047882626501136888903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49508031921751000757925935 74262047882626501136888903)
  ·
    refine ⟨111393071823939751705333355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74262047882626501136888903 111393071823939751705333355)
    ·
      refine ⟨167089607735909627558000033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111393071823939751705333355 167089607735909627558000033)
      ·
        refine ⟨125317205801932220668500025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167089607735909627558000033 125317205801932220668500025)
        ·
          refine ⟨93987904351449165501375019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125317205801932220668500025 93987904351449165501375019)
          ·
            refine ⟨140981856527173748252062529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93987904351449165501375019 140981856527173748252062529)
            ·
              refine ⟨105736392395380311189046897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140981856527173748252062529 105736392395380311189046897)
              ·
                refine ⟨79302294296535233391785173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105736392395380311189046897 79302294296535233391785173)
                ·
                  refine ⟨1858647522575044532619965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 79302294296535233391785173 1858647522575044532619965)
                  ·
                    refine ⟨696992820965641699732487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1858647522575044532619965 696992820965641699732487)
                    ·
                      rfl

theorem cell22_2036083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 3].length) (baseStart_2036083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036083 prefixEnd_2036083 := by exact prefixLift 2036083
  have htrace : WordTrace (prefixWord ++ tailWord_2036083) baseStart_2036083 baseEnd_2036083 := by
    simpa [prefixWord, tailWord_2036083, baseEnd_2036083] using wordTrace_append hprefix tailTrace_2036083
  have hstable : (prefixWord ++ tailWord_2036083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036083).length < 2 ^ (prefixWord ++ tailWord_2036083).sum := by decide
  have hdescent : baseEnd_2036083 < baseStart_2036083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036100 : List Nat := [2, 3, 2, 1, 1, 2, 1, 4, 3, 3]
def baseStart_2036100 : Nat := 118140960795 + 2036100 * 2 ^ 59
def prefixEnd_2036100 : Nat := 4983230072969 + 3 ^ 40 * 2036100 * 2
def baseEnd_2036100 : Nat := 696998640413059322057435

theorem tailTrace_2036100 : CollatzResearch.WordTrace tailWord_2036100 prefixEnd_2036100 696998640413059322057435 := by
  unfold tailWord_2036100
  simp only [CollatzResearch.WordTrace]
  refine ⟨37131333961782456520128877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49508445282376608693505169 37131333961782456520128877)
  ·
    refine ⟨13924250235668421195048329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37131333961782456520128877 13924250235668421195048329)
    ·
      refine ⟨10443187676751315896286247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13924250235668421195048329 10443187676751315896286247)
      ·
        refine ⟨15664781515126973844429371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10443187676751315896286247 15664781515126973844429371)
        ·
          refine ⟨23497172272690460766644057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15664781515126973844429371 23497172272690460766644057)
          ·
            refine ⟨17622879204517845574983043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23497172272690460766644057 17622879204517845574983043)
            ·
              refine ⟨26434318806776768362474565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17622879204517845574983043 26434318806776768362474565)
              ·
                refine ⟨4956434776270644067963981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26434318806776768362474565 4956434776270644067963981)
                ·
                  refine ⟨1858663041101491525486493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4956434776270644067963981 1858663041101491525486493)
                  ·
                    refine ⟨696998640413059322057435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1858663041101491525486493 696998640413059322057435)
                    ·
                      rfl

theorem cell22_2036100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_2036100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036100 prefixEnd_2036100 := by exact prefixLift 2036100
  have htrace : WordTrace (prefixWord ++ tailWord_2036100) baseStart_2036100 baseEnd_2036100 := by
    simpa [prefixWord, tailWord_2036100, baseEnd_2036100] using wordTrace_append hprefix tailTrace_2036100
  have hstable : (prefixWord ++ tailWord_2036100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036100).length < 2 ^ (prefixWord ++ tailWord_2036100).sum := by decide
  have hdescent : baseEnd_2036100 < baseStart_2036100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036130 : List Nat := [3, 3, 1, 2, 1, 1, 2, 4, 5]
def baseStart_2036130 : Nat := 118140960795 + 2036130 * 2 ^ 59
def prefixEnd_2036130 : Nat := 4983230072969 + 3 ^ 40 * 2036130 * 2
def baseEnd_2036130 : Nat := 232336303342049747935781

theorem tailTrace_2036130 : CollatzResearch.WordTrace tailWord_2036130 prefixEnd_2036130 232336303342049747935781 := by
  unfold tailWord_2036130
  simp only [CollatzResearch.WordTrace]
  refine ⟨18565940528364057040962461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49509174742304152109233229 18565940528364057040962461)
  ·
    refine ⟨6962227698136521390360923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18565940528364057040962461 6962227698136521390360923)
    ·
      refine ⟨10443341547204782085541385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6962227698136521390360923 10443341547204782085541385)
      ·
        refine ⟨7832506160403586564156039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10443341547204782085541385 7832506160403586564156039)
        ·
          refine ⟨11748759240605379846234059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7832506160403586564156039 11748759240605379846234059)
          ·
            refine ⟨17623138860908069769351089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11748759240605379846234059 17623138860908069769351089)
            ·
              refine ⟨13217354145681052327013317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17623138860908069769351089 13217354145681052327013317)
              ·
                refine ⟨2478253902315197311314997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13217354145681052327013317 2478253902315197311314997)
                ·
                  refine ⟨232336303342049747935781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2478253902315197311314997 232336303342049747935781)
                  ·
                    rfl

theorem cell22_2036130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_2036130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036130 prefixEnd_2036130 := by exact prefixLift 2036130
  have htrace : WordTrace (prefixWord ++ tailWord_2036130) baseStart_2036130 baseEnd_2036130 := by
    simpa [prefixWord, tailWord_2036130, baseEnd_2036130] using wordTrace_append hprefix tailTrace_2036130
  have hstable : (prefixWord ++ tailWord_2036130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036130).length < 2 ^ (prefixWord ++ tailWord_2036130).sum := by decide
  have hdescent : baseEnd_2036130 < baseStart_2036130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036175 : List Nat := [1, 1, 2, 1, 1, 4, 1, 7, 4]
def baseStart_2036175 : Nat := 118140960795 + 2036175 * 2 ^ 59
def prefixEnd_2036175 : Nat := 4983230072969 + 3 ^ 40 * 2036175 * 2
def baseEnd_2036175 : Nat := 232341438148594708810735

theorem tailTrace_2036175 : CollatzResearch.WordTrace tailWord_2036175 prefixEnd_2036175 232341438148594708810735 := by
  unfold tailWord_2036175
  simp only [CollatzResearch.WordTrace]
  refine ⟨74265403398293200849237979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49510268932195467232825319 74265403398293200849237979)
  ·
    refine ⟨111398105097439801273856969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74265403398293200849237979 111398105097439801273856969)
    ·
      refine ⟨83548578823079850955392727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111398105097439801273856969 83548578823079850955392727)
      ·
        refine ⟨125322868234619776433089091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83548578823079850955392727 125322868234619776433089091)
        ·
          refine ⟨187984302351929664649633637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125322868234619776433089091 187984302351929664649633637)
          ·
            refine ⟨35247056690986812121806307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187984302351929664649633637 35247056690986812121806307)
            ·
              refine ⟨52870585036480218182709461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35247056690986812121806307 52870585036480218182709461)
              ·
                refine ⟨1239154336792505113657253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 52870585036480218182709461 1239154336792505113657253)
                ·
                  refine ⟨232341438148594708810735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1239154336792505113657253 232341438148594708810735)
                  ·
                    rfl

theorem cell22_2036175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 4].length) (baseStart_2036175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036175 prefixEnd_2036175 := by exact prefixLift 2036175
  have htrace : WordTrace (prefixWord ++ tailWord_2036175) baseStart_2036175 baseEnd_2036175 := by
    simpa [prefixWord, tailWord_2036175, baseEnd_2036175] using wordTrace_append hprefix tailTrace_2036175
  have hstable : (prefixWord ++ tailWord_2036175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036175).length < 2 ^ (prefixWord ++ tailWord_2036175).sum := by decide
  have hdescent : baseEnd_2036175 < baseStart_2036175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036218 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 1, 9]
def baseStart_2036218 : Nat := 118140960795 + 2036218 * 2 ^ 59
def prefixEnd_2036218 : Nat := 4983230072969 + 3 ^ 40 * 2036218 * 2
def baseEnd_2036218 : Nat := 697039034224546347607073

theorem tailTrace_2036218 : CollatzResearch.WordTrace tailWord_2036218 prefixEnd_2036218 697039034224546347607073 := by
  unfold tailWord_2036218
  simp only [CollatzResearch.WordTrace]
  refine ⟨18566742934284354798263327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49511314491424946128702205 18566742934284354798263327)
  ·
    refine ⟨27850114401426532197394991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18566742934284354798263327 27850114401426532197394991)
    ·
      refine ⟨41775171602139798296092487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27850114401426532197394991 41775171602139798296092487)
      ·
        refine ⟨62662757403209697444138731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41775171602139798296092487 62662757403209697444138731)
        ·
          refine ⟨93994136104814546166208097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62662757403209697444138731 93994136104814546166208097)
          ·
            refine ⟨70495602078610909624656073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93994136104814546166208097 70495602078610909624656073)
            ·
              refine ⟨52871701558958182218492055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70495602078610909624656073 52871701558958182218492055)
              ·
                refine ⟨79307552338437273327738083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52871701558958182218492055 79307552338437273327738083)
                ·
                  refine ⟨118961328507655909991607125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79307552338437273327738083 118961328507655909991607125)
                  ·
                    refine ⟨697039034224546347607073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 118961328507655909991607125 697039034224546347607073)
                    ·
                      rfl

theorem cell22_2036218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_2036218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036218 prefixEnd_2036218 := by exact prefixLift 2036218
  have htrace : WordTrace (prefixWord ++ tailWord_2036218) baseStart_2036218 baseEnd_2036218 := by
    simpa [prefixWord, tailWord_2036218, baseEnd_2036218] using wordTrace_append hprefix tailTrace_2036218
  have hstable : (prefixWord ++ tailWord_2036218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036218).length < 2 ^ (prefixWord ++ tailWord_2036218).sum := by decide
  have hdescent : baseEnd_2036218 < baseStart_2036218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036226 : List Nat := [3, 4, 1, 2, 2, 1, 2, 3, 4]
def baseStart_2036226 : Nat := 118140960795 + 2036226 * 2 ^ 59
def prefixEnd_2036226 : Nat := 4983230072969 + 3 ^ 40 * 2036226 * 2
def baseEnd_2036226 : Nat := 232347257596012331135683

theorem tailTrace_2036226 : CollatzResearch.WordTrace tailWord_2036226 prefixEnd_2036226 232347257596012331135683 := by
  unfold tailWord_2036226
  simp only [CollatzResearch.WordTrace]
  refine ⟨18566815880277109139836133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49511509014072291039563021 18566815880277109139836133)
  ·
    refine ⟨3481277977551957963719275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18566815880277109139836133 3481277977551957963719275)
    ·
      refine ⟨5221916966327936945578913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3481277977551957963719275 5221916966327936945578913)
      ·
        refine ⟨3916437724745952709184185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5221916966327936945578913 3916437724745952709184185)
        ·
          refine ⟨2937328293559464531888139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3916437724745952709184185 2937328293559464531888139)
          ·
            refine ⟨4405992440339196797832209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2937328293559464531888139 4405992440339196797832209)
            ·
              refine ⟨3304494330254397598374157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4405992440339196797832209 3304494330254397598374157)
              ·
                refine ⟨1239185373845399099390309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3304494330254397598374157 1239185373845399099390309)
                ·
                  refine ⟨232347257596012331135683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1239185373845399099390309 232347257596012331135683)
                  ·
                    rfl

theorem cell22_2036226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_2036226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036226 prefixEnd_2036226 := by exact prefixLift 2036226
  have htrace : WordTrace (prefixWord ++ tailWord_2036226) baseStart_2036226 baseEnd_2036226 := by
    simpa [prefixWord, tailWord_2036226, baseEnd_2036226] using wordTrace_append hprefix tailTrace_2036226
  have hstable : (prefixWord ++ tailWord_2036226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036226).length < 2 ^ (prefixWord ++ tailWord_2036226).sum := by decide
  have hdescent : baseEnd_2036226 < baseStart_2036226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036233 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 1, 8]
def baseStart_2036233 : Nat := 118140960795 + 2036233 * 2 ^ 59
def prefixEnd_2036233 : Nat := 4983230072969 + 3 ^ 40 * 2036233 * 2
def baseEnd_2036233 : Nat := 697044169031091308482027

theorem tailTrace_2036233 : CollatzResearch.WordTrace tailWord_2036233 prefixEnd_2036233 697044169031091308482027 := by
  unfold tailWord_2036233
  simp only [CollatzResearch.WordTrace]
  refine ⟨74267518832083076754849353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49511679221388717836566235 74267518832083076754849353)
  ·
    refine ⟨55700639124062307566137015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74267518832083076754849353 55700639124062307566137015)
    ·
      refine ⟨83550958686093461349205523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55700639124062307566137015 83550958686093461349205523)
      ·
        refine ⟨125326438029140192023808285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83550958686093461349205523 125326438029140192023808285)
        ·
          refine ⟨46997414260927572008928107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125326438029140192023808285 46997414260927572008928107)
          ·
            refine ⟨70496121391391358013392161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46997414260927572008928107 70496121391391358013392161)
            ·
              refine ⟨52872091043543518510044121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70496121391391358013392161 52872091043543518510044121)
              ·
                refine ⟨39654068282657638882533091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52872091043543518510044121 39654068282657638882533091)
                ·
                  refine ⟨59481102423986458323799637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39654068282657638882533091 59481102423986458323799637)
                  ·
                    refine ⟨697044169031091308482027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59481102423986458323799637 697044169031091308482027)
                    ·
                      rfl

theorem cell22_2036233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_2036233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036233 prefixEnd_2036233 := by exact prefixLift 2036233
  have htrace : WordTrace (prefixWord ++ tailWord_2036233) baseStart_2036233 baseEnd_2036233 := by
    simpa [prefixWord, tailWord_2036233, baseEnd_2036233] using wordTrace_append hprefix tailTrace_2036233
  have hstable : (prefixWord ++ tailWord_2036233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036233).length < 2 ^ (prefixWord ++ tailWord_2036233).sum := by decide
  have hdescent : baseEnd_2036233 < baseStart_2036233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036252 : List Nat := [2, 2, 3, 1, 2, 2, 1, 3, 3, 3]
def baseStart_2036252 : Nat := 118140960795 + 2036252 * 2 ^ 59
def prefixEnd_2036252 : Nat := 4983230072969 + 3 ^ 40 * 2036252 * 2
def baseEnd_2036252 : Nat := 697050673119381592256969

theorem tailTrace_2036252 : CollatzResearch.WordTrace tailWord_2036252 prefixEnd_2036252 697050673119381592256969 := by
  unfold tailWord_2036252
  simp only [CollatzResearch.WordTrace]
  refine ⟨37134105909507121499895505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49512141212676161999860673 37134105909507121499895505)
  ·
    refine ⟨27850579432130341124921629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37134105909507121499895505 27850579432130341124921629)
    ·
      refine ⟨10443967287048877921845611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27850579432130341124921629 10443967287048877921845611)
      ·
        refine ⟨15665950930573316882768417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10443967287048877921845611 15665950930573316882768417)
        ·
          refine ⟨11749463197929987662076313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15665950930573316882768417 11749463197929987662076313)
          ·
            refine ⟨8812097398447490746557235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11749463197929987662076313 8812097398447490746557235)
            ·
              refine ⟨13218146097671236119835853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8812097398447490746557235 13218146097671236119835853)
              ·
                refine ⟨4956804786626713544938445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13218146097671236119835853 4956804786626713544938445)
                ·
                  refine ⟨1858801794985017579351917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4956804786626713544938445 1858801794985017579351917)
                  ·
                    refine ⟨697050673119381592256969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1858801794985017579351917 697050673119381592256969)
                    ·
                      rfl

theorem cell22_2036252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_2036252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036252 prefixEnd_2036252 := by exact prefixLift 2036252
  have htrace : WordTrace (prefixWord ++ tailWord_2036252) baseStart_2036252 baseEnd_2036252 := by
    simpa [prefixWord, tailWord_2036252, baseEnd_2036252] using wordTrace_append hprefix tailTrace_2036252
  have hstable : (prefixWord ++ tailWord_2036252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036252).length < 2 ^ (prefixWord ++ tailWord_2036252).sum := by decide
  have hdescent : baseEnd_2036252 < baseStart_2036252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036316 : List Nat := [2, 2, 4, 1, 3, 2, 2, 1, 5]
def baseStart_2036316 : Nat := 118140960795 + 2036316 * 2 ^ 59
def prefixEnd_2036316 : Nat := 4983230072969 + 3 ^ 40 * 2036316 * 2
def baseEnd_2036316 : Nat := 232357527209102252885591

theorem tailTrace_2036316 : CollatzResearch.WordTrace tailWord_2036316 prefixEnd_2036316 232357527209102252885591 := by
  unfold tailWord_2036316
  simp only [CollatzResearch.WordTrace]
  refine ⟨37135273045391190965060401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49513697393854921286747201 37135273045391190965060401)
  ·
    refine ⟨27851454784043393223795301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37135273045391190965060401 27851454784043393223795301)
    ·
      refine ⟨5222147772008136229461619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27851454784043393223795301 5222147772008136229461619)
      ·
        refine ⟨7833221658012204344192429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5222147772008136229461619 7833221658012204344192429)
        ·
          refine ⟨2937458121754576629072161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7833221658012204344192429 2937458121754576629072161)
          ·
            refine ⟨2203093591315932471804121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2937458121754576629072161 2203093591315932471804121)
            ·
              refine ⟨1652320193486949353853091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2203093591315932471804121 1652320193486949353853091)
              ·
                refine ⟨2478480290230424030779637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1652320193486949353853091 2478480290230424030779637)
                ·
                  refine ⟨232357527209102252885591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2478480290230424030779637 232357527209102252885591)
                  ·
                    rfl

theorem cell22_2036316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_2036316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036316 prefixEnd_2036316 := by exact prefixLift 2036316
  have htrace : WordTrace (prefixWord ++ tailWord_2036316) baseStart_2036316 baseEnd_2036316 := by
    simpa [prefixWord, tailWord_2036316, baseEnd_2036316] using wordTrace_append hprefix tailTrace_2036316
  have hstable : (prefixWord ++ tailWord_2036316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036316).length < 2 ^ (prefixWord ++ tailWord_2036316).sum := by decide
  have hdescent : baseEnd_2036316 < baseStart_2036316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036354 : List Nat := [3, 4, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_2036354 : Nat := 118140960795 + 2036354 * 2 ^ 59
def prefixEnd_2036354 : Nat := 4983230072969 + 3 ^ 40 * 2036354 * 2
def baseEnd_2036354 : Nat := 697085589803887326206657

theorem tailTrace_2036354 : CollatzResearch.WordTrace tailWord_2036354 prefixEnd_2036354 697085589803887326206657 := by
  unfold tailWord_2036354
  simp only [CollatzResearch.WordTrace]
  refine ⟨18567983016161178605001029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49514621376429809613336077 18567983016161178605001029)
  ·
    refine ⟨3481496815530220988437693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18567983016161178605001029 3481496815530220988437693)
    ·
      refine ⟨1305561305823832870664135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3481496815530220988437693 1305561305823832870664135)
      ·
        refine ⟨1958341958735749305996203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1305561305823832870664135 1958341958735749305996203)
        ·
          refine ⟨2937512938103623958994305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1958341958735749305996203 2937512938103623958994305)
          ·
            refine ⟨2203134703577717969245729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2937512938103623958994305 2203134703577717969245729)
            ·
              refine ⟨1652351027683288476934297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2203134703577717969245729 1652351027683288476934297)
              ·
                refine ⟨1239263270762466357700723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1652351027683288476934297 1239263270762466357700723)
                ·
                  refine ⟨1858894906143699536551085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239263270762466357700723 1858894906143699536551085)
                  ·
                    refine ⟨697085589803887326206657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1858894906143699536551085 697085589803887326206657)
                    ·
                      rfl

theorem cell22_2036354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_2036354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036354 prefixEnd_2036354 := by exact prefixLift 2036354
  have htrace : WordTrace (prefixWord ++ tailWord_2036354) baseStart_2036354 baseEnd_2036354 := by
    simpa [prefixWord, tailWord_2036354, baseEnd_2036354] using wordTrace_append hprefix tailTrace_2036354
  have hstable : (prefixWord ++ tailWord_2036354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036354).length < 2 ^ (prefixWord ++ tailWord_2036354).sum := by decide
  have hdescent : baseEnd_2036354 < baseStart_2036354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036357 : List Nat := [1, 3, 1, 1, 4, 2, 2, 2, 2, 4]
def baseStart_2036357 : Nat := 118140960795 + 2036357 * 2 ^ 59
def prefixEnd_2036357 : Nat := 4983230072969 + 3 ^ 40 * 2036357 * 2
def baseEnd_2036357 : Nat := 697086616765196318381647

theorem tailTrace_2036357 : CollatzResearch.WordTrace tailWord_2036357 prefixEnd_2036357 697086616765196318381647 := by
  unfold tailWord_2036357
  simp only [CollatzResearch.WordTrace]
  refine ⟨74272041483633845932363325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49514694322422563954908883 74272041483633845932363325)
  ·
    refine ⟨27852015556362692224636247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74272041483633845932363325 27852015556362692224636247)
    ·
      refine ⟨41778023334544038336954371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27852015556362692224636247 41778023334544038336954371)
      ·
        refine ⟨62667035001816057505431557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41778023334544038336954371 62667035001816057505431557)
        ·
          refine ⟨11750069062840510782268417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62667035001816057505431557 11750069062840510782268417)
          ·
            refine ⟨8812551797130383086701313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11750069062840510782268417 8812551797130383086701313)
            ·
              refine ⟨6609413847847787315025985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8812551797130383086701313 6609413847847787315025985)
              ·
                refine ⟨4957060385885840486269489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6609413847847787315025985 4957060385885840486269489)
                ·
                  refine ⟨3717795289414380364702117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4957060385885840486269489 3717795289414380364702117)
                  ·
                    refine ⟨697086616765196318381647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3717795289414380364702117 697086616765196318381647)
                    ·
                      rfl

theorem cell22_2036357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_2036357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036357 prefixEnd_2036357 := by exact prefixLift 2036357
  have htrace : WordTrace (prefixWord ++ tailWord_2036357) baseStart_2036357 baseEnd_2036357 := by
    simpa [prefixWord, tailWord_2036357, baseEnd_2036357] using wordTrace_append hprefix tailTrace_2036357
  have hstable : (prefixWord ++ tailWord_2036357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036357).length < 2 ^ (prefixWord ++ tailWord_2036357).sum := by decide
  have hdescent : baseEnd_2036357 < baseStart_2036357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036359 : List Nat := [1, 1, 4, 2, 1, 2, 4, 2, 2, 3]
def baseStart_2036359 : Nat := 118140960795 + 2036359 * 2 ^ 59
def prefixEnd_2036359 : Nat := 4983230072969 + 3 ^ 40 * 2036359 * 2
def baseEnd_2036359 : Nat := 697087301406068979831641

theorem tailTrace_2036359 : CollatzResearch.WordTrace tailWord_2036359 prefixEnd_2036359 697087301406068979831641 := by
  unfold tailWord_2036359
  simp only [CollatzResearch.WordTrace]
  refine ⟨74272114429626600273936131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49514742953084400182624087 74272114429626600273936131)
  ·
    refine ⟨111408171644439900410904197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74272114429626600273936131 111408171644439900410904197)
    ·
      refine ⟨20889032183332481327044537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111408171644439900410904197 20889032183332481327044537)
      ·
        refine ⟨15666774137499360995283403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20889032183332481327044537 15666774137499360995283403)
        ·
          refine ⟨23500161206249041492925105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15666774137499360995283403 23500161206249041492925105)
          ·
            refine ⟨17625120904686781119693829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23500161206249041492925105 17625120904686781119693829)
            ·
              refine ⟨3304710169628771459942593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17625120904686781119693829 3304710169628771459942593)
              ·
                refine ⟨2478532627221578594956945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3304710169628771459942593 2478532627221578594956945)
                ·
                  refine ⟨1858899470416183946217709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2478532627221578594956945 1858899470416183946217709)
                  ·
                    refine ⟨697087301406068979831641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1858899470416183946217709 697087301406068979831641)
                    ·
                      rfl

theorem cell22_2036359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_2036359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036359 prefixEnd_2036359 := by exact prefixLift 2036359
  have htrace : WordTrace (prefixWord ++ tailWord_2036359) baseStart_2036359 baseEnd_2036359 := by
    simpa [prefixWord, tailWord_2036359, baseEnd_2036359] using wordTrace_append hprefix tailTrace_2036359
  have hstable : (prefixWord ++ tailWord_2036359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036359).length < 2 ^ (prefixWord ++ tailWord_2036359).sum := by decide
  have hdescent : baseEnd_2036359 < baseStart_2036359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036400 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 7]
def baseStart_2036400 : Nat := 118140960795 + 2036400 * 2 ^ 59
def prefixEnd_2036400 : Nat := 4983230072969 + 3 ^ 40 * 2036400 * 2
def baseEnd_2036400 : Nat := 232367112181319513185505

theorem tailTrace_2036400 : CollatzResearch.WordTrace tailWord_2036400 prefixEnd_2036400 232367112181319513185505 := by
  unfold tailWord_2036400
  simp only [CollatzResearch.WordTrace]
  refine ⟨37136804911239032138089327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49515739881652042850785769 37136804911239032138089327)
  ·
    refine ⟨55705207366858548207133991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37136804911239032138089327 55705207366858548207133991)
    ·
      refine ⟨83557811050287822310700987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55705207366858548207133991 83557811050287822310700987)
      ·
        refine ⟨125336716575431733466051481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83557811050287822310700987 125336716575431733466051481)
        ·
          refine ⟨94002537431573800099538611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125336716575431733466051481 94002537431573800099538611)
          ·
            refine ⟨141003806147360700149307917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94002537431573800099538611 141003806147360700149307917)
            ·
              refine ⟨52876427305260262555990469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141003806147360700149307917 52876427305260262555990469)
              ·
                refine ⟨9914330119736299229248213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52876427305260262555990469 9914330119736299229248213)
                ·
                  refine ⟨232367112181319513185505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9914330119736299229248213 232367112181319513185505)
                  ·
                    rfl

theorem cell22_2036400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 7].length) (baseStart_2036400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036400 prefixEnd_2036400 := by exact prefixLift 2036400
  have htrace : WordTrace (prefixWord ++ tailWord_2036400) baseStart_2036400 baseEnd_2036400 := by
    simpa [prefixWord, tailWord_2036400, baseEnd_2036400] using wordTrace_append hprefix tailTrace_2036400
  have hstable : (prefixWord ++ tailWord_2036400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036400).length < 2 ^ (prefixWord ++ tailWord_2036400).sum := by decide
  have hdescent : baseEnd_2036400 < baseStart_2036400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036492 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 6, 4]
def baseStart_2036492 : Nat := 118140960795 + 2036492 * 2 ^ 59
def prefixEnd_2036492 : Nat := 4983230072969 + 3 ^ 40 * 2036492 * 2
def baseEnd_2036492 : Nat := 697132830024100966256233

theorem tailTrace_2036492 : CollatzResearch.WordTrace tailWord_2036492 prefixEnd_2036492 697132830024100966256233 := by
  unfold tailWord_2036492
  simp only [CollatzResearch.WordTrace]
  refine ⟨37138482669072381994263865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49517976892096509325685153 37138482669072381994263865)
  ·
    refine ⟨27853862001804286495697899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37138482669072381994263865 27853862001804286495697899)
    ·
      refine ⟨41780793002706429743546849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27853862001804286495697899 41780793002706429743546849)
      ·
        refine ⟨31335594752029822307660137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41780793002706429743546849 31335594752029822307660137)
        ·
          refine ⟨23501696064022366730745103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31335594752029822307660137 23501696064022366730745103)
          ·
            refine ⟨35252544096033550096117655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23501696064022366730745103 35252544096033550096117655)
            ·
              refine ⟨52878816144050325144176483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35252544096033550096117655 52878816144050325144176483)
              ·
                refine ⟨79318224216075487716264725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52878816144050325144176483 79318224216075487716264725)
                ·
                  refine ⟨3718041760128538486699909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79318224216075487716264725 3718041760128538486699909)
                  ·
                    refine ⟨697132830024100966256233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3718041760128538486699909 697132830024100966256233)
                    ·
                      rfl

theorem cell22_2036492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_2036492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036492 prefixEnd_2036492 := by exact prefixLift 2036492
  have htrace : WordTrace (prefixWord ++ tailWord_2036492) baseStart_2036492 baseEnd_2036492 := by
    simpa [prefixWord, tailWord_2036492, baseEnd_2036492] using wordTrace_append hprefix tailTrace_2036492
  have hstable : (prefixWord ++ tailWord_2036492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036492).length < 2 ^ (prefixWord ++ tailWord_2036492).sum := by decide
  have hdescent : baseEnd_2036492 < baseStart_2036492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036526 : List Nat := [4, 1, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_2036526 : Nat := 118140960795 + 2036526 * 2 ^ 59
def prefixEnd_2036526 : Nat := 4983230072969 + 3 ^ 40 * 2036526 * 2
def baseEnd_2036526 : Nat := 697144468918936210906129

theorem tailTrace_2036526 : CollatzResearch.WordTrace tailWord_2036526 prefixEnd_2036526 697144468918936210906129 := by
  unfold tailWord_2036526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9284775677502698474408179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49518803613347725196843621 9284775677502698474408179)
  ·
    refine ⟨13927163516254047711612269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9284775677502698474408179 13927163516254047711612269)
    ·
      refine ⟨5222686318595267891854601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13927163516254047711612269 5222686318595267891854601)
      ·
        refine ⟨3917014738946450918890951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5222686318595267891854601 3917014738946450918890951)
        ·
          refine ⟨5875522108419676378336427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3917014738946450918890951 5875522108419676378336427)
          ·
            refine ⟨8813283162629514567504641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5875522108419676378336427 8813283162629514567504641)
            ·
              refine ⟨6609962371972135925628481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8813283162629514567504641 6609962371972135925628481)
              ·
                refine ⟨4957471778979101944221361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6609962371972135925628481 4957471778979101944221361)
                ·
                  refine ⟨3718103834234326458166021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4957471778979101944221361 3718103834234326458166021)
                  ·
                    refine ⟨697144468918936210906129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3718103834234326458166021 697144468918936210906129)
                    ·
                      rfl

theorem cell22_2036526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_2036526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036526 prefixEnd_2036526 := by exact prefixLift 2036526
  have htrace : WordTrace (prefixWord ++ tailWord_2036526) baseStart_2036526 baseEnd_2036526 := by
    simpa [prefixWord, tailWord_2036526, baseEnd_2036526] using wordTrace_append hprefix tailTrace_2036526
  have hstable : (prefixWord ++ tailWord_2036526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036526).length < 2 ^ (prefixWord ++ tailWord_2036526).sum := by decide
  have hdescent : baseEnd_2036526 < baseStart_2036526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036541 : List Nat := [1, 4, 1, 4, 2, 2, 1, 7]
def baseStart_2036541 : Nat := 118140960795 + 2036541 * 2 ^ 59
def prefixEnd_2036541 : Nat := 4983230072969 + 3 ^ 40 * 2036541 * 2
def baseEnd_2036541 : Nat := 77461067080609019086787

theorem tailTrace_2036541 : CollatzResearch.WordTrace tailWord_2036541 prefixEnd_2036541 77461067080609019086787 := by
  unfold tailWord_2036541
  simp only [CollatzResearch.WordTrace]
  refine ⟨74278752514967245357061477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49519168343311496904707651 74278752514967245357061477)
  ·
    refine ⟨13927266096556358504449027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74278752514967245357061477 13927266096556358504449027)
    ·
      refine ⟨20890899144834537756673541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13927266096556358504449027 20890899144834537756673541)
      ·
        refine ⟨3917043589656475829376289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20890899144834537756673541 3917043589656475829376289)
        ·
          refine ⟨2937782692242356872032217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3917043589656475829376289 2937782692242356872032217)
          ·
            refine ⟨2203337019181767654024163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2937782692242356872032217 2203337019181767654024163)
            ·
              refine ⟨3305005528772651481036245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2203337019181767654024163 3305005528772651481036245)
              ·
                refine ⟨77461067080609019086787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3305005528772651481036245 77461067080609019086787)
                ·
                  rfl

theorem cell22_2036541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 7].length) (baseStart_2036541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036541 prefixEnd_2036541 := by exact prefixLift 2036541
  have htrace : WordTrace (prefixWord ++ tailWord_2036541) baseStart_2036541 baseEnd_2036541 := by
    simpa [prefixWord, tailWord_2036541, baseEnd_2036541] using wordTrace_append hprefix tailTrace_2036541
  have hstable : (prefixWord ++ tailWord_2036541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036541).length < 2 ^ (prefixWord ++ tailWord_2036541).sum := by decide
  have hdescent : baseEnd_2036541 < baseStart_2036541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036556 : List Nat := [2, 2, 1, 3, 3, 2, 1, 2, 3, 3]
def baseStart_2036556 : Nat := 118140960795 + 2036556 * 2 ^ 59
def prefixEnd_2036556 : Nat := 4983230072969 + 3 ^ 40 * 2036556 * 2
def baseEnd_2036556 : Nat := 697154738532026132656037

theorem tailTrace_2036556 : CollatzResearch.WordTrace tailWord_2036556 prefixEnd_2036556 697154738532026132656037 := by
  unfold tailWord_2036556
  simp only [CollatzResearch.WordTrace]
  refine ⟨37139649804956451459428761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49519533073275268612571681 37139649804956451459428761)
  ·
    refine ⟨27854737353717338594571571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37139649804956451459428761 27854737353717338594571571)
    ·
      refine ⟨41782106030576007891857357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27854737353717338594571571 41782106030576007891857357)
      ·
        refine ⟨15668289761466002959446509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41782106030576007891857357 15668289761466002959446509)
        ·
          refine ⟨5875608660549751109792441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15668289761466002959446509 5875608660549751109792441)
          ·
            refine ⟨4406706495412313332344331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5875608660549751109792441 4406706495412313332344331)
            ·
              refine ⟨6610059743118469998516497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4406706495412313332344331 6610059743118469998516497)
              ·
                refine ⟨4957544807338852498887373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6610059743118469998516497 4957544807338852498887373)
                ·
                  refine ⟨1859079302752069687082765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4957544807338852498887373 1859079302752069687082765)
                  ·
                    refine ⟨697154738532026132656037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1859079302752069687082765 697154738532026132656037)
                    ·
                      rfl

theorem cell22_2036556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_2036556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036556 prefixEnd_2036556 := by exact prefixLift 2036556
  have htrace : WordTrace (prefixWord ++ tailWord_2036556) baseStart_2036556 baseEnd_2036556 := by
    simpa [prefixWord, tailWord_2036556, baseEnd_2036556] using wordTrace_append hprefix tailTrace_2036556
  have hstable : (prefixWord ++ tailWord_2036556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036556).length < 2 ^ (prefixWord ++ tailWord_2036556).sum := by decide
  have hdescent : baseEnd_2036556 < baseStart_2036556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036584 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 2, 5]
def baseStart_2036584 : Nat := 118140960795 + 2036584 * 2 ^ 59
def prefixEnd_2036584 : Nat := 4983230072969 + 3 ^ 40 * 2036584 * 2
def baseEnd_2036584 : Nat := 697164323504243392955951

theorem tailTrace_2036584 : CollatzResearch.WordTrace tailWord_2036584 prefixEnd_2036584 697164323504243392955951 := by
  unfold tailWord_2036584
  simp only [CollatzResearch.WordTrace]
  refine ⟨37140160426905731850438403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49520213902540975800584537 37140160426905731850438403)
  ·
    refine ⟨55710240640358597775657605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37140160426905731850438403 55710240640358597775657605)
    ·
      refine ⟨10445670120067237082935801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55710240640358597775657605 10445670120067237082935801)
      ·
        refine ⟨7834252590050427812201851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10445670120067237082935801 7834252590050427812201851)
        ·
          refine ⟨11751378885075641718302777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7834252590050427812201851 11751378885075641718302777)
          ·
            refine ⟨8813534163806731288727083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11751378885075641718302777 8813534163806731288727083)
            ·
              refine ⟨13220301245710096933090625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8813534163806731288727083 13220301245710096933090625)
              ·
                refine ⟨9915225934282572699817969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13220301245710096933090625 9915225934282572699817969)
                ·
                  refine ⟨7436419450711929524863477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9915225934282572699817969 7436419450711929524863477)
                  ·
                    refine ⟨697164323504243392955951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7436419450711929524863477 697164323504243392955951)
                    ·
                      rfl

theorem cell22_2036584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_2036584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036584 prefixEnd_2036584 := by exact prefixLift 2036584
  have htrace : WordTrace (prefixWord ++ tailWord_2036584) baseStart_2036584 baseEnd_2036584 := by
    simpa [prefixWord, tailWord_2036584, baseEnd_2036584] using wordTrace_append hprefix tailTrace_2036584
  have hstable : (prefixWord ++ tailWord_2036584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036584).length < 2 ^ (prefixWord ++ tailWord_2036584).sum := by decide
  have hdescent : baseEnd_2036584 < baseStart_2036584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036616 : List Nat := [2, 1, 3, 3, 2, 1, 1, 4, 1, 4]
def baseStart_2036616 : Nat := 118140960795 + 2036616 * 2 ^ 59
def prefixEnd_2036616 : Nat := 4983230072969 + 3 ^ 40 * 2036616 * 2
def baseEnd_2036616 : Nat := 697175277758205976155853

theorem tailTrace_2036616 : CollatzResearch.WordTrace tailWord_2036616 prefixEnd_2036616 697175277758205976155853 := by
  unfold tailWord_2036616
  simp only [CollatzResearch.WordTrace]
  refine ⟨37140743994847766583020851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49520991993130355444027801 37140743994847766583020851)
  ·
    refine ⟨55711115992271649874531277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37140743994847766583020851 55711115992271649874531277)
    ·
      refine ⟨20891668497101868702949229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55711115992271649874531277 20891668497101868702949229)
      ·
        refine ⟨7834375686413200763605961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20891668497101868702949229 7834375686413200763605961)
        ·
          refine ⟨5875781764809900572704471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7834375686413200763605961 5875781764809900572704471)
          ·
            refine ⟨8813672647214850859056707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5875781764809900572704471 8813672647214850859056707)
            ·
              refine ⟨13220508970822276288585061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8813672647214850859056707 13220508970822276288585061)
              ·
                refine ⟨2478845432029176804109699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13220508970822276288585061 2478845432029176804109699)
                ·
                  refine ⟨3718268148043765206164549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2478845432029176804109699 3718268148043765206164549)
                  ·
                    refine ⟨697175277758205976155853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3718268148043765206164549 697175277758205976155853)
                    ·
                      rfl

theorem cell22_2036616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_2036616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036616 prefixEnd_2036616 := by exact prefixLift 2036616
  have htrace : WordTrace (prefixWord ++ tailWord_2036616) baseStart_2036616 baseEnd_2036616 := by
    simpa [prefixWord, tailWord_2036616, baseEnd_2036616] using wordTrace_append hprefix tailTrace_2036616
  have hstable : (prefixWord ++ tailWord_2036616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036616).length < 2 ^ (prefixWord ++ tailWord_2036616).sum := by decide
  have hdescent : baseEnd_2036616 < baseStart_2036616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036663 : List Nat := [1, 1, 3, 1, 3, 1, 6, 1, 2, 3]
def baseStart_2036663 : Nat := 118140960795 + 2036663 * 2 ^ 59
def prefixEnd_2036663 : Nat := 4983230072969 + 3 ^ 40 * 2036663 * 2
def baseEnd_2036663 : Nat := 697191366818713520230709

theorem tailTrace_2036663 : CollatzResearch.WordTrace tailWord_2036663 prefixEnd_2036663 697191366818713520230709 := by
  unfold tailWord_2036663
  simp only [CollatzResearch.WordTrace]
  refine ⟨74283202220525260193002643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49522134813683506795335095 74283202220525260193002643)
  ·
    refine ⟨111424803330787890289503965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74283202220525260193002643 111424803330787890289503965)
    ·
      refine ⟨41784301249045458858563987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111424803330787890289503965 41784301249045458858563987)
      ·
        refine ⟨62676451873568188287845981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41784301249045458858563987 62676451873568188287845981)
        ·
          refine ⟨23503669452588070607942243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62676451873568188287845981 23503669452588070607942243)
          ·
            refine ⟨35255504178882105911913365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23503669452588070607942243 35255504178882105911913365)
            ·
              refine ⟨1652601758385098714620939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35255504178882105911913365 1652601758385098714620939)
              ·
                refine ⟨2478902637577648071931409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1652601758385098714620939 2478902637577648071931409)
                ·
                  refine ⟨1859176978183236053948557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2478902637577648071931409 1859176978183236053948557)
                  ·
                    refine ⟨697191366818713520230709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1859176978183236053948557 697191366818713520230709)
                    ·
                      rfl

theorem cell22_2036663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 2, 3].length) (baseStart_2036663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036663 prefixEnd_2036663 := by exact prefixLift 2036663
  have htrace : WordTrace (prefixWord ++ tailWord_2036663) baseStart_2036663 baseEnd_2036663 := by
    simpa [prefixWord, tailWord_2036663, baseEnd_2036663] using wordTrace_append hprefix tailTrace_2036663
  have hstable : (prefixWord ++ tailWord_2036663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036663).length < 2 ^ (prefixWord ++ tailWord_2036663).sum := by decide
  have hdescent : baseEnd_2036663 < baseStart_2036663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036719 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 1, 7]
def baseStart_2036719 : Nat := 118140960795 + 2036719 * 2 ^ 59
def prefixEnd_2036719 : Nat := 4983230072969 + 3 ^ 40 * 2036719 * 2
def baseEnd_2036719 : Nat := 697210536763148040830537

theorem tailTrace_2036719 : CollatzResearch.WordTrace tailWord_2036719 prefixEnd_2036719 697210536763148040830537 := by
  unfold tailWord_2036719
  simp only [CollatzResearch.WordTrace]
  refine ⟨74285244708322381757041211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49523496472214921171360807 74285244708322381757041211)
  ·
    refine ⟨111427867062483572635561817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74285244708322381757041211 111427867062483572635561817)
    ·
      refine ⟨83570900296862679476671363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111427867062483572635561817 83570900296862679476671363)
      ·
        refine ⟨125356350445294019215007045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83570900296862679476671363 125356350445294019215007045)
        ·
          refine ⟨23504315708492628602813821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125356350445294019215007045 23504315708492628602813821)
          ·
            refine ⟨8814118390684735726055183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23504315708492628602813821 8814118390684735726055183)
            ·
              refine ⟨13221177586027103589082775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8814118390684735726055183 13221177586027103589082775)
              ·
                refine ⟨19831766379040655383624163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13221177586027103589082775 19831766379040655383624163)
                ·
                  refine ⟨29747649568560983075436245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19831766379040655383624163 29747649568560983075436245)
                  ·
                    refine ⟨697210536763148040830537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29747649568560983075436245 697210536763148040830537)
                    ·
                      rfl

theorem cell22_2036719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_2036719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036719 prefixEnd_2036719 := by exact prefixLift 2036719
  have htrace : WordTrace (prefixWord ++ tailWord_2036719) baseStart_2036719 baseEnd_2036719 := by
    simpa [prefixWord, tailWord_2036719, baseEnd_2036719] using wordTrace_append hprefix tailTrace_2036719
  have hstable : (prefixWord ++ tailWord_2036719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036719).length < 2 ^ (prefixWord ++ tailWord_2036719).sum := by decide
  have hdescent : baseEnd_2036719 < baseStart_2036719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036721 : List Nat := [1, 2, 2, 2, 4, 1, 2, 3, 5]
def baseStart_2036721 : Nat := 118140960795 + 2036721 * 2 ^ 59
def prefixEnd_2036721 : Nat := 4983230072969 + 3 ^ 40 * 2036721 * 2
def baseEnd_2036721 : Nat := 232403740468006900760177

theorem tailTrace_2036721 : CollatzResearch.WordTrace tailWord_2036721 prefixEnd_2036721 232403740468006900760177 := by
  unfold tailWord_2036721
  simp only [CollatzResearch.WordTrace]
  refine ⟨74285317654315136098614017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49523545102876757399076011 74285317654315136098614017)
  ·
    refine ⟨55713988240736352073960513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74285317654315136098614017 55713988240736352073960513)
    ·
      refine ⟨41785491180552264055470385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55713988240736352073960513 41785491180552264055470385)
      ·
        refine ⟨31339118385414198041602789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41785491180552264055470385 31339118385414198041602789)
        ·
          refine ⟨5876084697265162132800523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31339118385414198041602789 5876084697265162132800523)
          ·
            refine ⟨8814127045897743199200785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5876084697265162132800523 8814127045897743199200785)
            ·
              refine ⟨6610595284423307399400589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8814127045897743199200785 6610595284423307399400589)
              ·
                refine ⟨2478973231658740274775221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6610595284423307399400589 2478973231658740274775221)
                ·
                  refine ⟨232403740468006900760177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2478973231658740274775221 232403740468006900760177)
                  ·
                    rfl

theorem cell22_2036721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 5].length) (baseStart_2036721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036721 prefixEnd_2036721 := by exact prefixLift 2036721
  have htrace : WordTrace (prefixWord ++ tailWord_2036721) baseStart_2036721 baseEnd_2036721 := by
    simpa [prefixWord, tailWord_2036721, baseEnd_2036721] using wordTrace_append hprefix tailTrace_2036721
  have hstable : (prefixWord ++ tailWord_2036721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036721).length < 2 ^ (prefixWord ++ tailWord_2036721).sum := by decide
  have hdescent : baseEnd_2036721 < baseStart_2036721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036779 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 3, 6]
def baseStart_2036779 : Nat := 118140960795 + 2036779 * 2 ^ 59
def prefixEnd_2036779 : Nat := 4983230072969 + 3 ^ 40 * 2036779 * 2
def baseEnd_2036779 : Nat := 697231075989327884330353

theorem tailTrace_2036779 : CollatzResearch.WordTrace tailWord_2036779 prefixEnd_2036779 697231075989327884330353 := by
  unfold tailWord_2036779
  simp only [CollatzResearch.WordTrace]
  refine ⟨74287433088105012004225391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49524955392070008002816927 74287433088105012004225391)
  ·
    refine ⟨111431149632157518006338087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74287433088105012004225391 111431149632157518006338087)
    ·
      refine ⟨167146724448236277009507131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111431149632157518006338087 167146724448236277009507131)
      ·
        refine ⟨250720086672354415514260697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167146724448236277009507131 250720086672354415514260697)
        ·
          refine ⟨188040065004265811635695523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250720086672354415514260697 188040065004265811635695523)
          ·
            refine ⟨282060097506398717453543285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188040065004265811635695523 282060097506398717453543285)
            ·
              refine ⟨26443134141224879761269683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 282060097506398717453543285 26443134141224879761269683)
              ·
                refine ⟨39664701211837319641904525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26443134141224879761269683 39664701211837319641904525)
                ·
                  refine ⟨14874262954438994865714197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39664701211837319641904525 14874262954438994865714197)
                  ·
                    refine ⟨697231075989327884330353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14874262954438994865714197 697231075989327884330353)
                    ·
                      rfl

theorem cell22_2036779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 6].length) (baseStart_2036779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036779 prefixEnd_2036779 := by exact prefixLift 2036779
  have htrace : WordTrace (prefixWord ++ tailWord_2036779) baseStart_2036779 baseEnd_2036779 := by
    simpa [prefixWord, tailWord_2036779, baseEnd_2036779] using wordTrace_append hprefix tailTrace_2036779
  have hstable : (prefixWord ++ tailWord_2036779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036779).length < 2 ^ (prefixWord ++ tailWord_2036779).sum := by decide
  have hdescent : baseEnd_2036779 < baseStart_2036779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036796 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 1, 6]
def baseStart_2036796 : Nat := 118140960795 + 2036796 * 2 ^ 59
def prefixEnd_2036796 : Nat := 4983230072969 + 3 ^ 40 * 2036796 * 2
def baseEnd_2036796 : Nat := 697236895436745506655301

theorem tailTrace_2036796 : CollatzResearch.WordTrace tailWord_2036796 prefixEnd_2036796 697236895436745506655301 := by
  unfold tailWord_2036796
  simp only [CollatzResearch.WordTrace]
  refine ⟨37144026564521711953797121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49525368752695615938396161 37144026564521711953797121)
  ·
    refine ⟨27858019923391283965347841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37144026564521711953797121 27858019923391283965347841)
    ·
      refine ⟨20893514942543462974010881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27858019923391283965347841 20893514942543462974010881)
      ·
        refine ⟨15670136206907597230508161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20893514942543462974010881 15670136206907597230508161)
        ·
          refine ⟨11752602155180697922881121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15670136206907597230508161 11752602155180697922881121)
          ·
            refine ⟨8814451616385523442160841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11752602155180697922881121 8814451616385523442160841)
            ·
              refine ⟨6610838712289142581620631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8814451616385523442160841 6610838712289142581620631)
              ·
                refine ⟨9916258068433713872430947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6610838712289142581620631 9916258068433713872430947)
                ·
                  refine ⟨14874387102650570808646421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9916258068433713872430947 14874387102650570808646421)
                  ·
                    refine ⟨697236895436745506655301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14874387102650570808646421 697236895436745506655301)
                    ·
                      rfl

theorem cell22_2036796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_2036796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036796 prefixEnd_2036796 := by exact prefixLift 2036796
  have htrace : WordTrace (prefixWord ++ tailWord_2036796) baseStart_2036796 baseEnd_2036796 := by
    simpa [prefixWord, tailWord_2036796, baseEnd_2036796] using wordTrace_append hprefix tailTrace_2036796
  have hstable : (prefixWord ++ tailWord_2036796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036796).length < 2 ^ (prefixWord ++ tailWord_2036796).sum := by decide
  have hdescent : baseEnd_2036796 < baseStart_2036796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036813 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_2036813 : Nat := 118140960795 + 2036813 * 2 ^ 59
def prefixEnd_2036813 : Nat := 4983230072969 + 3 ^ 40 * 2036813 * 2
def baseEnd_2036813 : Nat := 697242714884163128980249

theorem tailTrace_2036813 : CollatzResearch.WordTrace tailWord_2036813 prefixEnd_2036813 697242714884163128980249 := by
  unfold tailWord_2036813
  simp only [CollatzResearch.WordTrace]
  refine ⟨74288673169981835810963093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49525782113321223873975395 74288673169981835810963093)
  ·
    refine ⟨3482281554842898553638895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74288673169981835810963093 3482281554842898553638895)
    ·
      refine ⟨5223422332264347830458343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3482281554842898553638895 5223422332264347830458343)
      ·
        refine ⟨7835133498396521745687515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5223422332264347830458343 7835133498396521745687515)
        ·
          refine ⟨11752700247594782618531273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7835133498396521745687515 11752700247594782618531273)
          ·
            refine ⟨8814525185696086963898455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11752700247594782618531273 8814525185696086963898455)
            ·
              refine ⟨13221787778544130445847683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8814525185696086963898455 13221787778544130445847683)
              ·
                refine ⟨19832681667816195668771525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13221787778544130445847683 19832681667816195668771525)
                ·
                  refine ⟨3718627812715536687894661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19832681667816195668771525 3718627812715536687894661)
                  ·
                    refine ⟨697242714884163128980249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3718627812715536687894661 697242714884163128980249)
                    ·
                      rfl

theorem cell22_2036813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_2036813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036813 prefixEnd_2036813 := by exact prefixLift 2036813
  have htrace : WordTrace (prefixWord ++ tailWord_2036813) baseStart_2036813 baseEnd_2036813 := by
    simpa [prefixWord, tailWord_2036813, baseEnd_2036813] using wordTrace_append hprefix tailTrace_2036813
  have hstable : (prefixWord ++ tailWord_2036813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036813).length < 2 ^ (prefixWord ++ tailWord_2036813).sum := by decide
  have hdescent : baseEnd_2036813 < baseStart_2036813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036860 : List Nat := [2, 2, 2, 1, 1, 3, 2, 5, 1, 3]
def baseStart_2036860 : Nat := 118140960795 + 2036860 * 2 ^ 59
def prefixEnd_2036860 : Nat := 4983230072969 + 3 ^ 40 * 2036860 * 2
def baseEnd_2036860 : Nat := 697258803944670673055105

theorem tailTrace_2036860 : CollatzResearch.WordTrace tailWord_2036860 prefixEnd_2036860 697258803944670673055105 := by
  unfold tailWord_2036860
  simp only [CollatzResearch.WordTrace]
  refine ⟨37145193700405781418962017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49526924933874375225282689 37145193700405781418962017)
  ·
    refine ⟨27858895275304336064221513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37145193700405781418962017 27858895275304336064221513)
    ·
      refine ⟨20894171456478252048166135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27858895275304336064221513 20894171456478252048166135)
      ·
        refine ⟨31341257184717378072249203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20894171456478252048166135 31341257184717378072249203)
        ·
          refine ⟨47011885777076067108373805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31341257184717378072249203 47011885777076067108373805)
          ·
            refine ⟨17629457166403525165640177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47011885777076067108373805 17629457166403525165640177)
            ·
              refine ⟨13222092874802643874230133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17629457166403525165640177 13222092874802643874230133)
              ·
                refine ⟨1239571207012747863209075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13222092874802643874230133 1239571207012747863209075)
                ·
                  refine ⟨1859356810519121794813613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239571207012747863209075 1859356810519121794813613)
                  ·
                    refine ⟨697258803944670673055105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1859356810519121794813613 697258803944670673055105)
                    ·
                      rfl

theorem cell22_2036860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_2036860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036860 prefixEnd_2036860 := by exact prefixLift 2036860
  have htrace : WordTrace (prefixWord ++ tailWord_2036860) baseStart_2036860 baseEnd_2036860 := by
    simpa [prefixWord, tailWord_2036860, baseEnd_2036860] using wordTrace_append hprefix tailTrace_2036860
  have hstable : (prefixWord ++ tailWord_2036860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036860).length < 2 ^ (prefixWord ++ tailWord_2036860).sum := by decide
  have hdescent : baseEnd_2036860 < baseStart_2036860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036862 : List Nat := [4, 2, 4, 1, 2, 9]
def baseStart_2036862 : Nat := 118140960795 + 2036862 * 2 ^ 59
def prefixEnd_2036862 : Nat := 4983230072969 + 3 ^ 40 * 2036862 * 2
def baseEnd_2036862 : Nat := 8608141834389423882779

theorem tailTrace_2036862 : CollatzResearch.WordTrace tailWord_2036862 prefixEnd_2036862 8608141834389423882779 := by
  unfold tailWord_2036862
  simp only [CollatzResearch.WordTrace]
  refine ⟨9286307543350539647437105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49526973564536211452997893 9286307543350539647437105)
  ·
    refine ⟨6964730657512904735577829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9286307543350539647437105 6964730657512904735577829)
    ·
      refine ⟨1305886998283669637920843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6964730657512904735577829 1305886998283669637920843)
      ·
        refine ⟨1958830497425504456881265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1305886998283669637920843 1958830497425504456881265)
        ·
          refine ⟨1469122873069128342660949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1958830497425504456881265 1469122873069128342660949)
          ·
            refine ⟨8608141834389423882779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1469122873069128342660949 8608141834389423882779)
            ·
              rfl

theorem cell22_2036862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 9].length) (baseStart_2036862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036862 prefixEnd_2036862 := by exact prefixLift 2036862
  have htrace : WordTrace (prefixWord ++ tailWord_2036862) baseStart_2036862 baseEnd_2036862 := by
    simpa [prefixWord, tailWord_2036862, baseEnd_2036862] using wordTrace_append hprefix tailTrace_2036862
  have hstable : (prefixWord ++ tailWord_2036862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036862).length < 2 ^ (prefixWord ++ tailWord_2036862).sum := by decide
  have hdescent : baseEnd_2036862 < baseStart_2036862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036871 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 2, 5]
def baseStart_2036871 : Nat := 118140960795 + 2036871 * 2 ^ 59
def prefixEnd_2036871 : Nat := 4983230072969 + 3 ^ 40 * 2036871 * 2
def baseEnd_2036871 : Nat := 697262569469470311030071

theorem tailTrace_2036871 : CollatzResearch.WordTrace tailWord_2036871 prefixEnd_2036871 697262569469470311030071 := by
  unfold tailWord_2036871
  simp only [CollatzResearch.WordTrace]
  refine ⟨74290788603771711716574467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49527192402514474477716311 74290788603771711716574467)
  ·
    refine ⟨111436182905657567574861701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74290788603771711716574467 111436182905657567574861701)
    ·
      refine ⟨20894284294810793920286569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111436182905657567574861701 20894284294810793920286569)
      ·
        refine ⟨15670713221108095440214927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20894284294810793920286569 15670713221108095440214927)
        ·
          refine ⟨23506069831662143160322391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15670713221108095440214927 23506069831662143160322391)
          ·
            refine ⟨35259104747493214740483587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23506069831662143160322391 35259104747493214740483587)
            ·
              refine ⟨52888657121239822110725381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35259104747493214740483587 52888657121239822110725381)
              ·
                refine ⟨9916623210232466645761009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52888657121239822110725381 9916623210232466645761009)
                ·
                  refine ⟨7437467407674349984320757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9916623210232466645761009 7437467407674349984320757)
                  ·
                    refine ⟨697262569469470311030071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7437467407674349984320757 697262569469470311030071)
                    ·
                      rfl

theorem cell22_2036871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_2036871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036871 prefixEnd_2036871 := by exact prefixLift 2036871
  have htrace : WordTrace (prefixWord ++ tailWord_2036871) baseStart_2036871 baseEnd_2036871 := by
    simpa [prefixWord, tailWord_2036871, baseEnd_2036871] using wordTrace_append hprefix tailTrace_2036871
  have hstable : (prefixWord ++ tailWord_2036871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036871).length < 2 ^ (prefixWord ++ tailWord_2036871).sum := by decide
  have hdescent : baseEnd_2036871 < baseStart_2036871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036873 : List Nat := [1, 2, 1, 1, 4, 4, 2, 2, 5]
def baseStart_2036873 : Nat := 118140960795 + 2036873 * 2 ^ 59
def prefixEnd_2036873 : Nat := 4983230072969 + 3 ^ 40 * 2036873 * 2
def baseEnd_2036873 : Nat := 232421084703447657493355

theorem tailTrace_2036873 : CollatzResearch.WordTrace tailWord_2036873 prefixEnd_2036873 232421084703447657493355 := by
  unfold tailWord_2036873
  simp only [CollatzResearch.WordTrace]
  refine ⟨74290861549764466058147273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49527241033176310705431515 74290861549764466058147273)
  ·
    refine ⟨55718146162323349543610455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74290861549764466058147273 55718146162323349543610455)
    ·
      refine ⟨83577219243485024315415683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55718146162323349543610455 83577219243485024315415683)
      ·
        refine ⟨125365828865227536473123525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83577219243485024315415683 125365828865227536473123525)
        ·
          refine ⟨23506092912230163088710661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125365828865227536473123525 23506092912230163088710661)
          ·
            refine ⟨4407392421043155579133249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23506092912230163088710661 4407392421043155579133249)
            ·
              refine ⟨3305544315782366684349937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4407392421043155579133249 3305544315782366684349937)
              ·
                refine ⟨2479158236836775013262453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3305544315782366684349937 2479158236836775013262453)
                ·
                  refine ⟨232421084703447657493355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2479158236836775013262453 232421084703447657493355)
                  ·
                    rfl

theorem cell22_2036873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 5].length) (baseStart_2036873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036873 prefixEnd_2036873 := by exact prefixLift 2036873
  have htrace : WordTrace (prefixWord ++ tailWord_2036873) baseStart_2036873 baseEnd_2036873 := by
    simpa [prefixWord, tailWord_2036873, baseEnd_2036873] using wordTrace_append hprefix tailTrace_2036873
  have hstable : (prefixWord ++ tailWord_2036873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036873).length < 2 ^ (prefixWord ++ tailWord_2036873).sum := by decide
  have hdescent : baseEnd_2036873 < baseStart_2036873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036888 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 2, 5]
def baseStart_2036888 : Nat := 118140960795 + 2036888 * 2 ^ 59
def prefixEnd_2036888 : Nat := 4983230072969 + 3 ^ 40 * 2036888 * 2
def baseEnd_2036888 : Nat := 697268388916887933355019

theorem tailTrace_2036888 : CollatzResearch.WordTrace tailWord_2036888 prefixEnd_2036888 697268388916887933355019 := by
  unfold tailWord_2036888
  simp only [CollatzResearch.WordTrace]
  refine ⟨37145704322355061809971659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49527605763140082413295545 37145704322355061809971659)
  ·
    refine ⟨55718556483532592714957489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37145704322355061809971659 55718556483532592714957489)
    ·
      refine ⟨41788917362649444536218117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55718556483532592714957489 41788917362649444536218117)
      ·
        refine ⟨7835422005496770850540897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41788917362649444536218117 7835422005496770850540897)
        ·
          refine ⟨5876566504122578137905673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7835422005496770850540897 5876566504122578137905673)
          ·
            refine ⟨4407424878091933603429255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5876566504122578137905673 4407424878091933603429255)
            ·
              refine ⟨6611137317137900405143883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4407424878091933603429255 6611137317137900405143883)
              ·
                refine ⟨9916705975706850607715825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6611137317137900405143883 9916705975706850607715825)
                ·
                  refine ⟨7437529481780137955786869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9916705975706850607715825 7437529481780137955786869)
                  ·
                    refine ⟨697268388916887933355019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7437529481780137955786869 697268388916887933355019)
                    ·
                      rfl

theorem cell22_2036888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_2036888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036888 prefixEnd_2036888 := by exact prefixLift 2036888
  have htrace : WordTrace (prefixWord ++ tailWord_2036888) baseStart_2036888 baseEnd_2036888 := by
    simpa [prefixWord, tailWord_2036888, baseEnd_2036888] using wordTrace_append hprefix tailTrace_2036888
  have hstable : (prefixWord ++ tailWord_2036888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036888).length < 2 ^ (prefixWord ++ tailWord_2036888).sum := by decide
  have hdescent : baseEnd_2036888 < baseStart_2036888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036901 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 8]
def baseStart_2036901 : Nat := 118140960795 + 2036901 * 2 ^ 59
def prefixEnd_2036901 : Nat := 4983230072969 + 3 ^ 40 * 2036901 * 2
def baseEnd_2036901 : Nat := 232424279694186744259993

theorem tailTrace_2036901 : CollatzResearch.WordTrace tailWord_2036901 prefixEnd_2036901 232424279694186744259993 := by
  unfold tailWord_2036901
  simp only [CollatzResearch.WordTrace]
  refine ⟨74291882793663026840166557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49527921862442017893444371 74291882793663026840166557)
  ·
    refine ⟨27859456047623635065062459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74291882793663026840166557 27859456047623635065062459)
    ·
      refine ⟨41789184071435452597593689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27859456047623635065062459 41789184071435452597593689)
      ·
        refine ⟨31341888053576589448195267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41789184071435452597593689 31341888053576589448195267)
        ·
          refine ⟨47012832080364884172292901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31341888053576589448195267 47012832080364884172292901)
          ·
            refine ⟨8814906015068415782304919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47012832080364884172292901 8814906015068415782304919)
            ·
              refine ⟨13222359022602623673457379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8814906015068415782304919 13222359022602623673457379)
              ·
                refine ⟨19833538533903935510186069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13222359022602623673457379 19833538533903935510186069)
                ·
                  refine ⟨232424279694186744259993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19833538533903935510186069 232424279694186744259993)
                  ·
                    rfl

theorem cell22_2036901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_2036901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036901 prefixEnd_2036901 := by exact prefixLift 2036901
  have htrace : WordTrace (prefixWord ++ tailWord_2036901) baseStart_2036901 baseEnd_2036901 := by
    simpa [prefixWord, tailWord_2036901, baseEnd_2036901] using wordTrace_append hprefix tailTrace_2036901
  have hstable : (prefixWord ++ tailWord_2036901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036901).length < 2 ^ (prefixWord ++ tailWord_2036901).sum := by decide
  have hdescent : baseEnd_2036901 < baseStart_2036901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036976 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 3, 8]
def baseStart_2036976 : Nat := 118140960795 + 2036976 * 2 ^ 59
def prefixEnd_2036976 : Nat := 4983230072969 + 3 ^ 40 * 2036976 * 2
def baseEnd_2036976 : Nat := 697298513115285037154749

theorem tailTrace_2036976 : CollatzResearch.WordTrace tailWord_2036976 prefixEnd_2036976 697298513115285037154749 := by
  unfold tailWord_2036976
  simp only [CollatzResearch.WordTrace]
  refine ⟨37147309134195657324573391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49529745512260876432764521 37147309134195657324573391)
  ·
    refine ⟨55720963701293485986860087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37147309134195657324573391 55720963701293485986860087)
    ·
      refine ⟨83581445551940228980290131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55720963701293485986860087 83581445551940228980290131)
      ·
        refine ⟨125372168327910343470435197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83581445551940228980290131 125372168327910343470435197)
        ·
          refine ⟨47014563122966378801413199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125372168327910343470435197 47014563122966378801413199)
          ·
            refine ⟨70521844684449568202119799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47014563122966378801413199 70521844684449568202119799)
            ·
              refine ⟨105782767026674352303179699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70521844684449568202119799 105782767026674352303179699)
              ·
                refine ⟨158674150540011528454769549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105782767026674352303179699 158674150540011528454769549)
                ·
                  refine ⟨59502806452504323170538581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158674150540011528454769549 59502806452504323170538581)
                  ·
                    refine ⟨697298513115285037154749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59502806452504323170538581 697298513115285037154749)
                    ·
                      rfl

theorem cell22_2036976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_2036976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036976 prefixEnd_2036976 := by exact prefixLift 2036976
  have htrace : WordTrace (prefixWord ++ tailWord_2036976) baseStart_2036976 baseEnd_2036976 := by
    simpa [prefixWord, tailWord_2036976, baseEnd_2036976] using wordTrace_append hprefix tailTrace_2036976
  have hstable : (prefixWord ++ tailWord_2036976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036976).length < 2 ^ (prefixWord ++ tailWord_2036976).sum := by decide
  have hdescent : baseEnd_2036976 < baseStart_2036976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036995 : List Nat := [1, 1, 1, 3, 2, 4, 3, 1, 3, 3]
def baseStart_2036995 : Nat := 118140960795 + 2036995 * 2 ^ 59
def prefixEnd_2036995 : Nat := 4983230072969 + 3 ^ 40 * 2036995 * 2
def baseEnd_2036995 : Nat := 697305017203575320929691

theorem tailTrace_2036995 : CollatzResearch.WordTrace tailWord_2036995 prefixEnd_2036995 697305017203575320929691 := by
  unfold tailWord_2036995
  simp only [CollatzResearch.WordTrace]
  refine ⟨74295311255322480894088439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49530207503548320596058959 74295311255322480894088439)
  ·
    refine ⟨111442966882983721341132659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74295311255322480894088439 111442966882983721341132659)
    ·
      refine ⟨167164450324475582011698989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111442966882983721341132659 167164450324475582011698989)
      ·
        refine ⟨62686668871678343254387121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167164450324475582011698989 62686668871678343254387121)
        ·
          refine ⟨47015001653758757440790341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62686668871678343254387121 47015001653758757440790341)
          ·
            refine ⟨8815312810079767020148189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47015001653758757440790341 8815312810079767020148189)
            ·
              refine ⟨3305742303779912632555571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8815312810079767020148189 3305742303779912632555571)
              ·
                refine ⟨4958613455669868948833357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3305742303779912632555571 4958613455669868948833357)
                ·
                  refine ⟨1859480045876200855812509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4958613455669868948833357 1859480045876200855812509)
                  ·
                    refine ⟨697305017203575320929691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1859480045876200855812509 697305017203575320929691)
                    ·
                      rfl

theorem cell22_2036995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 3].length) (baseStart_2036995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2036995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2036995 prefixEnd_2036995 := by exact prefixLift 2036995
  have htrace : WordTrace (prefixWord ++ tailWord_2036995) baseStart_2036995 baseEnd_2036995 := by
    simpa [prefixWord, tailWord_2036995, baseEnd_2036995] using wordTrace_append hprefix tailTrace_2036995
  have hstable : (prefixWord ++ tailWord_2036995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036995).length < 2 ^ (prefixWord ++ tailWord_2036995).sum := by decide
  have hdescent : baseEnd_2036995 < baseStart_2036995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037138 : List Nat := [3, 2, 3, 3, 2, 1, 1, 3, 4]
def baseStart_2037138 : Nat := 118140960795 + 2037138 * 2 ^ 59
def prefixEnd_2037138 : Nat := 4983230072969 + 3 ^ 40 * 2037138 * 2
def baseEnd_2037138 : Nat := 232451323008656871534751

theorem tailTrace_2037138 : CollatzResearch.WordTrace tailWord_2037138 prefixEnd_2037138 232451323008656871534751 := by
  unfold tailWord_2037138
  simp only [CollatzResearch.WordTrace]
  refine ⟨18575131723451104079136017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49533684595869610877696045 18575131723451104079136017)
  ·
    refine ⟨13931348792588328059352013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18575131723451104079136017 13931348792588328059352013)
    ·
      refine ⟨5224255797220623022257005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13931348792588328059352013 5224255797220623022257005)
      ·
        refine ⟨1959095923957733633346377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5224255797220623022257005 1959095923957733633346377)
        ·
          refine ⟨1469321942968300225009783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1959095923957733633346377 1469321942968300225009783)
          ·
            refine ⟨2203982914452450337514675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469321942968300225009783 2203982914452450337514675)
            ·
              refine ⟨3305974371678675506272013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2203982914452450337514675 3305974371678675506272013)
              ·
                refine ⟨1239740389379503314852005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3305974371678675506272013 1239740389379503314852005)
                ·
                  refine ⟨232451323008656871534751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1239740389379503314852005 232451323008656871534751)
                  ·
                    rfl

theorem cell22_2037138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_2037138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2037138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2037138 prefixEnd_2037138 := by exact prefixLift 2037138
  have htrace : WordTrace (prefixWord ++ tailWord_2037138) baseStart_2037138 baseEnd_2037138 := by
    simpa [prefixWord, tailWord_2037138, baseEnd_2037138] using wordTrace_append hprefix tailTrace_2037138
  have hstable : (prefixWord ++ tailWord_2037138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037138).length < 2 ^ (prefixWord ++ tailWord_2037138).sum := by decide
  have hdescent : baseEnd_2037138 < baseStart_2037138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037177 : List Nat := [1, 2, 1, 4, 4, 1, 1, 3, 5]
def baseStart_2037177 : Nat := 118140960795 + 2037177 * 2 ^ 59
def prefixEnd_2037177 : Nat := 4983230072969 + 3 ^ 40 * 2037177 * 2
def baseEnd_2037177 : Nat := 232455773174329170959711

theorem tailTrace_2037177 : CollatzResearch.WordTrace tailWord_2037177 prefixEnd_2037177 232455773174329170959711 := by
  unfold tailWord_2037177
  simp only [CollatzResearch.WordTrace]
  refine ⟨74301949340663125977213785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49534632893775417318142523 74301949340663125977213785)
  ·
    refine ⟨55726462005497344482910339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74301949340663125977213785 55726462005497344482910339)
    ·
      refine ⟨83589693008246016724365509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55726462005497344482910339 83589693008246016724365509)
      ·
        refine ⟨15673067439046128135818533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83589693008246016724365509 15673067439046128135818533)
        ·
          refine ⟨2938700144821149025465975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15673067439046128135818533 2938700144821149025465975)
          ·
            refine ⟨4408050217231723538198963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2938700144821149025465975 4408050217231723538198963)
            ·
              refine ⟨6612075325847585307298445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4408050217231723538198963 6612075325847585307298445)
              ·
                refine ⟨2479528247192844490236917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6612075325847585307298445 2479528247192844490236917)
                ·
                  refine ⟨232455773174329170959711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2479528247192844490236917 232455773174329170959711)
                  ·
                    rfl

theorem cell22_2037177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 5].length) (baseStart_2037177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2037177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2037177 prefixEnd_2037177 := by exact prefixLift 2037177
  have htrace : WordTrace (prefixWord ++ tailWord_2037177) baseStart_2037177 baseEnd_2037177 := by
    simpa [prefixWord, tailWord_2037177, baseEnd_2037177] using wordTrace_append hprefix tailTrace_2037177
  have hstable : (prefixWord ++ tailWord_2037177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037177).length < 2 ^ (prefixWord ++ tailWord_2037177).sum := by decide
  have hdescent : baseEnd_2037177 < baseStart_2037177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037288 : List Nat := [2, 1, 5, 2, 2, 1, 3, 1, 2, 3]
def baseStart_2037288 : Nat := 118140960795 + 2037288 * 2 ^ 59
def prefixEnd_2037288 : Nat := 4983230072969 + 3 ^ 40 * 2037288 * 2
def baseEnd_2037288 : Nat := 697405317091420223353793

theorem tailTrace_2037288 : CollatzResearch.WordTrace tailWord_2037288 prefixEnd_2037288 697405317091420223353793 := by
  unfold tailWord_2037288
  simp only [CollatzResearch.WordTrace]
  refine ⟨37152998921630495967252259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49537331895507327956336345 37152998921630495967252259)
  ·
    refine ⟨55729498382445743950878389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37152998921630495967252259 55729498382445743950878389)
    ·
      refine ⟨5224640473354288495394849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55729498382445743950878389 5224640473354288495394849)
      ·
        refine ⟨3918480355015716371546137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5224640473354288495394849 3918480355015716371546137)
        ·
          refine ⟨2938860266261787278659603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3918480355015716371546137 2938860266261787278659603)
          ·
            refine ⟨4408290399392680917989405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2938860266261787278659603 4408290399392680917989405)
            ·
              refine ⟨1653108899772255344246027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4408290399392680917989405 1653108899772255344246027)
              ·
                refine ⟨2479663349658383016369041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1653108899772255344246027 2479663349658383016369041)
                ·
                  refine ⟨1859747512243787262276781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2479663349658383016369041 1859747512243787262276781)
                  ·
                    refine ⟨697405317091420223353793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1859747512243787262276781 697405317091420223353793)
                    ·
                      rfl

theorem cell22_2037288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_2037288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2037288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2037288 prefixEnd_2037288 := by exact prefixLift 2037288
  have htrace : WordTrace (prefixWord ++ tailWord_2037288) baseStart_2037288 baseEnd_2037288 := by
    simpa [prefixWord, tailWord_2037288, baseEnd_2037288] using wordTrace_append hprefix tailTrace_2037288
  have hstable : (prefixWord ++ tailWord_2037288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037288).length < 2 ^ (prefixWord ++ tailWord_2037288).sum := by decide
  have hdescent : baseEnd_2037288 < baseStart_2037288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037387 : List Nat := [1, 1, 1, 1, 4, 1, 3, 4, 2, 4]
def baseStart_2037387 : Nat := 118140960795 + 2037387 * 2 ^ 59
def prefixEnd_2037387 : Nat := 4983230072969 + 3 ^ 40 * 2037387 * 2
def baseEnd_2037387 : Nat := 697439206814616965128489

theorem tailTrace_2037387 : CollatzResearch.WordTrace tailWord_2037387 prefixEnd_2037387 697439206814616965128489 := by
  unfold tailWord_2037387
  simp only [CollatzResearch.WordTrace]
  refine ⟨74309608669902331842358415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49539739113268221228238943 74309608669902331842358415)
  ·
    refine ⟨111464413004853497763537623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74309608669902331842358415 111464413004853497763537623)
    ·
      refine ⟨167196619507280246645306435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111464413004853497763537623 167196619507280246645306435)
      ·
        refine ⟨250794929260920369967959653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167196619507280246645306435 250794929260920369967959653)
        ·
          refine ⟨47024049236422569368992435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250794929260920369967959653 47024049236422569368992435)
          ·
            refine ⟨70536073854633854053488653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47024049236422569368992435 70536073854633854053488653)
            ·
              refine ⟨26451027695487695270058245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70536073854633854053488653 26451027695487695270058245)
              ·
                refine ⟨4959567692903942863135921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26451027695487695270058245 4959567692903942863135921)
                ·
                  refine ⟨3719675769677957147351941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4959567692903942863135921 3719675769677957147351941)
                  ·
                    refine ⟨697439206814616965128489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3719675769677957147351941 697439206814616965128489)
                    ·
                      rfl

theorem cell22_2037387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 4].length) (baseStart_2037387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2037387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2037387 prefixEnd_2037387 := by exact prefixLift 2037387
  have htrace : WordTrace (prefixWord ++ tailWord_2037387) baseStart_2037387 baseEnd_2037387 := by
    simpa [prefixWord, tailWord_2037387, baseEnd_2037387] using wordTrace_append hprefix tailTrace_2037387
  have hstable : (prefixWord ++ tailWord_2037387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037387).length < 2 ^ (prefixWord ++ tailWord_2037387).sum := by decide
  have hdescent : baseEnd_2037387 < baseStart_2037387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037406 : List Nat := [4, 3, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_2037406 : Nat := 118140960795 + 2037406 * 2 ^ 59
def prefixEnd_2037406 : Nat := 4983230072969 + 3 ^ 40 * 2037406 * 2
def baseEnd_2037406 : Nat := 697445710902907248903431

theorem tailTrace_2037406 : CollatzResearch.WordTrace tailWord_2037406 prefixEnd_2037406 697445710902907248903431 := by
  unfold tailWord_2037406
  simp only [CollatzResearch.WordTrace]
  refine ⟨9288787707104187260912509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49540201104555665391533381 9288787707104187260912509)
  ·
    refine ⟨3483295390164070222842191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9288787707104187260912509 3483295390164070222842191)
    ·
      refine ⟨5224943085246105334263287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3483295390164070222842191 5224943085246105334263287)
      ·
        refine ⟨7837414627869158001394931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5224943085246105334263287 7837414627869158001394931)
        ·
          refine ⟨11756121941803737002092397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7837414627869158001394931 11756121941803737002092397)
          ·
            refine ⟨4408545728176401375784649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11756121941803737002092397 4408545728176401375784649)
            ·
              refine ⟨3306409296132301031838487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4408545728176401375784649 3306409296132301031838487)
              ·
                refine ⟨4959613944198451547757731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3306409296132301031838487 4959613944198451547757731)
                ·
                  refine ⟨7439420916297677321636597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4959613944198451547757731 7439420916297677321636597)
                  ·
                    refine ⟨697445710902907248903431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7439420916297677321636597 697445710902907248903431)
                    ·
                      rfl

theorem cell22_2037406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_2037406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2037406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2037406 prefixEnd_2037406 := by exact prefixLift 2037406
  have htrace : WordTrace (prefixWord ++ tailWord_2037406) baseStart_2037406 baseEnd_2037406 := by
    simpa [prefixWord, tailWord_2037406, baseEnd_2037406] using wordTrace_append hprefix tailTrace_2037406
  have hstable : (prefixWord ++ tailWord_2037406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037406).length < 2 ^ (prefixWord ++ tailWord_2037406).sum := by decide
  have hdescent : baseEnd_2037406 < baseStart_2037406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037447 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 7]
def baseStart_2037447 : Nat := 118140960795 + 2037447 * 2 ^ 59
def prefixEnd_2037447 : Nat := 4983230072969 + 3 ^ 40 * 2037447 * 2
def baseEnd_2037447 : Nat := 232486582013598936209435

theorem tailTrace_2037447 : CollatzResearch.WordTrace tailWord_2037447 prefixEnd_2037447 232486582013598936209435 := by
  unfold tailWord_2037447
  simp only [CollatzResearch.WordTrace]
  refine ⟨74311797049684962089542595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49541198033123308059695063 74311797049684962089542595)
  ·
    refine ⟨111467695574527443134313893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74311797049684962089542595 111467695574527443134313893)
    ·
      refine ⟨20900192920223895587683855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111467695574527443134313893 20900192920223895587683855)
      ·
        refine ⟨31350289380335843381525783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20900192920223895587683855 31350289380335843381525783)
        ·
          refine ⟨47025434070503765072288675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31350289380335843381525783 47025434070503765072288675)
          ·
            refine ⟨70538151105755647608433013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47025434070503765072288675 70538151105755647608433013)
            ·
              refine ⟨6612951666164591963290595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70538151105755647608433013 6612951666164591963290595)
              ·
                refine ⟨9919427499246887944935893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6612951666164591963290595 9919427499246887944935893)
                ·
                  refine ⟨232486582013598936209435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9919427499246887944935893 232486582013598936209435)
                  ·
                    rfl

theorem cell22_2037447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 7].length) (baseStart_2037447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2037447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2037447 prefixEnd_2037447 := by exact prefixLift 2037447
  have htrace : WordTrace (prefixWord ++ tailWord_2037447) baseStart_2037447 baseEnd_2037447 := by
    simpa [prefixWord, tailWord_2037447, baseEnd_2037447] using wordTrace_append hprefix tailTrace_2037447
  have hstable : (prefixWord ++ tailWord_2037447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037447).length < 2 ^ (prefixWord ++ tailWord_2037447).sum := by decide
  have hdescent : baseEnd_2037447 < baseStart_2037447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037485 : List Nat := [1, 5, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_2037485 : Nat := 118140960795 + 2037485 * 2 ^ 59
def prefixEnd_2037485 : Nat := 4983230072969 + 3 ^ 40 * 2037485 * 2
def baseEnd_2037485 : Nat := 697472754217377376178189

theorem tailTrace_2037485 : CollatzResearch.WordTrace tailWord_2037485 prefixEnd_2037485 697472754217377376178189 := by
  unfold tailWord_2037485
  simp only [CollatzResearch.WordTrace]
  refine ⟨74313183023547294579425909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49542122015698196386283939 74313183023547294579425909)
  ·
    refine ⟨6966860908457558866821179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74313183023547294579425909 6966860908457558866821179)
    ·
      refine ⟨10450291362686338300231769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6966860908457558866821179 10450291362686338300231769)
      ·
        refine ⟨7837718522014753725173827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10450291362686338300231769 7837718522014753725173827)
        ·
          refine ⟨11756577783022130587760741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7837718522014753725173827 11756577783022130587760741)
          ·
            refine ⟨2204358334316649485205139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11756577783022130587760741 2204358334316649485205139)
            ·
              refine ⟨3306537501474974227807709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2204358334316649485205139 3306537501474974227807709)
              ·
                refine ⟨1239951563053115335427891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3306537501474974227807709 1239951563053115335427891)
                ·
                  refine ⟨1859927344579673003141837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239951563053115335427891 1859927344579673003141837)
                  ·
                    refine ⟨697472754217377376178189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1859927344579673003141837 697472754217377376178189)
                    ·
                      rfl

theorem cell22_2037485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_2037485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2037485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2037485 prefixEnd_2037485 := by exact prefixLift 2037485
  have htrace : WordTrace (prefixWord ++ tailWord_2037485) baseStart_2037485 baseEnd_2037485 := by
    simpa [prefixWord, tailWord_2037485, baseEnd_2037485] using wordTrace_append hprefix tailTrace_2037485
  have hstable : (prefixWord ++ tailWord_2037485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037485).length < 2 ^ (prefixWord ++ tailWord_2037485).sum := by decide
  have hdescent : baseEnd_2037485 < baseStart_2037485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037502 : List Nat := [4, 2, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_2037502 : Nat := 118140960795 + 2037502 * 2 ^ 59
def prefixEnd_2037502 : Nat := 4983230072969 + 3 ^ 40 * 2037502 * 2
def baseEnd_2037502 : Nat := 697478573664794998503137

theorem tailTrace_2037502 : CollatzResearch.WordTrace tailWord_2037502 prefixEnd_2037502 697478573664794998503137 := by
  unfold tailWord_2037502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9289225383060713310349345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49542535376323804321863173 9289225383060713310349345)
  ·
    refine ⟨6966919037295534982762009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9289225383060713310349345 6966919037295534982762009)
    ·
      refine ⟨5225189277971651237071507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6966919037295534982762009 5225189277971651237071507)
      ·
        refine ⟨7837783916957476855607261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5225189277971651237071507 7837783916957476855607261)
        ·
          refine ⟨2939168968859053820852723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7837783916957476855607261 2939168968859053820852723)
          ·
            refine ⟨4408753453288580731279085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2939168968859053820852723 4408753453288580731279085)
            ·
              refine ⟨1653282544983217774229657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4408753453288580731279085 1653282544983217774229657)
              ·
                refine ⟨1239961908737413330672243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1653282544983217774229657 1239961908737413330672243)
                ·
                  refine ⟨1859942863106119996008365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239961908737413330672243 1859942863106119996008365)
                  ·
                    refine ⟨697478573664794998503137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1859942863106119996008365 697478573664794998503137)
                    ·
                      rfl

theorem cell22_2037502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_2037502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2037502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2037502 prefixEnd_2037502 := by exact prefixLift 2037502
  have htrace : WordTrace (prefixWord ++ tailWord_2037502) baseStart_2037502 baseEnd_2037502 := by
    simpa [prefixWord, tailWord_2037502, baseEnd_2037502] using wordTrace_append hprefix tailTrace_2037502
  have hstable : (prefixWord ++ tailWord_2037502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037502).length < 2 ^ (prefixWord ++ tailWord_2037502).sum := by decide
  have hdescent : baseEnd_2037502 < baseStart_2037502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037539 : List Nat := [1, 1, 1, 4, 2, 1, 3, 3, 2, 4]
def baseStart_2037539 : Nat := 118140960795 + 2037539 * 2 ^ 59
def prefixEnd_2037539 : Nat := 4983230072969 + 3 ^ 40 * 2037539 * 2
def baseEnd_2037539 : Nat := 697491239520939235328023

theorem tailTrace_2037539 : CollatzResearch.WordTrace tailWord_2037539 prefixEnd_2037539 697491239520939235328023 := by
  unfold tailWord_2037539
  simp only [CollatzResearch.WordTrace]
  refine ⟨74315152565351661801891671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49543435043567774534594447 74315152565351661801891671)
  ·
    refine ⟨111472728848027492702837507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74315152565351661801891671 111472728848027492702837507)
    ·
      refine ⟨167209093272041239054256261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111472728848027492702837507 167209093272041239054256261)
      ·
        refine ⟨31351704988507732322673049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167209093272041239054256261 31351704988507732322673049)
        ·
          refine ⟨23513778741380799242004787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31351704988507732322673049 23513778741380799242004787)
          ·
            refine ⟨35270668112071198863007181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23513778741380799242004787 35270668112071198863007181)
            ·
              refine ⟨13226500542026699573627693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35270668112071198863007181 13226500542026699573627693)
              ·
                refine ⟨4959937703260012340110385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13226500542026699573627693 4959937703260012340110385)
                ·
                  refine ⟨3719953277445009255082789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4959937703260012340110385 3719953277445009255082789)
                  ·
                    refine ⟨697491239520939235328023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3719953277445009255082789 697491239520939235328023)
                    ·
                      rfl

theorem cell22_2037539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 4].length) (baseStart_2037539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2037539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2037539 prefixEnd_2037539 := by exact prefixLift 2037539
  have htrace : WordTrace (prefixWord ++ tailWord_2037539) baseStart_2037539 baseEnd_2037539 := by
    simpa [prefixWord, tailWord_2037539, baseEnd_2037539] using wordTrace_append hprefix tailTrace_2037539
  have hstable : (prefixWord ++ tailWord_2037539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037539).length < 2 ^ (prefixWord ++ tailWord_2037539).sum := by decide
  have hdescent : baseEnd_2037539 < baseStart_2037539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037586 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 5, 3]
def baseStart_2037586 : Nat := 118140960795 + 2037586 * 2 ^ 59
def prefixEnd_2037586 : Nat := 4983230072969 + 3 ^ 40 * 2037586 * 2
def baseEnd_2037586 : Nat := 697507328581446779402879

theorem tailTrace_2037586 : CollatzResearch.WordTrace tailWord_2037586 prefixEnd_2037586 697507328581446779402879 := by
  unfold tailWord_2037586
  simp only [CollatzResearch.WordTrace]
  refine ⟨18579216699045347207213153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49544577864120925885901741 18579216699045347207213153)
  ·
    refine ⟨13934412524284010405409865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18579216699045347207213153 13934412524284010405409865)
    ·
      refine ⟨10450809393213007804057399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13934412524284010405409865 10450809393213007804057399)
      ·
        refine ⟨15676214089819511706086099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10450809393213007804057399 15676214089819511706086099)
        ·
          refine ⟨23514321134729267559129149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15676214089819511706086099 23514321134729267559129149)
          ·
            refine ⟨8817870425523475334673431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23514321134729267559129149 8817870425523475334673431)
            ·
              refine ⟨13226805638285213002010147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8817870425523475334673431 13226805638285213002010147)
              ·
                refine ⟨19840208457427819503015221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13226805638285213002010147 19840208457427819503015221)
                ·
                  refine ⟨1860019542883858078407677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19840208457427819503015221 1860019542883858078407677)
                  ·
                    refine ⟨697507328581446779402879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1860019542883858078407677 697507328581446779402879)
                    ·
                      rfl

theorem cell22_2037586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_2037586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2037586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2037586 prefixEnd_2037586 := by exact prefixLift 2037586
  have htrace : WordTrace (prefixWord ++ tailWord_2037586) baseStart_2037586 baseEnd_2037586 := by
    simpa [prefixWord, tailWord_2037586, baseEnd_2037586] using wordTrace_append hprefix tailTrace_2037586
  have hstable : (prefixWord ++ tailWord_2037586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037586).length < 2 ^ (prefixWord ++ tailWord_2037586).sum := by decide
  have hdescent : baseEnd_2037586 < baseStart_2037586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037684 : List Nat := [2, 5, 2, 1, 3, 1, 2, 1, 5]
def baseStart_2037684 : Nat := 118140960795 + 2037684 * 2 ^ 59
def prefixEnd_2037684 : Nat := 4983230072969 + 3 ^ 40 * 2037684 * 2
def baseEnd_2037684 : Nat := 232513625328069063484193

theorem tailTrace_2037684 : CollatzResearch.WordTrace tailWord_2037684 prefixEnd_2037684 232513625328069063484193 := by
  unfold tailWord_2037684
  simp only [CollatzResearch.WordTrace]
  refine ⟨37160220574913175782960053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49546960766550901043946737 37160220574913175782960053)
  ·
    refine ⟨3483770678898110229652505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37160220574913175782960053 3483770678898110229652505)
    ·
      refine ⟨2612828009173582672239379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3483770678898110229652505 2612828009173582672239379)
      ·
        refine ⟨3919242013760374008359069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2612828009173582672239379 3919242013760374008359069)
        ·
          refine ⟨1469715755160140253134651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3919242013760374008359069 1469715755160140253134651)
          ·
            refine ⟨2204573632740210379701977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469715755160140253134651 2204573632740210379701977)
            ·
              refine ⟨1653430224555157784776483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2204573632740210379701977 1653430224555157784776483)
              ·
                refine ⟨2480145336832736677164725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1653430224555157784776483 2480145336832736677164725)
                ·
                  refine ⟨232513625328069063484193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2480145336832736677164725 232513625328069063484193)
                  ·
                    rfl

theorem cell22_2037684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_2037684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2037684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2037684 prefixEnd_2037684 := by exact prefixLift 2037684
  have htrace : WordTrace (prefixWord ++ tailWord_2037684) baseStart_2037684 baseEnd_2037684 := by
    simpa [prefixWord, tailWord_2037684, baseEnd_2037684] using wordTrace_append hprefix tailTrace_2037684
  have hstable : (prefixWord ++ tailWord_2037684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037684).length < 2 ^ (prefixWord ++ tailWord_2037684).sum := by decide
  have hdescent : baseEnd_2037684 < baseStart_2037684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037708 : List Nat := [2, 2, 1, 4, 1, 3, 2, 1, 2, 4]
def baseStart_2037708 : Nat := 118140960795 + 2037708 * 2 ^ 59
def prefixEnd_2037708 : Nat := 4983230072969 + 3 ^ 40 * 2037708 * 2
def baseEnd_2037708 : Nat := 697549091674679127852505

theorem tailTrace_2037708 : CollatzResearch.WordTrace tailWord_2037708 prefixEnd_2037708 697549091674679127852505 := by
  unfold tailWord_2037708
  simp only [CollatzResearch.WordTrace]
  refine ⟨37160658250869701832396889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49547544334492935776529185 37160658250869701832396889)
  ·
    refine ⟨27870493688152276374297667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37160658250869701832396889 27870493688152276374297667)
    ·
      refine ⟨41805740532228414561446501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27870493688152276374297667 41805740532228414561446501)
      ·
        refine ⟨7838576349792827730271219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41805740532228414561446501 7838576349792827730271219)
        ·
          refine ⟨11757864524689241595406829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7838576349792827730271219 11757864524689241595406829)
          ·
            refine ⟨4409199196758465598277561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11757864524689241595406829 4409199196758465598277561)
            ·
              refine ⟨3306899397568849198708171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4409199196758465598277561 3306899397568849198708171)
              ·
                refine ⟨4960349096353273798062257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3306899397568849198708171 4960349096353273798062257)
                ·
                  refine ⟨3720261822264955348546693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4960349096353273798062257 3720261822264955348546693)
                  ·
                    refine ⟨697549091674679127852505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3720261822264955348546693 697549091674679127852505)
                    ·
                      rfl

theorem cell22_2037708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_2037708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2037708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2037708 prefixEnd_2037708 := by exact prefixLift 2037708
  have htrace : WordTrace (prefixWord ++ tailWord_2037708) baseStart_2037708 baseEnd_2037708 := by
    simpa [prefixWord, tailWord_2037708, baseEnd_2037708] using wordTrace_append hprefix tailTrace_2037708
  have hstable : (prefixWord ++ tailWord_2037708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037708).length < 2 ^ (prefixWord ++ tailWord_2037708).sum := by decide
  have hdescent : baseEnd_2037708 < baseStart_2037708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037738 : List Nat := [3, 1, 3, 1, 2, 1, 2, 3, 3, 3]
def baseStart_2037738 : Nat := 118140960795 + 2037738 * 2 ^ 59
def prefixEnd_2037738 : Nat := 4983230072969 + 3 ^ 40 * 2037738 * 2
def baseEnd_2037738 : Nat := 697559361287769049602413

theorem tailTrace_2037738 : CollatzResearch.WordTrace tailWord_2037738 prefixEnd_2037738 697559361287769049602413 := by
  unfold tailWord_2037738
  simp only [CollatzResearch.WordTrace]
  refine ⟨18580602672907679697096467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49548273794420479192257245 18580602672907679697096467)
  ·
    refine ⟨27870904009361519545644701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18580602672907679697096467 27870904009361519545644701)
    ·
      refine ⟨10451589003510569829616763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27870904009361519545644701 10451589003510569829616763)
      ·
        refine ⟨15677383505265854744425145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10451589003510569829616763 15677383505265854744425145)
        ·
          refine ⟨11758037628949391058318859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15677383505265854744425145 11758037628949391058318859)
          ·
            refine ⟨17637056443424086587478289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11758037628949391058318859 17637056443424086587478289)
            ·
              refine ⟨13227792332568064940608717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17637056443424086587478289 13227792332568064940608717)
              ·
                refine ⟨4960422124713024352728269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13227792332568064940608717 4960422124713024352728269)
                ·
                  refine ⟨1860158296767384132273101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4960422124713024352728269 1860158296767384132273101)
                  ·
                    refine ⟨697559361287769049602413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1860158296767384132273101 697559361287769049602413)
                    ·
                      rfl

theorem cell22_2037738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_2037738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2037738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2037738 prefixEnd_2037738 := by exact prefixLift 2037738
  have htrace : WordTrace (prefixWord ++ tailWord_2037738) baseStart_2037738 baseEnd_2037738 := by
    simpa [prefixWord, tailWord_2037738, baseEnd_2037738] using wordTrace_append hprefix tailTrace_2037738
  have hstable : (prefixWord ++ tailWord_2037738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037738).length < 2 ^ (prefixWord ++ tailWord_2037738).sum := by decide
  have hdescent : baseEnd_2037738 < baseStart_2037738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037873 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 5, 3]
def baseStart_2037873 : Nat := 118140960795 + 2037873 * 2 ^ 59
def prefixEnd_2037873 : Nat := 4983230072969 + 3 ^ 40 * 2037873 * 2
def baseEnd_2037873 : Nat := 697605574546673697476999

theorem tailTrace_2037873 : CollatzResearch.WordTrace tailWord_2037873 prefixEnd_2037873 697605574546673697476999 := by
  unfold tailWord_2037873
  simp only [CollatzResearch.WordTrace]
  refine ⟨74327334546141636844550273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49551556364094424563033515 74327334546141636844550273)
  ·
    refine ⟨55745500909606227633412705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74327334546141636844550273 55745500909606227633412705)
    ·
      refine ⟨41809125682204670725059529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55745500909606227633412705 41809125682204670725059529)
      ·
        refine ⟨31356844261653503043794647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41809125682204670725059529 31356844261653503043794647)
        ·
          refine ⟨47035266392480254565691971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31356844261653503043794647 47035266392480254565691971)
          ·
            refine ⟨70552899588720381848537957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47035266392480254565691971 70552899588720381848537957)
            ·
              refine ⟨13228668672885071596600867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70552899588720381848537957 13228668672885071596600867)
              ·
                refine ⟨19843003009327607394901301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13228668672885071596600867 19843003009327607394901301)
                ·
                  refine ⟨1860281532124463193271997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19843003009327607394901301 1860281532124463193271997)
                  ·
                    refine ⟨697605574546673697476999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1860281532124463193271997 697605574546673697476999)
                    ·
                      rfl

theorem cell22_2037873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_2037873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2037873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2037873 prefixEnd_2037873 := by exact prefixLift 2037873
  have htrace : WordTrace (prefixWord ++ tailWord_2037873) baseStart_2037873 baseEnd_2037873 := by
    simpa [prefixWord, tailWord_2037873, baseEnd_2037873] using wordTrace_append hprefix tailTrace_2037873
  have hstable : (prefixWord ++ tailWord_2037873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037873).length < 2 ^ (prefixWord ++ tailWord_2037873).sum := by decide
  have hdescent : baseEnd_2037873 < baseStart_2037873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037941 : List Nat := [1, 3, 3, 4, 1, 1, 2, 3, 1, 3]
def baseStart_2037941 : Nat := 118140960795 + 2037941 * 2 ^ 59
def prefixEnd_2037941 : Nat := 4983230072969 + 3 ^ 40 * 2037941 * 2
def baseEnd_2037941 : Nat := 697628852336344186776791

theorem tailTrace_2037941 : CollatzResearch.WordTrace tailWord_2037941 prefixEnd_2037941 697628852336344186776791 := by
  unfold tailWord_2037941
  simp only [CollatzResearch.WordTrace]
  refine ⟨74329814709895284458025677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49553209806596856305350451 74329814709895284458025677)
  ·
    refine ⟨27873680516210731671759629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74329814709895284458025677 27873680516210731671759629)
    ·
      refine ⟨10452630193579024376909861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27873680516210731671759629 10452630193579024376909861)
      ·
        refine ⟨1959868161296067070670599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10452630193579024376909861 1959868161296067070670599)
        ·
          refine ⟨2939802241944100606005899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1959868161296067070670599 2939802241944100606005899)
          ·
            refine ⟨4409703362916150909008849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2939802241944100606005899 4409703362916150909008849)
            ·
              refine ⟨3307277522187113181756637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4409703362916150909008849 3307277522187113181756637)
              ·
                refine ⟨1240229070820167443158739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3307277522187113181756637 1240229070820167443158739)
                ·
                  refine ⟨1860343606230251164738109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1240229070820167443158739 1860343606230251164738109)
                  ·
                    refine ⟨697628852336344186776791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1860343606230251164738109 697628852336344186776791)
                    ·
                      rfl

theorem cell22_2037941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_2037941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2037941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2037941 prefixEnd_2037941 := by exact prefixLift 2037941
  have htrace : WordTrace (prefixWord ++ tailWord_2037941) baseStart_2037941 baseEnd_2037941 := by
    simpa [prefixWord, tailWord_2037941, baseEnd_2037941] using wordTrace_append hprefix tailTrace_2037941
  have hstable : (prefixWord ++ tailWord_2037941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037941).length < 2 ^ (prefixWord ++ tailWord_2037941).sum := by decide
  have hdescent : baseEnd_2037941 < baseStart_2037941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037954 : List Nat := [3, 5, 1, 1, 1, 1, 3, 2, 5]
def baseStart_2037954 : Nat := 118140960795 + 2037954 * 2 ^ 59
def prefixEnd_2037954 : Nat := 4983230072969 + 3 ^ 40 * 2037954 * 2
def baseEnd_2037954 : Nat := 232544434167338828733917

theorem tailTrace_2037954 : CollatzResearch.WordTrace tailWord_2037954 prefixEnd_2037954 232544434167338828733917 := by
  unfold tailWord_2037954
  simp only [CollatzResearch.WordTrace]
  refine ⟨18582572214712046919562229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49553525905898791785499277 18582572214712046919562229)
  ·
    refine ⟨1742116145129254398708959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18582572214712046919562229 1742116145129254398708959)
    ·
      refine ⟨2613174217693881598063439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1742116145129254398708959 2613174217693881598063439)
      ·
        refine ⟨3919761326540822397095159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2613174217693881598063439 3919761326540822397095159)
        ·
          refine ⟨5879641989811233595642739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3919761326540822397095159 5879641989811233595642739)
          ·
            refine ⟨8819462984716850393464109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5879641989811233595642739 8819462984716850393464109)
            ·
              refine ⟨3307298619268818897549041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8819462984716850393464109 3307298619268818897549041)
              ·
                refine ⟨2480473964451614173161781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3307298619268818897549041 2480473964451614173161781)
                ·
                  refine ⟨232544434167338828733917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2480473964451614173161781 232544434167338828733917)
                  ·
                    rfl

theorem cell22_2037954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_2037954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2037954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2037954 prefixEnd_2037954 := by exact prefixLift 2037954
  have htrace : WordTrace (prefixWord ++ tailWord_2037954) baseStart_2037954 baseEnd_2037954 := by
    simpa [prefixWord, tailWord_2037954, baseEnd_2037954] using wordTrace_append hprefix tailTrace_2037954
  have hstable : (prefixWord ++ tailWord_2037954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037954).length < 2 ^ (prefixWord ++ tailWord_2037954).sum := by decide
  have hdescent : baseEnd_2037954 < baseStart_2037954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037978 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 1, 6]
def baseStart_2037978 : Nat := 118140960795 + 2037978 * 2 ^ 59
def prefixEnd_2037978 : Nat := 4983230072969 + 3 ^ 40 * 2037978 * 2
def baseEnd_2037978 : Nat := 697641518192488423601677

theorem tailTrace_2037978 : CollatzResearch.WordTrace tailWord_2037978 prefixEnd_2037978 697641518192488423601677 := by
  unfold tailWord_2037978
  simp only [CollatzResearch.WordTrace]
  refine ⟨18582791052690309944280647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49554109473840826518081725 18582791052690309944280647)
  ·
    refine ⟨27874186579035464916420971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18582791052690309944280647 27874186579035464916420971)
    ·
      refine ⟨41811279868553197374631457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27874186579035464916420971 41811279868553197374631457)
      ·
        refine ⟨31358459901414898030973593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41811279868553197374631457 31358459901414898030973593)
        ·
          refine ⟨23518844926061173523230195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31358459901414898030973593 23518844926061173523230195)
          ·
            refine ⟨35278267389091760284845293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23518844926061173523230195 35278267389091760284845293)
            ·
              refine ⟨13229350270909410106816985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35278267389091760284845293 13229350270909410106816985)
              ·
                refine ⟨9922012703182057580112739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13229350270909410106816985 9922012703182057580112739)
                ·
                  refine ⟨14883019054773086370169109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9922012703182057580112739 14883019054773086370169109)
                  ·
                    refine ⟨697641518192488423601677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14883019054773086370169109 697641518192488423601677)
                    ·
                      rfl

theorem cell22_2037978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_2037978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2037978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2037978 prefixEnd_2037978 := by exact prefixLift 2037978
  have htrace : WordTrace (prefixWord ++ tailWord_2037978) baseStart_2037978 baseEnd_2037978 := by
    simpa [prefixWord, tailWord_2037978, baseEnd_2037978] using wordTrace_append hprefix tailTrace_2037978
  have hstable : (prefixWord ++ tailWord_2037978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037978).length < 2 ^ (prefixWord ++ tailWord_2037978).sum := by decide
  have hdescent : baseEnd_2037978 < baseStart_2037978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038100 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 8]
def baseStart_2038100 : Nat := 118140960795 + 2038100 * 2 ^ 59
def prefixEnd_2038100 : Nat := 4983230072969 + 3 ^ 40 * 2038100 * 2
def baseEnd_2038100 : Nat := 232561093761906924017101

theorem tailTrace_2038100 : CollatzResearch.WordTrace tailWord_2038100 prefixEnd_2038100 232561093761906924017101 := by
  unfold tailWord_2038100
  simp only [CollatzResearch.WordTrace]
  refine ⟨37167806958159627306531877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49557075944212836408709169 37167806958159627306531877)
  ·
    refine ⟨6968963804654930119974727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37167806958159627306531877 6968963804654930119974727)
    ·
      refine ⟨10453445706982395179962091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6968963804654930119974727 10453445706982395179962091)
      ·
        refine ⟨15680168560473592769943137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10453445706982395179962091 15680168560473592769943137)
        ·
          refine ⟨11760126420355194577457353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15680168560473592769943137 11760126420355194577457353)
          ·
            refine ⟨8820094815266395933093015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11760126420355194577457353 8820094815266395933093015)
            ·
              refine ⟨13230142222899593899639523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8820094815266395933093015 13230142222899593899639523)
              ·
                refine ⟨19845213334349390849459285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13230142222899593899639523 19845213334349390849459285)
                ·
                  refine ⟨232561093761906924017101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19845213334349390849459285 232561093761906924017101)
                  ·
                    rfl

theorem cell22_2038100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_2038100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038100 prefixEnd_2038100 := by exact prefixLift 2038100
  have htrace : WordTrace (prefixWord ++ tailWord_2038100) baseStart_2038100 baseEnd_2038100 := by
    simpa [prefixWord, tailWord_2038100, baseEnd_2038100] using wordTrace_append hprefix tailTrace_2038100
  have hstable : (prefixWord ++ tailWord_2038100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038100).length < 2 ^ (prefixWord ++ tailWord_2038100).sum := by decide
  have hdescent : baseEnd_2038100 < baseStart_2038100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038115 : List Nat := [1, 1, 1, 5, 2, 1, 1, 4, 1, 5]
def baseStart_2038115 : Nat := 118140960795 + 2038115 * 2 ^ 59
def prefixEnd_2038115 : Nat := 4983230072969 + 3 ^ 40 * 2038115 * 2
def baseEnd_2038115 : Nat := 697688416092265732926257

theorem tailTrace_2038115 : CollatzResearch.WordTrace tailWord_2038115 prefixEnd_2038115 697688416092265732926257 := by
  unfold tailWord_2038115
  simp only [CollatzResearch.WordTrace]
  refine ⟨74336161011264912174859799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49557440674176608116573199 74336161011264912174859799)
  ·
    refine ⟨111504241516897368262289699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74336161011264912174859799 111504241516897368262289699)
    ·
      refine ⟨167256362275346052393434549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111504241516897368262289699 167256362275346052393434549)
      ·
        refine ⟨15680283963313692411884489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167256362275346052393434549 15680283963313692411884489)
        ·
          refine ⟨11760212972485269308913367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15680283963313692411884489 11760212972485269308913367)
          ·
            refine ⟨17640319458727903963370051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11760212972485269308913367 17640319458727903963370051)
            ·
              refine ⟨26460479188091855945055077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17640319458727903963370051 26460479188091855945055077)
              ·
                refine ⟨4961339847767222989697827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26460479188091855945055077 4961339847767222989697827)
                ·
                  refine ⟨7442009771650834484546741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4961339847767222989697827 7442009771650834484546741)
                  ·
                    refine ⟨697688416092265732926257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7442009771650834484546741 697688416092265732926257)
                    ·
                      rfl

theorem cell22_2038115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 5].length) (baseStart_2038115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038115 prefixEnd_2038115 := by exact prefixLift 2038115
  have htrace : WordTrace (prefixWord ++ tailWord_2038115) baseStart_2038115 baseEnd_2038115 := by
    simpa [prefixWord, tailWord_2038115, baseEnd_2038115] using wordTrace_append hprefix tailTrace_2038115
  have hstable : (prefixWord ++ tailWord_2038115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038115).length < 2 ^ (prefixWord ++ tailWord_2038115).sum := by decide
  have hdescent : baseEnd_2038115 < baseStart_2038115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038117 : List Nat := [1, 3, 1, 3, 1, 3, 1, 5, 4]
def baseStart_2038117 : Nat := 118140960795 + 2038117 * 2 ^ 59
def prefixEnd_2038117 : Nat := 4983230072969 + 3 ^ 40 * 2038117 * 2
def baseEnd_2038117 : Nat := 232563033577712798125417

theorem tailTrace_2038117 : CollatzResearch.WordTrace tailWord_2038117 prefixEnd_2038117 232563033577712798125417 := by
  unfold tailWord_2038117
  simp only [CollatzResearch.WordTrace]
  refine ⟨74336233957257666516432605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49557489304838444344288403 74336233957257666516432605)
  ·
    refine ⟨27876087733971624943662227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74336233957257666516432605 27876087733971624943662227)
    ·
      refine ⟨41814131600957437415493341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27876087733971624943662227 41814131600957437415493341)
      ·
        refine ⟨15680299350359039030810003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41814131600957437415493341 15680299350359039030810003)
        ·
          refine ⟨23520449025538558546215005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15680299350359039030810003 23520449025538558546215005)
          ·
            refine ⟨8820168384576959454830627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23520449025538558546215005 8820168384576959454830627)
            ·
              refine ⟨13230252576865439182245941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8820168384576959454830627 13230252576865439182245941)
              ·
                refine ⟨1240336179081134923335557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13230252576865439182245941 1240336179081134923335557)
                ·
                  refine ⟨232563033577712798125417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1240336179081134923335557 232563033577712798125417)
                  ·
                    rfl

theorem cell22_2038117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_2038117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038117 prefixEnd_2038117 := by exact prefixLift 2038117
  have htrace : WordTrace (prefixWord ++ tailWord_2038117) baseStart_2038117 baseEnd_2038117 := by
    simpa [prefixWord, tailWord_2038117, baseEnd_2038117] using wordTrace_append hprefix tailTrace_2038117
  have hstable : (prefixWord ++ tailWord_2038117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038117).length < 2 ^ (prefixWord ++ tailWord_2038117).sum := by decide
  have hdescent : baseEnd_2038117 < baseStart_2038117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038119 : List Nat := [1, 1, 5, 1, 3, 1, 4, 1, 1, 4]
def baseStart_2038119 : Nat := 118140960795 + 2038119 * 2 ^ 59
def prefixEnd_2038119 : Nat := 4983230072969 + 3 ^ 40 * 2038119 * 2
def baseEnd_2038119 : Nat := 697689785374011055826245

theorem tailTrace_2038119 : CollatzResearch.WordTrace tailWord_2038119 prefixEnd_2038119 697689785374011055826245 := by
  unfold tailWord_2038119
  simp only [CollatzResearch.WordTrace]
  refine ⟨74336306903250420858005411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49557537935500280572003607 74336306903250420858005411)
  ·
    refine ⟨111504460354875631287008117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74336306903250420858005411 111504460354875631287008117)
    ·
      refine ⟨10453543158269590433157011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111504460354875631287008117 10453543158269590433157011)
      ·
        refine ⟨15680314737404385649735517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10453543158269590433157011 15680314737404385649735517)
        ·
          refine ⟨5880118026526644618650819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15680314737404385649735517 5880118026526644618650819)
          ·
            refine ⟨8820177039789966927976229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5880118026526644618650819 8820177039789966927976229)
            ·
              refine ⟨1653783194960618798995543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8820177039789966927976229 1653783194960618798995543)
              ·
                refine ⟨2480674792440928198493315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1653783194960618798995543 2480674792440928198493315)
                ·
                  refine ⟨3721012188661392297739973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2480674792440928198493315 3721012188661392297739973)
                  ·
                    refine ⟨697689785374011055826245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3721012188661392297739973 697689785374011055826245)
                    ·
                      rfl

theorem cell22_2038119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_2038119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038119 prefixEnd_2038119 := by exact prefixLift 2038119
  have htrace : WordTrace (prefixWord ++ tailWord_2038119) baseStart_2038119 baseEnd_2038119 := by
    simpa [prefixWord, tailWord_2038119, baseEnd_2038119] using wordTrace_append hprefix tailTrace_2038119
  have hstable : (prefixWord ++ tailWord_2038119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038119).length < 2 ^ (prefixWord ++ tailWord_2038119).sum := by decide
  have hdescent : baseEnd_2038119 < baseStart_2038119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038196 : List Nat := [2, 5, 2, 2, 1, 1, 2, 7]
def baseStart_2038196 : Nat := 118140960795 + 2038196 * 2 ^ 59
def prefixEnd_2038196 : Nat := 4983230072969 + 3 ^ 40 * 2038196 * 2
def baseEnd_2038196 : Nat := 77524016005289835739001

theorem tailTrace_2038196 : CollatzResearch.WordTrace tailWord_2038196 prefixEnd_2038196 77524016005289835739001 := by
  unfold tailWord_2038196
  simp only [CollatzResearch.WordTrace]
  refine ⟨37169557661985731504279221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49559410215980975339038961 37169557661985731504279221)
  ·
    refine ⟨3484646030811162328526177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37169557661985731504279221 3484646030811162328526177)
    ·
      refine ⟨2613484523108371746394633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3484646030811162328526177 2613484523108371746394633)
      ·
        refine ⟨1960113392331278809795975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2613484523108371746394633 1960113392331278809795975)
        ·
          refine ⟨2940170088496918214693963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1960113392331278809795975 2940170088496918214693963)
          ·
            refine ⟨4410255132745377322040945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940170088496918214693963 4410255132745377322040945)
            ·
              refine ⟨3307691349559032991530709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4410255132745377322040945 3307691349559032991530709)
              ·
                refine ⟨77524016005289835739001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3307691349559032991530709 77524016005289835739001)
                ·
                  rfl

theorem cell22_2038196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 7].length) (baseStart_2038196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038196 prefixEnd_2038196 := by exact prefixLift 2038196
  have htrace : WordTrace (prefixWord ++ tailWord_2038196) baseStart_2038196 baseEnd_2038196 := by
    simpa [prefixWord, tailWord_2038196, baseEnd_2038196] using wordTrace_append hprefix tailTrace_2038196
  have hstable : (prefixWord ++ tailWord_2038196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038196).length < 2 ^ (prefixWord ++ tailWord_2038196).sum := by decide
  have hdescent : baseEnd_2038196 < baseStart_2038196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038245 : List Nat := [1, 3, 1, 5, 2, 2, 2, 2, 1, 3]
def baseStart_2038245 : Nat := 118140960795 + 2038245 * 2 ^ 59
def prefixEnd_2038245 : Nat := 4983230072969 + 3 ^ 40 * 2038245 * 2
def baseEnd_2038245 : Nat := 697732917748988727175859

theorem tailTrace_2038245 : CollatzResearch.WordTrace tailWord_2038245 prefixEnd_2038245 697732917748988727175859 := by
  unfold tailWord_2038245
  simp only [CollatzResearch.WordTrace]
  refine ⟨74340902500793944377092189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49560601667195962918061459 74340902500793944377092189)
  ·
    refine ⟨27877838437797729141409571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74340902500793944377092189 27877838437797729141409571)
    ·
      refine ⟨41816757656696593712114357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27877838437797729141409571 41816757656696593712114357)
      ·
        refine ⟨3920321030315305660510721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41816757656696593712114357 3920321030315305660510721)
        ·
          refine ⟨2940240772736479245383041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3920321030315305660510721 2940240772736479245383041)
          ·
            refine ⟨2205180579552359434037281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2940240772736479245383041 2205180579552359434037281)
            ·
              refine ⟨1653885434664269575527961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2205180579552359434037281 1653885434664269575527961)
              ·
                refine ⟨1240414075998202181645971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1653885434664269575527961 1240414075998202181645971)
                ·
                  refine ⟨1860621113997303272468957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1240414075998202181645971 1860621113997303272468957)
                  ·
                    refine ⟨697732917748988727175859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1860621113997303272468957 697732917748988727175859)
                    ·
                      rfl

theorem cell22_2038245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 1, 3].length) (baseStart_2038245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038245 prefixEnd_2038245 := by exact prefixLift 2038245
  have htrace : WordTrace (prefixWord ++ tailWord_2038245) baseStart_2038245 baseEnd_2038245 := by
    simpa [prefixWord, tailWord_2038245, baseEnd_2038245] using wordTrace_append hprefix tailTrace_2038245
  have hstable : (prefixWord ++ tailWord_2038245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038245).length < 2 ^ (prefixWord ++ tailWord_2038245).sum := by decide
  have hdescent : baseEnd_2038245 < baseStart_2038245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038282 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 1, 6]
def baseStart_2038282 : Nat := 118140960795 + 2038282 * 2 ^ 59
def prefixEnd_2038282 : Nat := 4983230072969 + 3 ^ 40 * 2038282 * 2
def baseEnd_2038282 : Nat := 697745583605132964000745

theorem tailTrace_2038282 : CollatzResearch.WordTrace tailWord_2038282 prefixEnd_2038282 697745583605132964000745 := by
  unfold tailWord_2038282
  simp only [CollatzResearch.WordTrace]
  refine ⟨18585563000414974924047275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49561501334439933130792733 18585563000414974924047275)
  ·
    refine ⟨27878344500622462386070913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18585563000414974924047275 27878344500622462386070913)
    ·
      refine ⟨20908758375466846789553185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27878344500622462386070913 20908758375466846789553185)
      ·
        refine ⟨15681568781600135092164889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20908758375466846789553185 15681568781600135092164889)
        ·
          refine ⟨11761176586200101319123667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15681568781600135092164889 11761176586200101319123667)
          ·
            refine ⟨17641764879300151978685501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11761176586200101319123667 17641764879300151978685501)
            ·
              refine ⟨6615661829737556992007063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17641764879300151978685501 6615661829737556992007063)
              ·
                refine ⟨9923492744606335488010595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6615661829737556992007063 9923492744606335488010595)
                ·
                  refine ⟨14885239116909503232015893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9923492744606335488010595 14885239116909503232015893)
                  ·
                    refine ⟨697745583605132964000745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14885239116909503232015893 697745583605132964000745)
                    ·
                      rfl

theorem cell22_2038282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_2038282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038282 prefixEnd_2038282 := by exact prefixLift 2038282
  have htrace : WordTrace (prefixWord ++ tailWord_2038282) baseStart_2038282 baseEnd_2038282 := by
    simpa [prefixWord, tailWord_2038282, baseEnd_2038282] using wordTrace_append hprefix tailTrace_2038282
  have hstable : (prefixWord ++ tailWord_2038282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038282).length < 2 ^ (prefixWord ++ tailWord_2038282).sum := by decide
  have hdescent : baseEnd_2038282 < baseStart_2038282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038286 : List Nat := [4, 1, 1, 2, 3, 2, 2, 3, 4]
def baseStart_2038286 : Nat := 118140960795 + 2038286 * 2 ^ 59
def prefixEnd_2038286 : Nat := 4983230072969 + 3 ^ 40 * 2038286 * 2
def baseEnd_2038286 : Nat := 232582317628959428966911

theorem tailTrace_2038286 : CollatzResearch.WordTrace tailWord_2038286 prefixEnd_2038286 232582317628959428966911 := by
  unfold tailWord_2038286
  simp only [CollatzResearch.WordTrace]
  refine ⟨9292799736705676047416839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49561598595763605586223141 9292799736705676047416839)
  ·
    refine ⟨13939199605058514071125259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9292799736705676047416839 13939199605058514071125259)
    ·
      refine ⟨20908799407587771106687889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13939199605058514071125259 20908799407587771106687889)
      ·
        refine ⟨15681599555690828330015917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20908799407587771106687889 15681599555690828330015917)
        ·
          refine ⟨5880599833384060623755969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15681599555690828330015917 5880599833384060623755969)
          ·
            refine ⟨4410449875038045467816977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5880599833384060623755969 4410449875038045467816977)
            ·
              refine ⟨3307837406278534100862733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4410449875038045467816977 3307837406278534100862733)
              ·
                refine ⟨1240439027354450287823525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3307837406278534100862733 1240439027354450287823525)
                ·
                  refine ⟨232582317628959428966911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1240439027354450287823525 232582317628959428966911)
                  ·
                    rfl

theorem cell22_2038286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_2038286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038286 prefixEnd_2038286 := by exact prefixLift 2038286
  have htrace : WordTrace (prefixWord ++ tailWord_2038286) baseStart_2038286 baseEnd_2038286 := by
    simpa [prefixWord, tailWord_2038286, baseEnd_2038286] using wordTrace_append hprefix tailTrace_2038286
  have hstable : (prefixWord ++ tailWord_2038286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038286).length < 2 ^ (prefixWord ++ tailWord_2038286).sum := by decide
  have hdescent : baseEnd_2038286 < baseStart_2038286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038301 : List Nat := [1, 4, 2, 2, 1, 2, 3, 2, 2, 3]
def baseStart_2038301 : Nat := 118140960795 + 2038301 * 2 ^ 59
def prefixEnd_2038301 : Nat := 4983230072969 + 3 ^ 40 * 2038301 * 2
def baseEnd_2038301 : Nat := 697752087693423247775687

theorem tailTrace_2038301 : CollatzResearch.WordTrace tailWord_2038301 prefixEnd_2038301 697752087693423247775687 := by
  unfold tailWord_2038301
  simp only [CollatzResearch.WordTrace]
  refine ⟨74342944988591065941130757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49561963325727377294087171 74342944988591065941130757)
  ·
    refine ⟨13939302185360824863962017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74342944988591065941130757 13939302185360824863962017)
    ·
      refine ⟨10454476639020618647971513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13939302185360824863962017 10454476639020618647971513)
      ·
        refine ⟨7840857479265463985978635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10454476639020618647971513 7840857479265463985978635)
        ·
          refine ⟨11761286218898195978967953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7840857479265463985978635 11761286218898195978967953)
          ·
            refine ⟨8820964664173646984225965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11761286218898195978967953 8820964664173646984225965)
            ·
              refine ⟨3307861749065117619084737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8820964664173646984225965 3307861749065117619084737)
              ·
                refine ⟨2480896311798838214313553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3307861749065117619084737 2480896311798838214313553)
                ·
                  refine ⟨1860672233849128660735165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2480896311798838214313553 1860672233849128660735165)
                  ·
                    refine ⟨697752087693423247775687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1860672233849128660735165 697752087693423247775687)
                    ·
                      rfl

theorem cell22_2038301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_2038301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038301 prefixEnd_2038301 := by exact prefixLift 2038301
  have htrace : WordTrace (prefixWord ++ tailWord_2038301) baseStart_2038301 baseEnd_2038301 := by
    simpa [prefixWord, tailWord_2038301, baseEnd_2038301] using wordTrace_append hprefix tailTrace_2038301
  have hstable : (prefixWord ++ tailWord_2038301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038301).length < 2 ^ (prefixWord ++ tailWord_2038301).sum := by decide
  have hdescent : baseEnd_2038301 < baseStart_2038301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038318 : List Nat := [4, 1, 3, 1, 4, 1, 1, 1, 1, 5]
def baseStart_2038318 : Nat := 118140960795 + 2038318 * 2 ^ 59
def prefixEnd_2038318 : Nat := 4983230072969 + 3 ^ 40 * 2038318 * 2
def baseEnd_2038318 : Nat := 697757907140840870100635

theorem tailTrace_2038318 : CollatzResearch.WordTrace tailWord_2038318 prefixEnd_2038318 697757907140840870100635 := by
  unfold tailWord_2038318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9292945628691184730562451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49562376686352985229666405 9292945628691184730562451)
  ·
    refine ⟨13939418443036777095843677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9292945628691184730562451 13939418443036777095843677)
    ·
      refine ⟨5227281916138791410941379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13939418443036777095843677 5227281916138791410941379)
      ·
        refine ⟨7840922874208187116412069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5227281916138791410941379 7840922874208187116412069)
        ·
          refine ⟨1470173038914035084327263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7840922874208187116412069 1470173038914035084327263)
          ·
            refine ⟨2205259558371052626490895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470173038914035084327263 2205259558371052626490895)
            ·
              refine ⟨3307889337556578939736343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205259558371052626490895 3307889337556578939736343)
              ·
                refine ⟨4961834006334868409604515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3307889337556578939736343 4961834006334868409604515)
                ·
                  refine ⟨7442751009502302614406773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4961834006334868409604515 7442751009502302614406773)
                  ·
                    refine ⟨697757907140840870100635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7442751009502302614406773 697757907140840870100635)
                    ·
                      rfl

theorem cell22_2038318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_2038318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038318 prefixEnd_2038318 := by exact prefixLift 2038318
  have htrace : WordTrace (prefixWord ++ tailWord_2038318) baseStart_2038318 baseEnd_2038318 := by
    simpa [prefixWord, tailWord_2038318, baseEnd_2038318] using wordTrace_append hprefix tailTrace_2038318
  have hstable : (prefixWord ++ tailWord_2038318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038318).length < 2 ^ (prefixWord ++ tailWord_2038318).sum := by decide
  have hdescent : baseEnd_2038318 < baseStart_2038318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038329 : List Nat := [1, 2, 1, 5, 1, 1, 1, 4, 3, 3]
def baseStart_2038329 : Nat := 118140960795 + 2038329 * 2 ^ 59
def prefixEnd_2038329 : Nat := 4983230072969 + 3 ^ 40 * 2038329 * 2
def baseEnd_2038329 : Nat := 697761672665640508075601

theorem tailTrace_2038329 : CollatzResearch.WordTrace tailWord_2038329 prefixEnd_2038329 697761672665640508075601 := by
  unfold tailWord_2038329
  simp only [CollatzResearch.WordTrace]
  refine ⟨74343966232489626723150041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49562644154993084482100027 74343966232489626723150041)
  ·
    refine ⟨55757974674367220042362531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74343966232489626723150041 55757974674367220042362531)
    ·
      refine ⟨83636962011550830063543797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55757974674367220042362531 83636962011550830063543797)
      ·
        refine ⟨7840965188582890318457231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83636962011550830063543797 7840965188582890318457231)
        ·
          refine ⟨11761447782874335477685847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7840965188582890318457231 11761447782874335477685847)
          ·
            refine ⟨17642171674311503216528771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11761447782874335477685847 17642171674311503216528771)
            ·
              refine ⟨26463257511467254824793157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17642171674311503216528771 26463257511467254824793157)
              ·
                refine ⟨4961860783400110279648717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26463257511467254824793157 4961860783400110279648717)
                ·
                  refine ⟨1860697793775041354868269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4961860783400110279648717 1860697793775041354868269)
                  ·
                    refine ⟨697761672665640508075601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1860697793775041354868269 697761672665640508075601)
                    ·
                      rfl

theorem cell22_2038329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 3].length) (baseStart_2038329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038329 prefixEnd_2038329 := by exact prefixLift 2038329
  have htrace : WordTrace (prefixWord ++ tailWord_2038329) baseStart_2038329 baseEnd_2038329 := by
    simpa [prefixWord, tailWord_2038329, baseEnd_2038329] using wordTrace_append hprefix tailTrace_2038329
  have hstable : (prefixWord ++ tailWord_2038329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038329).length < 2 ^ (prefixWord ++ tailWord_2038329).sum := by decide
  have hdescent : baseEnd_2038329 < baseStart_2038329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038357 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 4, 5]
def baseStart_2038357 : Nat := 118140960795 + 2038357 * 2 ^ 59
def prefixEnd_2038357 : Nat := 4983230072969 + 3 ^ 40 * 2038357 * 2
def baseEnd_2038357 : Nat := 697771257637857768375515

theorem tailTrace_2038357 : CollatzResearch.WordTrace tailWord_2038357 prefixEnd_2038357 697771257637857768375515 := by
  unfold tailWord_2038357
  simp only [CollatzResearch.WordTrace]
  refine ⟨74344987476388187505169325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49563324984258791670112883 74344987476388187505169325)
  ·
    refine ⟨27879370303645570314438497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74344987476388187505169325 27879370303645570314438497)
    ·
      refine ⟨20909527727734177735828873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27879370303645570314438497 20909527727734177735828873)
      ·
        refine ⟨15682145795800633301871655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20909527727734177735828873 15682145795800633301871655)
        ·
          refine ⟨23523218693700949952807483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15682145795800633301871655 23523218693700949952807483)
          ·
            refine ⟨35284828040551424929211225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23523218693700949952807483 35284828040551424929211225)
            ·
              refine ⟨26463621030413568696908419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35284828040551424929211225 26463621030413568696908419)
              ·
                refine ⟨39695431545620353045362629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26463621030413568696908419 39695431545620353045362629)
                ·
                  refine ⟨7442893414803816196005493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39695431545620353045362629 7442893414803816196005493)
                  ·
                    refine ⟨697771257637857768375515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7442893414803816196005493 697771257637857768375515)
                    ·
                      rfl

theorem cell22_2038357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_2038357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038357 prefixEnd_2038357 := by exact prefixLift 2038357
  have htrace : WordTrace (prefixWord ++ tailWord_2038357) baseStart_2038357 baseEnd_2038357 := by
    simpa [prefixWord, tailWord_2038357, baseEnd_2038357] using wordTrace_append hprefix tailTrace_2038357
  have hstable : (prefixWord ++ tailWord_2038357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038357).length < 2 ^ (prefixWord ++ tailWord_2038357).sum := by decide
  have hdescent : baseEnd_2038357 < baseStart_2038357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038376 : List Nat := [2, 1, 4, 3, 2, 1, 1, 3, 5]
def baseStart_2038376 : Nat := 118140960795 + 2038376 * 2 ^ 59
def prefixEnd_2038376 : Nat := 4983230072969 + 3 ^ 40 * 2038376 * 2
def baseEnd_2038376 : Nat := 232592587242049350716819

theorem tailTrace_2038376 : CollatzResearch.WordTrace tailWord_2038376 prefixEnd_2038376 232592587242049350716819 := by
  unfold tailWord_2038376
  simp only [CollatzResearch.WordTrace]
  refine ⟨37172840231659676875055491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49563786975546235833407321 37172840231659676875055491)
  ·
    refine ⟨55759260347489515312583237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37172840231659676875055491 55759260347489515312583237)
    ·
      refine ⟨10454861315154284121109357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55759260347489515312583237 10454861315154284121109357)
      ·
        refine ⟨3920572993182856545416009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10454861315154284121109357 3920572993182856545416009)
        ·
          refine ⟨2940429744887142409062007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3920572993182856545416009 2940429744887142409062007)
          ·
            refine ⟨4410644617330713613593011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940429744887142409062007 4410644617330713613593011)
            ·
              refine ⟨6615966925996070420389517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4410644617330713613593011 6615966925996070420389517)
              ·
                refine ⟨2480987597248526407646069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6615966925996070420389517 2480987597248526407646069)
                ·
                  refine ⟨232592587242049350716819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2480987597248526407646069 232592587242049350716819)
                  ·
                    rfl

theorem cell22_2038376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 5].length) (baseStart_2038376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038376 prefixEnd_2038376 := by exact prefixLift 2038376
  have htrace : WordTrace (prefixWord ++ tailWord_2038376) baseStart_2038376 baseEnd_2038376 := by
    simpa [prefixWord, tailWord_2038376, baseEnd_2038376] using wordTrace_append hprefix tailTrace_2038376
  have hstable : (prefixWord ++ tailWord_2038376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038376).length < 2 ^ (prefixWord ++ tailWord_2038376).sum := by decide
  have hdescent : baseEnd_2038376 < baseStart_2038376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038436 : List Nat := [2, 3, 1, 2, 2, 1, 1, 5, 2, 3]
def baseStart_2038436 : Nat := 118140960795 + 2038436 * 2 ^ 59
def prefixEnd_2038436 : Nat := 4983230072969 + 3 ^ 40 * 2038436 * 2
def baseEnd_2038436 : Nat := 697798300952327895650273

theorem tailTrace_2038436 : CollatzResearch.WordTrace tailWord_2038436 prefixEnd_2038436 697798300952327895650273 := by
  unfold tailWord_2038436
  simp only [CollatzResearch.WordTrace]
  refine ⟨37173934421550991998647581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49565245895401322664863441 37173934421550991998647581)
  ·
    refine ⟨13940225408081621999492843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37173934421550991998647581 13940225408081621999492843)
    ·
      refine ⟨20910338112122432999239265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13940225408081621999492843 20910338112122432999239265)
      ·
        refine ⟨15682753584091824749429449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20910338112122432999239265 15682753584091824749429449)
        ·
          refine ⟨11762065188068868562072087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15682753584091824749429449 11762065188068868562072087)
          ·
            refine ⟨17643097782103302843108131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11762065188068868562072087 17643097782103302843108131)
            ·
              refine ⟨26464646673154954264662197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17643097782103302843108131 26464646673154954264662197)
              ·
                refine ⟨2481060625608276962312081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26464646673154954264662197 2481060625608276962312081)
                ·
                  refine ⟨1860795469206207721734061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2481060625608276962312081 1860795469206207721734061)
                  ·
                    refine ⟨697798300952327895650273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1860795469206207721734061 697798300952327895650273)
                    ·
                      rfl

theorem cell22_2038436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_2038436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038436 prefixEnd_2038436 := by exact prefixLift 2038436
  have htrace : WordTrace (prefixWord ++ tailWord_2038436) baseStart_2038436 baseEnd_2038436 := by
    simpa [prefixWord, tailWord_2038436, baseEnd_2038436] using wordTrace_append hprefix tailTrace_2038436
  have hstable : (prefixWord ++ tailWord_2038436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038436).length < 2 ^ (prefixWord ++ tailWord_2038436).sum := by decide
  have hdescent : baseEnd_2038436 < baseStart_2038436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038451 : List Nat := [1, 1, 1, 2, 3, 6, 1, 1, 2, 4]
def baseStart_2038451 : Nat := 118140960795 + 2038451 * 2 ^ 59
def prefixEnd_2038451 : Nat := 4983230072969 + 3 ^ 40 * 2038451 * 2
def baseEnd_2038451 : Nat := 697803435758872856525227

theorem tailTrace_2038451 : CollatzResearch.WordTrace tailWord_2038451 prefixEnd_2038451 697803435758872856525227 := by
  unfold tailWord_2038451
  simp only [CollatzResearch.WordTrace]
  refine ⟨74348415938047641559091207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49565610625365094372727471 74348415938047641559091207)
  ·
    refine ⟨111522623907071462338636811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74348415938047641559091207 111522623907071462338636811)
    ·
      refine ⟨167283935860607193507955217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111522623907071462338636811 167283935860607193507955217)
      ·
        refine ⟨125462951895455395130966413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167283935860607193507955217 125462951895455395130966413)
        ·
          refine ⟨47048606960795773174112405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125462951895455395130966413 47048606960795773174112405)
          ·
            refine ⟨2205403451287301867536519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47048606960795773174112405 2205403451287301867536519)
            ·
              refine ⟨3308105176930952801304779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205403451287301867536519 3308105176930952801304779)
              ·
                refine ⟨4962157765396429201957169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308105176930952801304779 4962157765396429201957169)
                ·
                  refine ⟨3721618324047321901467877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4962157765396429201957169 3721618324047321901467877)
                  ·
                    refine ⟨697803435758872856525227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3721618324047321901467877 697803435758872856525227)
                    ·
                      rfl

theorem cell22_2038451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 4].length) (baseStart_2038451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038451 prefixEnd_2038451 := by exact prefixLift 2038451
  have htrace : WordTrace (prefixWord ++ tailWord_2038451) baseStart_2038451 baseEnd_2038451 := by
    simpa [prefixWord, tailWord_2038451, baseEnd_2038451] using wordTrace_append hprefix tailTrace_2038451
  have hstable : (prefixWord ++ tailWord_2038451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038451).length < 2 ^ (prefixWord ++ tailWord_2038451).sum := by decide
  have hdescent : baseEnd_2038451 < baseStart_2038451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038481 : List Nat := [1, 2, 2, 1, 2, 3, 4, 1, 3, 3]
def baseStart_2038481 : Nat := 118140960795 + 2038481 * 2 ^ 59
def prefixEnd_2038481 : Nat := 4983230072969 + 3 ^ 40 * 2038481 * 2
def baseEnd_2038481 : Nat := 697813705371962778275135

theorem tailTrace_2038481 : CollatzResearch.WordTrace tailWord_2038481 prefixEnd_2038481 697813705371962778275135 := by
  unfold tailWord_2038481
  simp only [CollatzResearch.WordTrace]
  refine ⟨74349510127938956682683297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49566340085292637788455531 74349510127938956682683297)
  ·
    refine ⟨55762132595954217512012473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74349510127938956682683297 55762132595954217512012473)
    ·
      refine ⟨41821599446965663134009355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55762132595954217512012473 41821599446965663134009355)
      ·
        refine ⟨62732399170448494701014033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41821599446965663134009355 62732399170448494701014033)
        ·
          refine ⟨47049299377836371025760525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62732399170448494701014033 47049299377836371025760525)
          ·
            refine ⟨17643487266688639134660197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47049299377836371025760525 17643487266688639134660197)
            ·
              refine ⟨3308153862504119837748787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17643487266688639134660197 3308153862504119837748787)
              ·
                refine ⟨4962230793756179756623181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308153862504119837748787 4962230793756179756623181)
                ·
                  refine ⟨1860836547658567408733693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4962230793756179756623181 1860836547658567408733693)
                  ·
                    refine ⟨697813705371962778275135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1860836547658567408733693 697813705371962778275135)
                    ·
                      rfl

theorem cell22_2038481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_2038481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038481 prefixEnd_2038481 := by exact prefixLift 2038481
  have htrace : WordTrace (prefixWord ++ tailWord_2038481) baseStart_2038481 baseEnd_2038481 := by
    simpa [prefixWord, tailWord_2038481, baseEnd_2038481] using wordTrace_append hprefix tailTrace_2038481
  have hstable : (prefixWord ++ tailWord_2038481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038481).length < 2 ^ (prefixWord ++ tailWord_2038481).sum := by decide
  have hdescent : baseEnd_2038481 < baseStart_2038481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038569 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 6, 4]
def baseStart_2038569 : Nat := 118140960795 + 2038569 * 2 ^ 59
def prefixEnd_2038569 : Nat := 4983230072969 + 3 ^ 40 * 2038569 * 2
def baseEnd_2038569 : Nat := 697843829570359882074865

theorem tailTrace_2038569 : CollatzResearch.WordTrace tailWord_2038569 prefixEnd_2038569 697843829570359882074865 := by
  unfold tailWord_2038569
  simp only [CollatzResearch.WordTrace]
  refine ⟨74352719751620147711886761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49568479834413431807924507 74352719751620147711886761)
  ·
    refine ⟨55764539813715110783915071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74352719751620147711886761 55764539813715110783915071)
    ·
      refine ⟨83646809720572666175872607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55764539813715110783915071 83646809720572666175872607)
      ·
        refine ⟨125470214580858999263808911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83646809720572666175872607 125470214580858999263808911)
        ·
          refine ⟨188205321871288498895713367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125470214580858999263808911 188205321871288498895713367)
          ·
            refine ⟨282307982806932748343570051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188205321871288498895713367 282307982806932748343570051)
            ·
              refine ⟨423461974210399122515355077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282307982806932748343570051 423461974210399122515355077)
              ·
                refine ⟨79399120164449835471629077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423461974210399122515355077 79399120164449835471629077)
                ·
                  refine ⟨3721833757708586037732613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79399120164449835471629077 3721833757708586037732613)
                  ·
                    refine ⟨697843829570359882074865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3721833757708586037732613 697843829570359882074865)
                    ·
                      rfl

theorem cell22_2038569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_2038569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038569 prefixEnd_2038569 := by exact prefixLift 2038569
  have htrace : WordTrace (prefixWord ++ tailWord_2038569) baseStart_2038569 baseEnd_2038569 := by
    simpa [prefixWord, tailWord_2038569, baseEnd_2038569] using wordTrace_append hprefix tailTrace_2038569
  have hstable : (prefixWord ++ tailWord_2038569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038569).length < 2 ^ (prefixWord ++ tailWord_2038569).sum := by decide
  have hdescent : baseEnd_2038569 < baseStart_2038569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038590 : List Nat := [4, 2, 1, 2, 3, 1, 1, 4, 4]
def baseStart_2038590 : Nat := 118140960795 + 2038590 * 2 ^ 59
def prefixEnd_2038590 : Nat := 4983230072969 + 3 ^ 40 * 2038590 * 2
def baseEnd_2038590 : Nat := 232617006099840942433267

theorem tailTrace_2038590 : CollatzResearch.WordTrace tailWord_2038590 prefixEnd_2038590 232617006099840942433267 := by
  unfold tailWord_2038590
  simp only [CollatzResearch.WordTrace]
  refine ⟨9294185710568008537300153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49568990456362712198934149 9294185710568008537300153)
  ·
    refine ⟨6970639282926006402975115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9294185710568008537300153 6970639282926006402975115)
    ·
      refine ⟨10455958924389009604462673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6970639282926006402975115 10455958924389009604462673)
      ·
        refine ⟨7841969193291757203347005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10455958924389009604462673 7841969193291757203347005)
        ·
          refine ⟨2940738447484408951255127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7841969193291757203347005 2940738447484408951255127)
          ·
            refine ⟨4411107671226613426882691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940738447484408951255127 4411107671226613426882691)
            ·
              refine ⟨6616661506839920140324037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4411107671226613426882691 6616661506839920140324037)
              ·
                refine ⟨1240624032532485026310757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6616661506839920140324037 1240624032532485026310757)
                ·
                  refine ⟨232617006099840942433267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1240624032532485026310757 232617006099840942433267)
                  ·
                    rfl

theorem cell22_2038590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_2038590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038590 prefixEnd_2038590 := by exact prefixLift 2038590
  have htrace : WordTrace (prefixWord ++ tailWord_2038590) baseStart_2038590 baseEnd_2038590 := by
    simpa [prefixWord, tailWord_2038590, baseEnd_2038590] using wordTrace_append hprefix tailTrace_2038590
  have hstable : (prefixWord ++ tailWord_2038590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038590).length < 2 ^ (prefixWord ++ tailWord_2038590).sum := by decide
  have hdescent : baseEnd_2038590 < baseStart_2038590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038599 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 2, 7]
def baseStart_2038599 : Nat := 118140960795 + 2038599 * 2 ^ 59
def prefixEnd_2038599 : Nat := 4983230072969 + 3 ^ 40 * 2038599 * 2
def baseEnd_2038599 : Nat := 697854099183449803824773

theorem tailTrace_2038599 : CollatzResearch.WordTrace tailWord_2038599 prefixEnd_2038599 697854099183449803824773 := by
  unfold tailWord_2038599
  simp only [CollatzResearch.WordTrace]
  refine ⟨74353813941511462835478851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49569209294340975223652567 74353813941511462835478851)
  ·
    refine ⟨111530720912267194253218277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74353813941511462835478851 111530720912267194253218277)
    ·
      refine ⟨20912010171050098922478427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111530720912267194253218277 20912010171050098922478427)
      ·
        refine ⟨31368015256575148383717641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20912010171050098922478427 31368015256575148383717641)
        ·
          refine ⟨23526011442431361287788231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31368015256575148383717641 23526011442431361287788231)
          ·
            refine ⟨35289017163647041931682347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23526011442431361287788231 35289017163647041931682347)
            ·
              refine ⟨52933525745470562897523521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35289017163647041931682347 52933525745470562897523521)
              ·
                refine ⟨39700144309102922173142641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52933525745470562897523521 39700144309102922173142641)
                ·
                  refine ⟨29775108231827191629856981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39700144309102922173142641 29775108231827191629856981)
                  ·
                    refine ⟨697854099183449803824773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29775108231827191629856981 697854099183449803824773)
                    ·
                      rfl

theorem cell22_2038599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_2038599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038599 prefixEnd_2038599 := by exact prefixLift 2038599
  have htrace : WordTrace (prefixWord ++ tailWord_2038599) baseStart_2038599 baseEnd_2038599 := by
    simpa [prefixWord, tailWord_2038599, baseEnd_2038599] using wordTrace_append hprefix tailTrace_2038599
  have hstable : (prefixWord ++ tailWord_2038599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038599).length < 2 ^ (prefixWord ++ tailWord_2038599).sum := by decide
  have hdescent : baseEnd_2038599 < baseStart_2038599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038601 : List Nat := [1, 2, 1, 1, 2, 7, 1, 7]
def baseStart_2038601 : Nat := 118140960795 + 2038601 * 2 ^ 59
def prefixEnd_2038601 : Nat := 4983230072969 + 3 ^ 40 * 2038601 * 2
def baseEnd_2038601 : Nat := 77539420424924718363863

theorem tailTrace_2038601 : CollatzResearch.WordTrace tailWord_2038601 prefixEnd_2038601 77539420424924718363863 := by
  unfold tailWord_2038601
  simp only [CollatzResearch.WordTrace]
  refine ⟨74353886887504217177051657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49569257925002811451367771 74353886887504217177051657)
  ·
    refine ⟨55765415165628162882788743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74353886887504217177051657 55765415165628162882788743)
    ·
      refine ⟨83648122748442244324183115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55765415165628162882788743 83648122748442244324183115)
      ·
        refine ⟨125472184122663366486274673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83648122748442244324183115 125472184122663366486274673)
        ·
          refine ⟨94104138091997524864706005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125472184122663366486274673 94104138091997524864706005)
          ·
            refine ⟨2205565736531191989016547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 94104138091997524864706005 2205565736531191989016547)
            ·
              refine ⟨3308348604796787983524821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205565736531191989016547 3308348604796787983524821)
              ·
                refine ⟨77539420424924718363863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3308348604796787983524821 77539420424924718363863)
                ·
                  rfl

theorem cell22_2038601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 7].length) (baseStart_2038601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038601 prefixEnd_2038601 := by exact prefixLift 2038601
  have htrace : WordTrace (prefixWord ++ tailWord_2038601) baseStart_2038601 baseEnd_2038601 := by
    simpa [prefixWord, tailWord_2038601, baseEnd_2038601] using wordTrace_append hprefix tailTrace_2038601
  have hstable : (prefixWord ++ tailWord_2038601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038601).length < 2 ^ (prefixWord ++ tailWord_2038601).sum := by decide
  have hdescent : baseEnd_2038601 < baseStart_2038601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038605 : List Nat := [1, 6, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_2038605 : Nat := 118140960795 + 2038605 * 2 ^ 59
def prefixEnd_2038605 : Nat := 4983230072969 + 3 ^ 40 * 2038605 * 2
def baseEnd_2038605 : Nat := 697856153106067788174755

theorem tailTrace_2038605 : CollatzResearch.WordTrace tailWord_2038605 prefixEnd_2038605 697856153106067788174755 := by
  unfold tailWord_2038605
  simp only [CollatzResearch.WordTrace]
  refine ⟨74354032779489725860197269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49569355186326483906798179 74354032779489725860197269)
  ·
    refine ⟨3485345286538580899696747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74354032779489725860197269 3485345286538580899696747)
    ·
      refine ⟨5228017929807871349545121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3485345286538580899696747 5228017929807871349545121)
      ·
        refine ⟨3921013447355903512158841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5228017929807871349545121 3921013447355903512158841)
        ·
          refine ⟨2940760085516927634119131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3921013447355903512158841 2940760085516927634119131)
          ·
            refine ⟨4411140128275391451178697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940760085516927634119131 4411140128275391451178697)
            ·
              refine ⟨3308355096206543588384023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4411140128275391451178697 3308355096206543588384023)
              ·
                refine ⟨4962532644309815382576035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308355096206543588384023 4962532644309815382576035)
                ·
                  refine ⟨7443798966464723073864053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4962532644309815382576035 7443798966464723073864053)
                  ·
                    refine ⟨697856153106067788174755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7443798966464723073864053 697856153106067788174755)
                    ·
                      rfl

theorem cell22_2038605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_2038605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038605 prefixEnd_2038605 := by exact prefixLift 2038605
  have htrace : WordTrace (prefixWord ++ tailWord_2038605) baseStart_2038605 baseEnd_2038605 := by
    simpa [prefixWord, tailWord_2038605, baseEnd_2038605] using wordTrace_append hprefix tailTrace_2038605
  have hstable : (prefixWord ++ tailWord_2038605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038605).length < 2 ^ (prefixWord ++ tailWord_2038605).sum := by decide
  have hdescent : baseEnd_2038605 < baseStart_2038605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038620 : List Nat := [2, 2, 4, 2, 1, 3, 1, 1, 2, 4]
def baseStart_2038620 : Nat := 118140960795 + 2038620 * 2 ^ 59
def prefixEnd_2038620 : Nat := 4983230072969 + 3 ^ 40 * 2038620 * 2
def baseEnd_2038620 : Nat := 697861287912612749049709

theorem tailTrace_2038620 : CollatzResearch.WordTrace tailWord_2038620 prefixEnd_2038620 697861287912612749049709 := by
  unfold tailWord_2038620
  simp only [CollatzResearch.WordTrace]
  refine ⟨37177289937217691710996657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49569719916290255614662209 37177289937217691710996657)
  ·
    refine ⟨27882967452913268783247493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37177289937217691710996657 27882967452913268783247493)
    ·
      refine ⟨5228056397421237896858905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27882967452913268783247493 5228056397421237896858905)
      ·
        refine ⟨3921042298065928422644179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5228056397421237896858905 3921042298065928422644179)
        ·
          refine ⟨5881563447098892633966269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3921042298065928422644179 5881563447098892633966269)
          ·
            refine ⟨2205586292662084737737351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5881563447098892633966269 2205586292662084737737351)
            ·
              refine ⟨3308379438993127106606027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205586292662084737737351 3308379438993127106606027)
              ·
                refine ⟨4962569158489690659909041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308379438993127106606027 4962569158489690659909041)
                ·
                  refine ⟨3721926868867267994931781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4962569158489690659909041 3721926868867267994931781)
                  ·
                    refine ⟨697861287912612749049709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3721926868867267994931781 697861287912612749049709)
                    ·
                      rfl

theorem cell22_2038620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_2038620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038620 prefixEnd_2038620 := by exact prefixLift 2038620
  have htrace : WordTrace (prefixWord ++ tailWord_2038620) baseStart_2038620 baseEnd_2038620 := by
    simpa [prefixWord, tailWord_2038620, baseEnd_2038620] using wordTrace_append hprefix tailTrace_2038620
  have hstable : (prefixWord ++ tailWord_2038620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038620).length < 2 ^ (prefixWord ++ tailWord_2038620).sum := by decide
  have hdescent : baseEnd_2038620 < baseStart_2038620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038661 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 2, 5]
def baseStart_2038661 : Nat := 118140960795 + 2038661 * 2 ^ 59
def prefixEnd_2038661 : Nat := 4983230072969 + 3 ^ 40 * 2038661 * 2
def baseEnd_2038661 : Nat := 697875323050502308774583

theorem tailTrace_2038661 : CollatzResearch.WordTrace tailWord_2038661 prefixEnd_2038661 697875323050502308774583 := by
  unfold tailWord_2038661
  simp only [CollatzResearch.WordTrace]
  refine ⟨74356075267286847424235837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49570716844857898282823891 74356075267286847424235837)
  ·
    refine ⟨27883528225232567784088439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74356075267286847424235837 27883528225232567784088439)
    ·
      refine ⟨41825292337848851676132659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27883528225232567784088439 41825292337848851676132659)
      ·
        refine ⟨62737938506773277514198989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41825292337848851676132659 62737938506773277514198989)
        ·
          refine ⟨23526726940039979067824621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62737938506773277514198989 23526726940039979067824621)
          ·
            refine ⟨8822522602514992150434233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23526726940039979067824621 8822522602514992150434233)
            ·
              refine ⟨6616891951886244112825675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8822522602514992150434233 6616891951886244112825675)
              ·
                refine ⟨9925337927829366169238513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6616891951886244112825675 9925337927829366169238513)
                ·
                  refine ⟨7444003445872024626928885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9925337927829366169238513 7444003445872024626928885)
                  ·
                    refine ⟨697875323050502308774583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7444003445872024626928885 697875323050502308774583)
                    ·
                      rfl

theorem cell22_2038661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_2038661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038661 prefixEnd_2038661 := by exact prefixLift 2038661
  have htrace : WordTrace (prefixWord ++ tailWord_2038661) baseStart_2038661 baseEnd_2038661 := by
    simpa [prefixWord, tailWord_2038661, baseEnd_2038661] using wordTrace_append hprefix tailTrace_2038661
  have hstable : (prefixWord ++ tailWord_2038661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038661).length < 2 ^ (prefixWord ++ tailWord_2038661).sum := by decide
  have hdescent : baseEnd_2038661 < baseStart_2038661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038684 : List Nat := [2, 2, 3, 3, 2, 2, 1, 3, 1, 3]
def baseStart_2038684 : Nat := 118140960795 + 2038684 * 2 ^ 59
def prefixEnd_2038684 : Nat := 4983230072969 + 3 ^ 40 * 2038684 * 2
def baseEnd_2038684 : Nat := 697883196420537915449513

theorem tailTrace_2038684 : CollatzResearch.WordTrace tailWord_2038684 prefixEnd_2038684 697883196420537915449513 := by
  unfold tailWord_2038684
  simp only [CollatzResearch.WordTrace]
  refine ⟨37178457073101761176161553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49571276097469014901548737 37178457073101761176161553)
  ·
    refine ⟨27883842804826320882121165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37178457073101761176161553 27883842804826320882121165)
    ·
      refine ⟨10456441051809870330795437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27883842804826320882121165 10456441051809870330795437)
      ·
        refine ⟨3921165394428701374048289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10456441051809870330795437 3921165394428701374048289)
        ·
          refine ⟨2940874045821526030536217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3921165394428701374048289 2940874045821526030536217)
          ·
            refine ⟨2205655534366144522902163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2940874045821526030536217 2205655534366144522902163)
            ·
              refine ⟨3308483301549216784353245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205655534366144522902163 3308483301549216784353245)
              ·
                refine ⟨1240681238080956294132467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3308483301549216784353245 1240681238080956294132467)
                ·
                  refine ⟨1861021857121434441198701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1240681238080956294132467 1861021857121434441198701)
                  ·
                    refine ⟨697883196420537915449513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1861021857121434441198701 697883196420537915449513)
                    ·
                      rfl

theorem cell22_2038684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_2038684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038684 prefixEnd_2038684 := by exact prefixLift 2038684
  have htrace : WordTrace (prefixWord ++ tailWord_2038684) baseStart_2038684 baseEnd_2038684 := by
    simpa [prefixWord, tailWord_2038684, baseEnd_2038684] using wordTrace_append hprefix tailTrace_2038684
  have hstable : (prefixWord ++ tailWord_2038684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038684).length < 2 ^ (prefixWord ++ tailWord_2038684).sum := by decide
  have hdescent : baseEnd_2038684 < baseStart_2038684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038701 : List Nat := [1, 5, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_2038701 : Nat := 118140960795 + 2038701 * 2 ^ 59
def prefixEnd_2038701 : Nat := 4983230072969 + 3 ^ 40 * 2038701 * 2
def baseEnd_2038701 : Nat := 697889015867955537774461

theorem tailTrace_2038701 : CollatzResearch.WordTrace tailWord_2038701 prefixEnd_2038701 697889015867955537774461 := by
  unfold tailWord_2038701
  simp only [CollatzResearch.WordTrace]
  refine ⟨74357534187141934255691957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49571689458094622837127971 74357534187141934255691957)
  ·
    refine ⟨6971018830044556336471121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74357534187141934255691957 6971018830044556336471121)
    ·
      refine ⟨5228264122533417252353341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6971018830044556336471121 5228264122533417252353341)
      ·
        refine ⟨1960599045950031469632503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5228264122533417252353341 1960599045950031469632503)
        ·
          refine ⟨2940898568925047204448755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1960599045950031469632503 2940898568925047204448755)
          ·
            refine ⟨4411347853387570806673133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940898568925047204448755 4411347853387570806673133)
            ·
              refine ⟨1654255445020339052502425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4411347853387570806673133 1654255445020339052502425)
              ·
                refine ⟨1240691583765254289376819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1654255445020339052502425 1240691583765254289376819)
                ·
                  refine ⟨1861037375647881434065229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1240691583765254289376819 1861037375647881434065229)
                  ·
                    refine ⟨697889015867955537774461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1861037375647881434065229 697889015867955537774461)
                    ·
                      rfl

theorem cell22_2038701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_2038701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038701 prefixEnd_2038701 := by exact prefixLift 2038701
  have htrace : WordTrace (prefixWord ++ tailWord_2038701) baseStart_2038701 baseEnd_2038701 := by
    simpa [prefixWord, tailWord_2038701, baseEnd_2038701] using wordTrace_append hprefix tailTrace_2038701
  have hstable : (prefixWord ++ tailWord_2038701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038701).length < 2 ^ (prefixWord ++ tailWord_2038701).sum := by decide
  have hdescent : baseEnd_2038701 < baseStart_2038701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038723 : List Nat := [1, 1, 1, 3, 1, 1, 2, 7, 2, 3]
def baseStart_2038723 : Nat := 118140960795 + 2038723 * 2 ^ 59
def prefixEnd_2038723 : Nat := 4983230072969 + 3 ^ 40 * 2038723 * 2
def baseEnd_2038723 : Nat := 697896546917554813724393

theorem tailTrace_2038723 : CollatzResearch.WordTrace tailWord_2038723 prefixEnd_2038723 697896546917554813724393 := by
  unfold tailWord_2038723
  simp only [CollatzResearch.WordTrace]
  refine ⟨74358336593062232012992823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49572224395374821341995215 74358336593062232012992823)
  ·
    refine ⟨111537504889593348019489235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74358336593062232012992823 111537504889593348019489235)
    ·
      refine ⟨167306257334390022029233853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111537504889593348019489235 167306257334390022029233853)
      ·
        refine ⟨62739846500396258260962695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167306257334390022029233853 62739846500396258260962695)
        ·
          refine ⟨94109769750594387391444043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62739846500396258260962695 94109769750594387391444043)
          ·
            refine ⟨141164654625891581087166065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94109769750594387391444043 141164654625891581087166065)
            ·
              refine ⟨105873490969418685815374549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141164654625891581087166065 105873490969418685815374549)
              ·
                refine ⟨2481409944595750448797841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 105873490969418685815374549 2481409944595750448797841)
                ·
                  refine ⟨1861057458446812836598381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2481409944595750448797841 1861057458446812836598381)
                  ·
                    refine ⟨697896546917554813724393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1861057458446812836598381 697896546917554813724393)
                    ·
                      rfl

theorem cell22_2038723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 3].length) (baseStart_2038723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038723 prefixEnd_2038723 := by exact prefixLift 2038723
  have htrace : WordTrace (prefixWord ++ tailWord_2038723) baseStart_2038723 baseEnd_2038723 := by
    simpa [prefixWord, tailWord_2038723, baseEnd_2038723] using wordTrace_append hprefix tailTrace_2038723
  have hstable : (prefixWord ++ tailWord_2038723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038723).length < 2 ^ (prefixWord ++ tailWord_2038723).sum := by decide
  have hdescent : baseEnd_2038723 < baseStart_2038723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038768 : List Nat := [2, 1, 1, 1, 3, 2, 1, 5, 3, 3]
def baseStart_2038768 : Nat := 118140960795 + 2038768 * 2 ^ 59
def prefixEnd_2038768 : Nat := 4983230072969 + 3 ^ 40 * 2038768 * 2
def baseEnd_2038768 : Nat := 697911951337189696349255

theorem tailTrace_2038768 : CollatzResearch.WordTrace tailWord_2038768 prefixEnd_2038768 697911951337189696349255 := by
  unfold tailWord_2038768
  simp only [CollatzResearch.WordTrace]
  refine ⟨37179988938949602349190479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49573318585266136465587305 37179988938949602349190479)
  ·
    refine ⟨55769983408424403523785719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37179988938949602349190479 55769983408424403523785719)
    ·
      refine ⟨83654975112636605285678579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55769983408424403523785719 83654975112636605285678579)
      ·
        refine ⟨125482462668954907928517869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83654975112636605285678579 125482462668954907928517869)
        ·
          refine ⟨47055923500858090473194201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125482462668954907928517869 47055923500858090473194201)
          ·
            refine ⟨35291942625643567854895651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47055923500858090473194201 35291942625643567854895651)
            ·
              refine ⟨52937913938465351782343477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35291942625643567854895651 52937913938465351782343477)
              ·
                refine ⟨4962929431731126729594701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52937913938465351782343477 4962929431731126729594701)
                ·
                  refine ⟨1861098536899172523598013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4962929431731126729594701 1861098536899172523598013)
                  ·
                    refine ⟨697911951337189696349255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1861098536899172523598013 697911951337189696349255)
                    ·
                      rfl

theorem cell22_2038768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 3, 3].length) (baseStart_2038768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038768 prefixEnd_2038768 := by exact prefixLift 2038768
  have htrace : WordTrace (prefixWord ++ tailWord_2038768) baseStart_2038768 baseEnd_2038768 := by
    simpa [prefixWord, tailWord_2038768, baseEnd_2038768] using wordTrace_append hprefix tailTrace_2038768
  have hstable : (prefixWord ++ tailWord_2038768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038768).length < 2 ^ (prefixWord ++ tailWord_2038768).sum := by decide
  have hdescent : baseEnd_2038768 < baseStart_2038768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038781 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 9]
def baseStart_2038781 : Nat := 118140960795 + 2038781 * 2 ^ 59
def prefixEnd_2038781 : Nat := 4983230072969 + 3 ^ 40 * 2038781 * 2
def baseEnd_2038781 : Nat := 232638800500953998591405

theorem tailTrace_2038781 : CollatzResearch.WordTrace tailWord_2038781 prefixEnd_2038781 232638800500953998591405 := by
  unfold tailWord_2038781
  simp only [CollatzResearch.WordTrace]
  refine ⟨74360452026852107918604197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49573634684568071945736131 74360452026852107918604197)
  ·
    refine ⟨13942584755034770234738287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74360452026852107918604197 13942584755034770234738287)
    ·
      refine ⟨20913877132552155352107431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13942584755034770234738287 20913877132552155352107431)
      ·
        refine ⟨31370815698828233028161147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20913877132552155352107431 31370815698828233028161147)
        ·
          refine ⟨47056223548242349542241721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31370815698828233028161147 47056223548242349542241721)
          ·
            refine ⟨35292167661181762156681291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47056223548242349542241721 35292167661181762156681291)
            ·
              refine ⟨52938251491772643235021937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35292167661181762156681291 52938251491772643235021937)
              ·
                refine ⟨39703688618829482426266453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52938251491772643235021937 39703688618829482426266453)
                ·
                  refine ⟨232638800500953998591405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39703688618829482426266453 232638800500953998591405)
                  ·
                    rfl

theorem cell22_2038781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_2038781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038781 prefixEnd_2038781 := by exact prefixLift 2038781
  have htrace : WordTrace (prefixWord ++ tailWord_2038781) baseStart_2038781 baseEnd_2038781 := by
    simpa [prefixWord, tailWord_2038781, baseEnd_2038781] using wordTrace_append hprefix tailTrace_2038781
  have hstable : (prefixWord ++ tailWord_2038781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038781).length < 2 ^ (prefixWord ++ tailWord_2038781).sum := by decide
  have hdescent : baseEnd_2038781 < baseStart_2038781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038785 : List Nat := [1, 2, 4, 1, 2, 3, 1, 2, 3, 3]
def baseStart_2038785 : Nat := 118140960795 + 2038785 * 2 ^ 59
def prefixEnd_2038785 : Nat := 4983230072969 + 3 ^ 40 * 2038785 * 2
def baseEnd_2038785 : Nat := 697917770784607318674203

theorem tailTrace_2038785 : CollatzResearch.WordTrace tailWord_2038785 prefixEnd_2038785 697917770784607318674203 := by
  unfold tailWord_2038785
  simp only [CollatzResearch.WordTrace]
  refine ⟨74360597918837616601749809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49573731945891744401166539 74360597918837616601749809)
  ·
    refine ⟨55770448439128212451312357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74360597918837616601749809 55770448439128212451312357)
    ·
      refine ⟨10456959082336539834621067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55770448439128212451312357 10456959082336539834621067)
      ·
        refine ⟨15685438623504809751931601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10456959082336539834621067 15685438623504809751931601)
        ·
          refine ⟨11764078967628607313948701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15685438623504809751931601 11764078967628607313948701)
          ·
            refine ⟨4411529612860727742730763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11764078967628607313948701 4411529612860727742730763)
            ·
              refine ⟨6617294419291091614096145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4411529612860727742730763 6617294419291091614096145)
              ·
                refine ⟨4962970814468318710572109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6617294419291091614096145 4962970814468318710572109)
                ·
                  refine ⟨1861114055425619516464541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4962970814468318710572109 1861114055425619516464541)
                  ·
                    refine ⟨697917770784607318674203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1861114055425619516464541 697917770784607318674203)
                    ·
                      rfl

theorem cell22_2038785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_2038785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038785 prefixEnd_2038785 := by exact prefixLift 2038785
  have htrace : WordTrace (prefixWord ++ tailWord_2038785) baseStart_2038785 baseEnd_2038785 := by
    simpa [prefixWord, tailWord_2038785, baseEnd_2038785] using wordTrace_append hprefix tailTrace_2038785
  have hstable : (prefixWord ++ tailWord_2038785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038785).length < 2 ^ (prefixWord ++ tailWord_2038785).sum := by decide
  have hdescent : baseEnd_2038785 < baseStart_2038785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038815 : List Nat := [1, 1, 2, 4, 1, 5, 1, 2, 5]
def baseStart_2038815 : Nat := 118140960795 + 2038815 * 2 ^ 59
def prefixEnd_2038815 : Nat := 4983230072969 + 3 ^ 40 * 2038815 * 2
def baseEnd_2038815 : Nat := 232642680132565746808037

theorem tailTrace_2038815 : CollatzResearch.WordTrace tailWord_2038815 prefixEnd_2038815 232642680132565746808037 := by
  unfold tailWord_2038815
  simp only [CollatzResearch.WordTrace]
  refine ⟨74361692108728931725341899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49574461405819287816894599 74361692108728931725341899)
  ·
    refine ⟨111542538163093397588012849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74361692108728931725341899 111542538163093397588012849)
    ·
      refine ⟨83656903622320048191009637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111542538163093397588012849 83656903622320048191009637)
      ·
        refine ⟨15685669429185009035814307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83656903622320048191009637 15685669429185009035814307)
        ·
          refine ⟨23528504143777513553721461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15685669429185009035814307 23528504143777513553721461)
          ·
            refine ⟨2205797263479141895661387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23528504143777513553721461 2205797263479141895661387)
            ·
              refine ⟨3308695895218712843492081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205797263479141895661387 3308695895218712843492081)
              ·
                refine ⟨2481521921414034632619061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3308695895218712843492081 2481521921414034632619061)
                ·
                  refine ⟨232642680132565746808037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2481521921414034632619061 232642680132565746808037)
                  ·
                    rfl

theorem cell22_2038815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 5].length) (baseStart_2038815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038815 prefixEnd_2038815 := by exact prefixLift 2038815
  have htrace : WordTrace (prefixWord ++ tailWord_2038815) baseStart_2038815 baseEnd_2038815 := by
    simpa [prefixWord, tailWord_2038815, baseEnd_2038815] using wordTrace_append hprefix tailTrace_2038815
  have hstable : (prefixWord ++ tailWord_2038815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038815).length < 2 ^ (prefixWord ++ tailWord_2038815).sum := by decide
  have hdescent : baseEnd_2038815 < baseStart_2038815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038845 : List Nat := [1, 4, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_2038845 : Nat := 118140960795 + 2038845 * 2 ^ 59
def prefixEnd_2038845 : Nat := 4983230072969 + 3 ^ 40 * 2038845 * 2
def baseEnd_2038845 : Nat := 697938310010787162174019

theorem tailTrace_2038845 : CollatzResearch.WordTrace tailWord_2038845 prefixEnd_2038845 697938310010787162174019 := by
  unfold tailWord_2038845
  simp only [CollatzResearch.WordTrace]
  refine ⟨74362786298620246848933989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49575190865746831232622659 74362786298620246848933989)
  ·
    refine ⟨13943022430991296284175123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74362786298620246848933989 13943022430991296284175123)
    ·
      refine ⟨20914533646486944426262685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13943022430991296284175123 20914533646486944426262685)
      ·
        refine ⟨7842950117432604159848507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20914533646486944426262685 7842950117432604159848507)
        ·
          refine ⟨11764425176148906239772761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7842950117432604159848507 11764425176148906239772761)
          ·
            refine ⟨8823318882111679679829571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11764425176148906239772761 8823318882111679679829571)
            ·
              refine ⟨13234978323167519519744357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8823318882111679679829571 13234978323167519519744357)
              ·
                refine ⟨2481558435593909909952067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13234978323167519519744357 2481558435593909909952067)
                ·
                  refine ⟨3722337653390864864928101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2481558435593909909952067 3722337653390864864928101)
                  ·
                    refine ⟨697938310010787162174019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3722337653390864864928101 697938310010787162174019)
                    ·
                      rfl

theorem cell22_2038845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_2038845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038845 prefixEnd_2038845 := by exact prefixLift 2038845
  have htrace : WordTrace (prefixWord ++ tailWord_2038845) baseStart_2038845 baseEnd_2038845 := by
    simpa [prefixWord, tailWord_2038845, baseEnd_2038845] using wordTrace_append hprefix tailTrace_2038845
  have hstable : (prefixWord ++ tailWord_2038845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038845).length < 2 ^ (prefixWord ++ tailWord_2038845).sum := by decide
  have hdescent : baseEnd_2038845 < baseStart_2038845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038858 : List Nat := [3, 1, 2, 1, 1, 2, 2, 4, 1, 5]
def baseStart_2038858 : Nat := 118140960795 + 2038858 * 2 ^ 59
def prefixEnd_2038858 : Nat := 4983230072969 + 3 ^ 40 * 2038858 * 2
def baseEnd_2038858 : Nat := 697942760176459461598979

theorem tailTrace_2038858 : CollatzResearch.WordTrace tailWord_2038858 prefixEnd_2038858 697942760176459461598979 := by
  unfold tailWord_2038858
  simp only [CollatzResearch.WordTrace]
  refine ⟨18590815111893287517289307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49575506965048766712771485 18590815111893287517289307)
  ·
    refine ⟨27886222667839931275933961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18590815111893287517289307 27886222667839931275933961)
    ·
      refine ⟨20914667000879948456950471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27886222667839931275933961 20914667000879948456950471)
      ·
        refine ⟨31372000501319922685425707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20914667000879948456950471 31372000501319922685425707)
        ·
          refine ⟨47058000751979884028138561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31372000501319922685425707 47058000751979884028138561)
          ·
            refine ⟨35293500563984913021103921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47058000751979884028138561 35293500563984913021103921)
            ·
              refine ⟨26470125422988684765827941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35293500563984913021103921 26470125422988684765827941)
              ·
                refine ⟨4963148516810378393592739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26470125422988684765827941 4963148516810378393592739)
                ·
                  refine ⟨7444722775215567590389109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4963148516810378393592739 7444722775215567590389109)
                  ·
                    refine ⟨697942760176459461598979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7444722775215567590389109 697942760176459461598979)
                    ·
                      rfl

theorem cell22_2038858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_2038858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038858 prefixEnd_2038858 := by exact prefixLift 2038858
  have htrace : WordTrace (prefixWord ++ tailWord_2038858) baseStart_2038858 baseEnd_2038858 := by
    simpa [prefixWord, tailWord_2038858, baseEnd_2038858] using wordTrace_append hprefix tailTrace_2038858
  have hstable : (prefixWord ++ tailWord_2038858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038858).length < 2 ^ (prefixWord ++ tailWord_2038858).sum := by decide
  have hdescent : baseEnd_2038858 < baseStart_2038858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038954 : List Nat := [3, 1, 5, 1, 1, 2, 1, 2, 3, 3]
def baseStart_2038954 : Nat := 118140960795 + 2038954 * 2 ^ 59
def prefixEnd_2038954 : Nat := 4983230072969 + 3 ^ 40 * 2038954 * 2
def baseEnd_2038954 : Nat := 697975622938347211198685

theorem tailTrace_2038954 : CollatzResearch.WordTrace tailWord_2038954 prefixEnd_2038954 697975622938347211198685 := by
  unfold tailWord_2038954
  simp only [CollatzResearch.WordTrace]
  refine ⟨18591690463806339616162979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49577841236816905643101277 18591690463806339616162979)
  ·
    refine ⟨27887535695709509424244469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18591690463806339616162979 27887535695709509424244469)
    ·
      refine ⟨2614456471472766508522919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27887535695709509424244469 2614456471472766508522919)
      ·
        refine ⟨3921684707209149762784379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2614456471472766508522919 3921684707209149762784379)
        ·
          refine ⟨5882527060813724644176569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3921684707209149762784379 5882527060813724644176569)
          ·
            refine ⟨4411895295610293483132427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5882527060813724644176569 4411895295610293483132427)
            ·
              refine ⟨6617842943415440224698641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4411895295610293483132427 6617842943415440224698641)
              ·
                refine ⟨4963382207561580168523981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6617842943415440224698641 4963382207561580168523981)
                ·
                  refine ⟨1861268327835592563196493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4963382207561580168523981 1861268327835592563196493)
                  ·
                    refine ⟨697975622938347211198685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1861268327835592563196493 697975622938347211198685)
                    ·
                      rfl

theorem cell22_2038954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_2038954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2038954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2038954 prefixEnd_2038954 := by exact prefixLift 2038954
  have htrace : WordTrace (prefixWord ++ tailWord_2038954) baseStart_2038954 baseEnd_2038954 := by
    simpa [prefixWord, tailWord_2038954, baseEnd_2038954] using wordTrace_append hprefix tailTrace_2038954
  have hstable : (prefixWord ++ tailWord_2038954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038954).length < 2 ^ (prefixWord ++ tailWord_2038954).sum := by decide
  have hdescent : baseEnd_2038954 < baseStart_2038954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039025 : List Nat := [1, 2, 2, 2, 2, 1, 1, 5, 2, 4]
def baseStart_2039025 : Nat := 118140960795 + 2039025 * 2 ^ 59
def prefixEnd_2039025 : Nat := 4983230072969 + 3 ^ 40 * 2039025 * 2
def baseEnd_2039025 : Nat := 697999927689326692673467

theorem tailTrace_2039025 : CollatzResearch.WordTrace tailWord_2039025 prefixEnd_2039025 697999927689326692673467 := by
  unfold tailWord_2039025
  simp only [CollatzResearch.WordTrace]
  refine ⟨74369351437968137590486529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49579567625312091726991019 74369351437968137590486529)
  ·
    refine ⟨55777013578476103192864897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74369351437968137590486529 55777013578476103192864897)
    ·
      refine ⟨41832760183857077394648673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55777013578476103192864897 41832760183857077394648673)
      ·
        refine ⟨31374570137892808045986505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41832760183857077394648673 31374570137892808045986505)
        ·
          refine ⟨23530927603419606034489879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31374570137892808045986505 23530927603419606034489879)
          ·
            refine ⟨35296391405129409051734819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23530927603419606034489879 35296391405129409051734819)
            ·
              refine ⟨52944587107694113577602229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35296391405129409051734819 52944587107694113577602229)
              ·
                refine ⟨4963555041346323147900209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52944587107694113577602229 4963555041346323147900209)
                ·
                  refine ⟨3722666281009742360925157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4963555041346323147900209 3722666281009742360925157)
                  ·
                    refine ⟨697999927689326692673467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3722666281009742360925157 697999927689326692673467)
                    ·
                      rfl

theorem cell22_2039025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_2039025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039025 prefixEnd_2039025 := by exact prefixLift 2039025
  have htrace : WordTrace (prefixWord ++ tailWord_2039025) baseStart_2039025 baseEnd_2039025 := by
    simpa [prefixWord, tailWord_2039025, baseEnd_2039025] using wordTrace_append hprefix tailTrace_2039025
  have hstable : (prefixWord ++ tailWord_2039025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039025).length < 2 ^ (prefixWord ++ tailWord_2039025).sum := by decide
  have hdescent : baseEnd_2039025 < baseStart_2039025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039130 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 8]
def baseStart_2039130 : Nat := 118140960795 + 2039130 * 2 ^ 59
def prefixEnd_2039130 : Nat := 4983230072969 + 3 ^ 40 * 2039130 * 2
def baseEnd_2039130 : Nat := 232678623778380472932715

theorem tailTrace_2039130 : CollatzResearch.WordTrace tailWord_2039130 prefixEnd_2039130 232678623778380472932715 := by
  unfold tailWord_2039130
  simp only [CollatzResearch.WordTrace]
  refine ⟨18593295275646935130764711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49582120735058493682039229 18593295275646935130764711)
  ·
    refine ⟨27889942913470402696147067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18593295275646935130764711 27889942913470402696147067)
    ·
      refine ⟨41834914370205604044220601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27889942913470402696147067 41834914370205604044220601)
      ·
        refine ⟨31376185777654203033165451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41834914370205604044220601 31376185777654203033165451)
        ·
          refine ⟨47064278666481304549748177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31376185777654203033165451 47064278666481304549748177)
          ·
            refine ⟨35298208999860978412311133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47064278666481304549748177 35298208999860978412311133)
            ·
              refine ⟨13236828374947866904616675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35298208999860978412311133 13236828374947866904616675)
              ·
                refine ⟨19855242562421800356925013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13236828374947866904616675 19855242562421800356925013)
                ·
                  refine ⟨232678623778380472932715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19855242562421800356925013 232678623778380472932715)
                  ·
                    rfl

theorem cell22_2039130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_2039130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039130 prefixEnd_2039130 := by exact prefixLift 2039130
  have htrace : WordTrace (prefixWord ++ tailWord_2039130) baseStart_2039130 baseEnd_2039130 := by
    simpa [prefixWord, tailWord_2039130, baseEnd_2039130] using wordTrace_append hprefix tailTrace_2039130
  have hstable : (prefixWord ++ tailWord_2039130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039130).length < 2 ^ (prefixWord ++ tailWord_2039130).sum := by decide
  have hdescent : baseEnd_2039130 < baseStart_2039130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039145 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 3, 5]
def baseStart_2039145 : Nat := 118140960795 + 2039145 * 2 ^ 59
def prefixEnd_2039145 : Nat := 4983230072969 + 3 ^ 40 * 2039145 * 2
def baseEnd_2039145 : Nat := 698041006141686379673099

theorem tailTrace_2039145 : CollatzResearch.WordTrace tailWord_2039145 prefixEnd_2039145 698041006141686379673099 := by
  unfold tailWord_2039145
  simp only [CollatzResearch.WordTrace]
  refine ⟨74373728197533398084854889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49582485465022265389903259 74373728197533398084854889)
  ·
    refine ⟨55780296148150048563641167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74373728197533398084854889 55780296148150048563641167)
    ·
      refine ⟨83670444222225072845461751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55780296148150048563641167 83670444222225072845461751)
      ·
        refine ⟨125505666333337609268192627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83670444222225072845461751 125505666333337609268192627)
        ·
          refine ⟨188258499500006413902288941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125505666333337609268192627 188258499500006413902288941)
          ·
            refine ⟨70596937312502405213358353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188258499500006413902288941 70596937312502405213358353)
            ·
              refine ⟨52947702984376803910018765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70596937312502405213358353 52947702984376803910018765)
              ·
                refine ⟨19855388619141301466257037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52947702984376803910018765 19855388619141301466257037)
                ·
                  refine ⟨7445770732177988049846389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19855388619141301466257037 7445770732177988049846389)
                  ·
                    refine ⟨698041006141686379673099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7445770732177988049846389 698041006141686379673099)
                    ·
                      rfl

theorem cell22_2039145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_2039145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039145 prefixEnd_2039145 := by exact prefixLift 2039145
  have htrace : WordTrace (prefixWord ++ tailWord_2039145) baseStart_2039145 baseEnd_2039145 := by
    simpa [prefixWord, tailWord_2039145, baseEnd_2039145] using wordTrace_append hprefix tailTrace_2039145
  have hstable : (prefixWord ++ tailWord_2039145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039145).length < 2 ^ (prefixWord ++ tailWord_2039145).sum := by decide
  have hdescent : baseEnd_2039145 < baseStart_2039145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039149 : List Nat := [1, 5, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_2039149 : Nat := 118140960795 + 2039149 * 2 ^ 59
def prefixEnd_2039149 : Nat := 4983230072969 + 3 ^ 40 * 2039149 * 2
def baseEnd_2039149 : Nat := 698042375423431702573087

theorem tailTrace_2039149 : CollatzResearch.WordTrace tailWord_2039149 prefixEnd_2039149 698042375423431702573087 := by
  unfold tailWord_2039149
  simp only [CollatzResearch.WordTrace]
  refine ⟨74373874089518906768000501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49582582726345937845333667 74373874089518906768000501)
  ·
    refine ⟨6972550695892397509500047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74373874089518906768000501 6972550695892397509500047)
    ·
      refine ⟨10458826043838596264250071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6972550695892397509500047 10458826043838596264250071)
      ·
        refine ⟨15688239065757894396375107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10458826043838596264250071 15688239065757894396375107)
        ·
          refine ⟨23532358598636841594562661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15688239065757894396375107 23532358598636841594562661)
          ·
            refine ⟨4412317237244407798980499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23532358598636841594562661 4412317237244407798980499)
            ·
              refine ⟨6618475855866611698470749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4412317237244407798980499 6618475855866611698470749)
              ·
                refine ⟨2481928445949979386926531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6618475855866611698470749 2481928445949979386926531)
                ·
                  refine ⟨3722892668924969080389797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2481928445949979386926531 3722892668924969080389797)
                  ·
                    refine ⟨698042375423431702573087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3722892668924969080389797 698042375423431702573087)
                    ·
                      rfl

theorem cell22_2039149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_2039149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039149 prefixEnd_2039149 := by exact prefixLift 2039149
  have htrace : WordTrace (prefixWord ++ tailWord_2039149) baseStart_2039149 baseEnd_2039149 := by
    simpa [prefixWord, tailWord_2039149, baseEnd_2039149] using wordTrace_append hprefix tailTrace_2039149
  have hstable : (prefixWord ++ tailWord_2039149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039149).length < 2 ^ (prefixWord ++ tailWord_2039149).sum := by decide
  have hdescent : baseEnd_2039149 < baseStart_2039149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039162 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 4, 3]
def baseStart_2039162 : Nat := 118140960795 + 2039162 * 2 ^ 59
def prefixEnd_2039162 : Nat := 4983230072969 + 3 ^ 40 * 2039162 * 2
def baseEnd_2039162 : Nat := 698046825589104001998047

theorem tailTrace_2039162 : CollatzResearch.WordTrace tailWord_2039162 prefixEnd_2039162 698046825589104001998047 := by
  unfold tailWord_2039162
  simp only [CollatzResearch.WordTrace]
  refine ⟨18593587059617952497055935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49582898825647873325482493 18593587059617952497055935)
  ·
    refine ⟨27890380589426928745583903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18593587059617952497055935 27890380589426928745583903)
    ·
      refine ⟨41835570884140393118375855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27890380589426928745583903 41835570884140393118375855)
      ·
        refine ⟨62753356326210589677563783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41835570884140393118375855 62753356326210589677563783)
        ·
          refine ⟨94130034489315884516345675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62753356326210589677563783 94130034489315884516345675)
          ·
            refine ⟨141195051733973826774518513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94130034489315884516345675 141195051733973826774518513)
            ·
              refine ⟨105896288800480370080888885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141195051733973826774518513 105896288800480370080888885)
              ·
                refine ⟨9927777075045034695083333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105896288800480370080888885 9927777075045034695083333)
                ·
                  refine ⟨1861458201570944005328125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9927777075045034695083333 1861458201570944005328125)
                  ·
                    refine ⟨698046825589104001998047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1861458201570944005328125 698046825589104001998047)
                    ·
                      rfl

theorem cell22_2039162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_2039162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039162 prefixEnd_2039162 := by exact prefixLift 2039162
  have htrace : WordTrace (prefixWord ++ tailWord_2039162) baseStart_2039162 baseEnd_2039162 := by
    simpa [prefixWord, tailWord_2039162, baseEnd_2039162] using wordTrace_append hprefix tailTrace_2039162
  have hstable : (prefixWord ++ tailWord_2039162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039162).length < 2 ^ (prefixWord ++ tailWord_2039162).sum := by decide
  have hdescent : baseEnd_2039162 < baseStart_2039162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039224 : List Nat := [2, 1, 2, 1, 2, 2, 5, 1, 3, 3]
def baseStart_2039224 : Nat := 118140960795 + 2039224 * 2 ^ 59
def prefixEnd_2039224 : Nat := 4983230072969 + 3 ^ 40 * 2039224 * 2
def baseEnd_2039224 : Nat := 698068049456156506947857

theorem tailTrace_2039224 : CollatzResearch.WordTrace tailWord_2039224 prefixEnd_2039224 698068049456156506947857 := by
  unfold tailWord_2039224
  simp only [CollatzResearch.WordTrace]
  refine ⟨37188304782123597288490363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49584406376164796384653817 37188304782123597288490363)
  ·
    refine ⟨55782457173185395932735545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37188304782123597288490363 55782457173185395932735545)
    ·
      refine ⟨41836842879889046949551659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55782457173185395932735545 41836842879889046949551659)
      ·
        refine ⟨62755264319833570424327489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41836842879889046949551659 62755264319833570424327489)
        ·
          refine ⟨47066448239875177818245617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62755264319833570424327489 47066448239875177818245617)
          ·
            refine ⟨35299836179906383363684213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47066448239875177818245617 35299836179906383363684213)
            ·
              refine ⟨3309359641866223440345395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35299836179906383363684213 3309359641866223440345395)
              ·
                refine ⟨4964039462799335160518093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3309359641866223440345395 4964039462799335160518093)
                ·
                  refine ⟨1861514798549750685194285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4964039462799335160518093 1861514798549750685194285)
                  ·
                    refine ⟨698068049456156506947857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1861514798549750685194285 698068049456156506947857)
                    ·
                      rfl

theorem cell22_2039224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_2039224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039224 prefixEnd_2039224 := by exact prefixLift 2039224
  have htrace : WordTrace (prefixWord ++ tailWord_2039224) baseStart_2039224 baseEnd_2039224 := by
    simpa [prefixWord, tailWord_2039224, baseEnd_2039224] using wordTrace_append hprefix tailTrace_2039224
  have hstable : (prefixWord ++ tailWord_2039224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039224).length < 2 ^ (prefixWord ++ tailWord_2039224).sum := by decide
  have hdescent : baseEnd_2039224 < baseStart_2039224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039234 : List Nat := [3, 5, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_2039234 : Nat := 118140960795 + 2039234 * 2 ^ 59
def prefixEnd_2039234 : Nat := 4983230072969 + 3 ^ 40 * 2039234 * 2
def baseEnd_2039234 : Nat := 698071472660519814197827

theorem tailTrace_2039234 : CollatzResearch.WordTrace tailWord_2039234 prefixEnd_2039234 698071472660519814197827 := by
  unfold tailWord_2039234
  simp only [CollatzResearch.WordTrace]
  refine ⟨18594243573552741571211189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49584649529473977523229837 18594243573552741571211189)
  ·
    refine ⟨1743210335020569522301049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18594243573552741571211189 1743210335020569522301049)
    ·
      refine ⟨1307407751265427141725787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1743210335020569522301049 1307407751265427141725787)
      ·
        refine ⟨1961111626898140712588681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1307407751265427141725787 1961111626898140712588681)
        ·
          refine ⟨1470833720173605534441511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1961111626898140712588681 1470833720173605534441511)
          ·
            refine ⟨2206250580260408301662267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470833720173605534441511 2206250580260408301662267)
            ·
              refine ⟨3309375870390612452493401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206250580260408301662267 3309375870390612452493401)
              ·
                refine ⟨2482031902792959339370051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3309375870390612452493401 2482031902792959339370051)
                ·
                  refine ⟨3723047854189439009055077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2482031902792959339370051 3723047854189439009055077)
                  ·
                    refine ⟨698071472660519814197827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3723047854189439009055077 698071472660519814197827)
                    ·
                      rfl

theorem cell22_2039234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_2039234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039234 prefixEnd_2039234 := by exact prefixLift 2039234
  have htrace : WordTrace (prefixWord ++ tailWord_2039234) baseStart_2039234 baseEnd_2039234 := by
    simpa [prefixWord, tailWord_2039234, baseEnd_2039234] using wordTrace_append hprefix tailTrace_2039234
  have hstable : (prefixWord ++ tailWord_2039234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039234).length < 2 ^ (prefixWord ++ tailWord_2039234).sum := by decide
  have hdescent : baseEnd_2039234 < baseStart_2039234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039331 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 4, 3]
def baseStart_2039331 : Nat := 118140960795 + 2039331 * 2 ^ 59
def prefixEnd_2039331 : Nat := 4983230072969 + 3 ^ 40 * 2039331 * 2
def baseEnd_2039331 : Nat := 698104677742843894522529

theorem tailTrace_2039331 : CollatzResearch.WordTrace tailWord_2039331 prefixEnd_2039331 698104677742843894522529 := by
  unfold tailWord_2039331
  simp only [CollatzResearch.WordTrace]
  refine ⟨74380512174859551851125847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49587008116573034567417231 74380512174859551851125847)
  ·
    refine ⟨111570768262289327776688771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74380512174859551851125847 111570768262289327776688771)
    ·
      refine ⟨167356152393433991665033157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111570768262289327776688771 167356152393433991665033157)
      ·
        refine ⟨31379278573768873437193717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167356152393433991665033157 31379278573768873437193717)
        ·
          refine ⟨2941807366290831884736911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31379278573768873437193717 2941807366290831884736911)
          ·
            refine ⟨4412711049436247827105367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2941807366290831884736911 4412711049436247827105367)
            ·
              refine ⟨6619066574154371740658051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4412711049436247827105367 6619066574154371740658051)
              ·
                refine ⟨9928599861231557610987077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6619066574154371740658051 9928599861231557610987077)
                ·
                  refine ⟨1861612473980917052060077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9928599861231557610987077 1861612473980917052060077)
                  ·
                    refine ⟨698104677742843894522529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1861612473980917052060077 698104677742843894522529)
                    ·
                      rfl

theorem cell22_2039331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 3].length) (baseStart_2039331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039331 prefixEnd_2039331 := by exact prefixLift 2039331
  have htrace : WordTrace (prefixWord ++ tailWord_2039331) baseStart_2039331 baseEnd_2039331 := by
    simpa [prefixWord, tailWord_2039331, baseEnd_2039331] using wordTrace_append hprefix tailTrace_2039331
  have hstable : (prefixWord ++ tailWord_2039331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039331).length < 2 ^ (prefixWord ++ tailWord_2039331).sum := by decide
  have hdescent : baseEnd_2039331 < baseStart_2039331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039419 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 3, 4]
def baseStart_2039419 : Nat := 118140960795 + 2039419 * 2 ^ 59
def prefixEnd_2039419 : Nat := 4983230072969 + 3 ^ 40 * 2039419 * 2
def baseEnd_2039419 : Nat := 698134801941240998322259

theorem tailTrace_2039419 : CollatzResearch.WordTrace tailWord_2039419 prefixEnd_2039419 698134801941240998322259 := by
  unfold tailWord_2039419
  simp only [CollatzResearch.WordTrace]
  refine ⟨74383721798540742880329311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49589147865693828586886207 74383721798540742880329311)
  ·
    refine ⟨111575582697811114320493967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74383721798540742880329311 111575582697811114320493967)
    ·
      refine ⟨167363374046716671480740951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111575582697811114320493967 167363374046716671480740951)
      ·
        refine ⟨251045061070075007221111427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167363374046716671480740951 251045061070075007221111427)
        ·
          refine ⟨376567591605112510831667141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251045061070075007221111427 376567591605112510831667141)
          ·
            refine ⟨70606423425958595780937589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 376567591605112510831667141 70606423425958595780937589)
            ·
              refine ⟨6619352196183618354462899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70606423425958595780937589 6619352196183618354462899)
              ·
                refine ⟨9929028294275427531694349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6619352196183618354462899 9929028294275427531694349)
                ·
                  refine ⟨3723385610353285324385381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9929028294275427531694349 3723385610353285324385381)
                  ·
                    refine ⟨698134801941240998322259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3723385610353285324385381 698134801941240998322259)
                    ·
                      rfl

theorem cell22_2039419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 4].length) (baseStart_2039419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039419 prefixEnd_2039419 := by exact prefixLift 2039419
  have htrace : WordTrace (prefixWord ++ tailWord_2039419) baseStart_2039419 baseEnd_2039419 := by
    simpa [prefixWord, tailWord_2039419, baseEnd_2039419] using wordTrace_append hprefix tailTrace_2039419
  have hstable : (prefixWord ++ tailWord_2039419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039419).length < 2 ^ (prefixWord ++ tailWord_2039419).sum := by decide
  have hdescent : baseEnd_2039419 < baseStart_2039419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039444 : List Nat := [2, 4, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_2039444 : Nat := 118140960795 + 2039444 * 2 ^ 59
def prefixEnd_2039444 : Nat := 4983230072969 + 3 ^ 40 * 2039444 * 2
def baseEnd_2039444 : Nat := 698143359952149266447183

theorem tailTrace_2039444 : CollatzResearch.WordTrace tailWord_2039444 prefixEnd_2039444 698143359952149266447183 := by
  unfold tailWord_2039444
  simp only [CollatzResearch.WordTrace]
  refine ⟨37192316811725086074994693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49589755748966781433326257 37192316811725086074994693)
  ·
    refine ⟨6973559402198453639061505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37192316811725086074994693 6973559402198453639061505)
    ·
      refine ⟨5230169551648840229296129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6973559402198453639061505 5230169551648840229296129)
      ·
        refine ⟨3922627163736630171972097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5230169551648840229296129 3922627163736630171972097)
        ·
          refine ⟨2941970372802472628979073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3922627163736630171972097 2941970372802472628979073)
          ·
            refine ⟨2206477779601854471734305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2941970372802472628979073 2206477779601854471734305)
            ·
              refine ⟨1654858334701390853800729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2206477779601854471734305 1654858334701390853800729)
              ·
                refine ⟨1241143751026043140350547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1654858334701390853800729 1241143751026043140350547)
                ·
                  refine ⟨1861715626539064710525821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1241143751026043140350547 1861715626539064710525821)
                  ·
                    refine ⟨698143359952149266447183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1861715626539064710525821 698143359952149266447183)
                    ·
                      rfl

theorem cell22_2039444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_2039444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039444 prefixEnd_2039444 := by exact prefixLift 2039444
  have htrace : WordTrace (prefixWord ++ tailWord_2039444) baseStart_2039444 baseEnd_2039444 := by
    simpa [prefixWord, tailWord_2039444, baseEnd_2039444] using wordTrace_append hprefix tailTrace_2039444
  have hstable : (prefixWord ++ tailWord_2039444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039444).length < 2 ^ (prefixWord ++ tailWord_2039444).sum := by decide
  have hdescent : baseEnd_2039444 < baseStart_2039444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039481 : List Nat := [1, 2, 1, 4, 1, 1, 5, 1, 2, 4]
def baseStart_2039481 : Nat := 118140960795 + 2039481 * 2 ^ 59
def prefixEnd_2039481 : Nat := 4983230072969 + 3 ^ 40 * 2039481 * 2
def baseEnd_2039481 : Nat := 698156025808293503272069

theorem tailTrace_2039481 : CollatzResearch.WordTrace tailWord_2039481 prefixEnd_2039481 698156025808293503272069 := by
  unfold tailWord_2039481
  simp only [CollatzResearch.WordTrace]
  refine ⟨74385983124316127469086297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49590655416210751646057531 74385983124316127469086297)
  ·
    refine ⟨55789487343237095601814723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74385983124316127469086297 55789487343237095601814723)
    ·
      refine ⟨83684231014855643402722085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55789487343237095601814723 83684231014855643402722085)
      ·
        refine ⟨15690793315285433138010391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83684231014855643402722085 15690793315285433138010391)
        ·
          refine ⟨23536189972928149707015587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15690793315285433138010391 23536189972928149707015587)
          ·
            refine ⟨35304284959392224560523381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23536189972928149707015587 35304284959392224560523381)
            ·
              refine ⟨3309776714943021052549067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35304284959392224560523381 3309776714943021052549067)
              ·
                refine ⟨4964665072414531578823601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3309776714943021052549067 4964665072414531578823601)
                ·
                  refine ⟨3723498804310898684117701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4964665072414531578823601 3723498804310898684117701)
                  ·
                    refine ⟨698156025808293503272069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3723498804310898684117701 698156025808293503272069)
                    ·
                      rfl

theorem cell22_2039481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 4].length) (baseStart_2039481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039481 prefixEnd_2039481 := by exact prefixLift 2039481
  have htrace : WordTrace (prefixWord ++ tailWord_2039481) baseStart_2039481 baseEnd_2039481 := by
    simpa [prefixWord, tailWord_2039481, baseEnd_2039481] using wordTrace_append hprefix tailTrace_2039481
  have hstable : (prefixWord ++ tailWord_2039481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039481).length < 2 ^ (prefixWord ++ tailWord_2039481).sum := by decide
  have hdescent : baseEnd_2039481 < baseStart_2039481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039517 : List Nat := [1, 4, 3, 3, 2, 1, 1, 1, 1, 5]
def baseStart_2039517 : Nat := 118140960795 + 2039517 * 2 ^ 59
def prefixEnd_2039517 : Nat := 4983230072969 + 3 ^ 40 * 2039517 * 2
def baseEnd_2039517 : Nat := 698168349344001409371959

theorem tailTrace_2039517 : CollatzResearch.WordTrace tailWord_2039517 prefixEnd_2039517 698168349344001409371959 := by
  unfold tailWord_2039517
  simp only [CollatzResearch.WordTrace]
  refine ⟨74387296152185705617396805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49591530768123803744931203 74387296152185705617396805)
  ·
    refine ⟨13947618028534819803261901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74387296152185705617396805 13947618028534819803261901)
    ·
      refine ⟨5230356760700557426223213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13947618028534819803261901 5230356760700557426223213)
      ·
        refine ⟨1961383785262709034833705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5230356760700557426223213 1961383785262709034833705)
        ·
          refine ⟨1471037838947031776125279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1961383785262709034833705 1471037838947031776125279)
          ·
            refine ⟨2206556758420547664187919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1471037838947031776125279 2206556758420547664187919)
            ·
              refine ⟨3309835137630821496281879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206556758420547664187919 3309835137630821496281879)
              ·
                refine ⟨4964752706446232244422819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3309835137630821496281879 4964752706446232244422819)
                ·
                  refine ⟨7447129059669348366634229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4964752706446232244422819 7447129059669348366634229)
                  ·
                    refine ⟨698168349344001409371959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7447129059669348366634229 698168349344001409371959)
                    ·
                      rfl

theorem cell22_2039517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_2039517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039517 prefixEnd_2039517 := by exact prefixLift 2039517
  have htrace : WordTrace (prefixWord ++ tailWord_2039517) baseStart_2039517 baseEnd_2039517 := by
    simpa [prefixWord, tailWord_2039517, baseEnd_2039517] using wordTrace_append hprefix tailTrace_2039517
  have hstable : (prefixWord ++ tailWord_2039517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039517).length < 2 ^ (prefixWord ++ tailWord_2039517).sum := by decide
  have hdescent : baseEnd_2039517 < baseStart_2039517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039528 : List Nat := [2, 1, 4, 1, 3, 1, 2, 2, 3, 3]
def baseStart_2039528 : Nat := 118140960795 + 2039528 * 2 ^ 59
def prefixEnd_2039528 : Nat := 4983230072969 + 3 ^ 40 * 2039528 * 2
def baseEnd_2039528 : Nat := 698172114868801047346925

theorem tailTrace_2039528 : CollatzResearch.WordTrace tailWord_2039528 prefixEnd_2039528 698172114868801047346925 := by
  unfold tailWord_2039528
  simp only [CollatzResearch.WordTrace]
  refine ⟨37193848677572927248023619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49591798236763902997364825 37193848677572927248023619)
  ·
    refine ⟨55790773016359390872035429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37193848677572927248023619 55790773016359390872035429)
    ·
      refine ⟨10460769940567385788506643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55790773016359390872035429 10460769940567385788506643)
      ·
        refine ⟨15691154910851078682759965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10460769940567385788506643 15691154910851078682759965)
        ·
          refine ⟨5884183091569154506034987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15691154910851078682759965 5884183091569154506034987)
          ·
            refine ⟨8826274637353731759052481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5884183091569154506034987 8826274637353731759052481)
            ·
              refine ⟨6619705978015298819289361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8826274637353731759052481 6619705978015298819289361)
              ·
                refine ⟨4964779483511474114467021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6619705978015298819289361 4964779483511474114467021)
                ·
                  refine ⟨1861792306316802792925133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4964779483511474114467021 1861792306316802792925133)
                  ·
                    refine ⟨698172114868801047346925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1861792306316802792925133 698172114868801047346925)
                    ·
                      rfl

theorem cell22_2039528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_2039528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039528 prefixEnd_2039528 := by exact prefixLift 2039528
  have htrace : WordTrace (prefixWord ++ tailWord_2039528) baseStart_2039528 baseEnd_2039528 := by
    simpa [prefixWord, tailWord_2039528, baseEnd_2039528] using wordTrace_append hprefix tailTrace_2039528
  have hstable : (prefixWord ++ tailWord_2039528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039528).length < 2 ^ (prefixWord ++ tailWord_2039528).sum := by decide
  have hdescent : baseEnd_2039528 < baseStart_2039528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039539 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 1, 7]
def baseStart_2039539 : Nat := 118140960795 + 2039539 * 2 ^ 59
def prefixEnd_2039539 : Nat := 4983230072969 + 3 ^ 40 * 2039539 * 2
def baseEnd_2039539 : Nat := 698175880393600685321891

theorem tailTrace_2039539 : CollatzResearch.WordTrace tailWord_2039539 prefixEnd_2039539 698175880393600685321891 := by
  unfold tailWord_2039539
  simp only [CollatzResearch.WordTrace]
  refine ⟨74388098558106003374697671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49592065705404002249798447 74388098558106003374697671)
  ·
    refine ⟨111582147837159005062046507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74388098558106003374697671 111582147837159005062046507)
    ·
      refine ⟨167373221755738507593069761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111582147837159005062046507 167373221755738507593069761)
      ·
        refine ⟨125529916316803880694802321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167373221755738507593069761 125529916316803880694802321)
        ·
          refine ⟨94147437237602910521101741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125529916316803880694802321 94147437237602910521101741)
          ·
            refine ⟨35305288964101091445413153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94147437237602910521101741 35305288964101091445413153)
            ·
              refine ⟨26478966723075818584059865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35305288964101091445413153 26478966723075818584059865)
              ·
                refine ⟨19859225042306863938044899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26478966723075818584059865 19859225042306863938044899)
                ·
                  refine ⟨29788837563460295907067349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19859225042306863938044899 29788837563460295907067349)
                  ·
                    refine ⟨698175880393600685321891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29788837563460295907067349 698175880393600685321891)
                    ·
                      rfl

theorem cell22_2039539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 7].length) (baseStart_2039539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039539 prefixEnd_2039539 := by exact prefixLift 2039539
  have htrace : WordTrace (prefixWord ++ tailWord_2039539) baseStart_2039539 baseEnd_2039539 := by
    simpa [prefixWord, tailWord_2039539, baseEnd_2039539] using wordTrace_append hprefix tailTrace_2039539
  have hstable : (prefixWord ++ tailWord_2039539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039539).length < 2 ^ (prefixWord ++ tailWord_2039539).sum := by decide
  have hdescent : baseEnd_2039539 < baseStart_2039539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039562 : List Nat := [3, 1, 2, 2, 1, 4, 3, 2, 1, 3]
def baseStart_2039562 : Nat := 118140960795 + 2039562 * 2 ^ 59
def prefixEnd_2039562 : Nat := 4983230072969 + 3 ^ 40 * 2039562 * 2
def baseEnd_2039562 : Nat := 698183753763636291996821

theorem tailTrace_2039562 : CollatzResearch.WordTrace tailWord_2039562 prefixEnd_2039562 698183753763636291996821 := by
  unfold tailWord_2039562
  simp only [CollatzResearch.WordTrace]
  refine ⟨18597234359255669575696235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49592624958015118868523293 18597234359255669575696235)
  ·
    refine ⟨27895851538883504363544353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18597234359255669575696235 27895851538883504363544353)
    ·
      refine ⟨20921888654162628272658265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27895851538883504363544353 20921888654162628272658265)
      ·
        refine ⟨15691416490621971204493699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20921888654162628272658265 15691416490621971204493699)
        ·
          refine ⟨23537124735932956806740549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15691416490621971204493699 23537124735932956806740549)
          ·
            refine ⟨4413210887987429401263853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23537124735932956806740549 4413210887987429401263853)
            ·
              refine ⟨1654954082995286025473945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4413210887987429401263853 1654954082995286025473945)
              ·
                refine ⟨1241215562246464519105459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1654954082995286025473945 1241215562246464519105459)
                ·
                  refine ⟨1861823343369696778658189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1241215562246464519105459 1861823343369696778658189)
                  ·
                    refine ⟨698183753763636291996821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1861823343369696778658189 698183753763636291996821)
                    ·
                      rfl

theorem cell22_2039562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_2039562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039562 prefixEnd_2039562 := by exact prefixLift 2039562
  have htrace : WordTrace (prefixWord ++ tailWord_2039562) baseStart_2039562 baseEnd_2039562 := by
    simpa [prefixWord, tailWord_2039562, baseEnd_2039562] using wordTrace_append hprefix tailTrace_2039562
  have hstable : (prefixWord ++ tailWord_2039562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039562).length < 2 ^ (prefixWord ++ tailWord_2039562).sum := by decide
  have hdescent : baseEnd_2039562 < baseStart_2039562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039575 : List Nat := [1, 1, 3, 4, 2, 3, 2, 1, 5]
def baseStart_2039575 : Nat := 118140960795 + 2039575 * 2 ^ 59
def prefixEnd_2039575 : Nat := 4983230072969 + 3 ^ 40 * 2039575 * 2
def baseEnd_2039575 : Nat := 232729401309769530473927

theorem tailTrace_2039575 : CollatzResearch.WordTrace tailWord_2039575 prefixEnd_2039575 232729401309769530473927 := by
  unfold tailWord_2039575
  simp only [CollatzResearch.WordTrace]
  refine ⟨74389411585975581523008179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49592941057317054348672119 74389411585975581523008179)
  ·
    refine ⟨111584117378963372284512269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74389411585975581523008179 111584117378963372284512269)
    ·
      refine ⟨41844044017111264606692101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111584117378963372284512269 41844044017111264606692101)
      ·
        refine ⟨7845758253208362113754769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41844044017111264606692101 7845758253208362113754769)
        ·
          refine ⟨5884318689906271585316077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7845758253208362113754769 5884318689906271585316077)
          ·
            refine ⟨2206619508714851844493529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5884318689906271585316077 2206619508714851844493529)
            ·
              refine ⟨1654964631536138883370147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2206619508714851844493529 1654964631536138883370147)
              ·
                refine ⟨2482446947304208325055221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1654964631536138883370147 2482446947304208325055221)
                ·
                  refine ⟨232729401309769530473927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2482446947304208325055221 232729401309769530473927)
                  ·
                    rfl

theorem cell22_2039575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 5].length) (baseStart_2039575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039575 prefixEnd_2039575 := by exact prefixLift 2039575
  have htrace : WordTrace (prefixWord ++ tailWord_2039575) baseStart_2039575 baseEnd_2039575 := by
    simpa [prefixWord, tailWord_2039575, baseEnd_2039575] using wordTrace_append hprefix tailTrace_2039575
  have hstable : (prefixWord ++ tailWord_2039575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039575).length < 2 ^ (prefixWord ++ tailWord_2039575).sum := by decide
  have hdescent : baseEnd_2039575 < baseStart_2039575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039586 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 8]
def baseStart_2039586 : Nat := 118140960795 + 2039586 * 2 ^ 59
def prefixEnd_2039586 : Nat := 4983230072969 + 3 ^ 40 * 2039586 * 2
def baseEnd_2039586 : Nat := 232730656484702743132249

theorem tailTrace_2039586 : CollatzResearch.WordTrace tailWord_2039586 prefixEnd_2039586 232730656484702743132249 := by
  unfold tailWord_2039586
  simp only [CollatzResearch.WordTrace]
  refine ⟨18597453197233932600414653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49593208525957153601105741 18597453197233932600414653)
  ·
    refine ⟨6974044948962724725155495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18597453197233932600414653 6974044948962724725155495)
    ·
      refine ⟨10461067423444087087733243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6974044948962724725155495 10461067423444087087733243)
      ·
        refine ⟨15691601135166130631599865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10461067423444087087733243 15691601135166130631599865)
        ·
          refine ⟨11768700851374597973699899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15691601135166130631599865 11768700851374597973699899)
          ·
            refine ⟨17653051277061896960549849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11768700851374597973699899 17653051277061896960549849)
            ·
              refine ⟨13239788457796422720412387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17653051277061896960549849 13239788457796422720412387)
              ·
                refine ⟨19859682686694634080618581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13239788457796422720412387 19859682686694634080618581)
                ·
                  refine ⟨232730656484702743132249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19859682686694634080618581 232730656484702743132249)
                  ·
                    rfl

theorem cell22_2039586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_2039586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039586 prefixEnd_2039586 := by exact prefixLift 2039586
  have htrace : WordTrace (prefixWord ++ tailWord_2039586) baseStart_2039586 baseEnd_2039586 := by
    simpa [prefixWord, tailWord_2039586, baseEnd_2039586] using wordTrace_append hprefix tailTrace_2039586
  have hstable : (prefixWord ++ tailWord_2039586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039586).length < 2 ^ (prefixWord ++ tailWord_2039586).sum := by decide
  have hdescent : baseEnd_2039586 < baseStart_2039586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039588 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_2039588 : Nat := 118140960795 + 2039588 * 2 ^ 59
def prefixEnd_2039588 : Nat := 4983230072969 + 3 ^ 40 * 2039588 * 2
def baseEnd_2039588 : Nat := 698192654094980890846741

theorem tailTrace_2039588 : CollatzResearch.WordTrace tailWord_2039588 prefixEnd_2039588 698192654094980890846741 := by
  unfold tailWord_2039588
  simp only [CollatzResearch.WordTrace]
  refine ⟨37194942867464242371615709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49593257156618989828820945 37194942867464242371615709)
  ·
    refine ⟨13948103575299090889355891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37194942867464242371615709 13948103575299090889355891)
    ·
      refine ⟨20922155362948636334033837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13948103575299090889355891 20922155362948636334033837)
      ·
        refine ⟨7845808261105738625262689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20922155362948636334033837 7845808261105738625262689)
        ·
          refine ⟨5884356195829303968947017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7845808261105738625262689 5884356195829303968947017)
          ·
            refine ⟨4413267146871977976710263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5884356195829303968947017 4413267146871977976710263)
            ·
              refine ⟨6619900720307966965065395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4413267146871977976710263 6619900720307966965065395)
              ·
                refine ⟨9929851080461950447598093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6619900720307966965065395 9929851080461950447598093)
                ·
                  refine ⟨3723694155173231417849285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9929851080461950447598093 3723694155173231417849285)
                  ·
                    refine ⟨698192654094980890846741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3723694155173231417849285 698192654094980890846741)
                    ·
                      rfl

theorem cell22_2039588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_2039588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039588 prefixEnd_2039588 := by exact prefixLift 2039588
  have htrace : WordTrace (prefixWord ++ tailWord_2039588) baseStart_2039588 baseEnd_2039588 := by
    simpa [prefixWord, tailWord_2039588, baseEnd_2039588] using wordTrace_append hprefix tailTrace_2039588
  have hstable : (prefixWord ++ tailWord_2039588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039588).length < 2 ^ (prefixWord ++ tailWord_2039588).sum := by decide
  have hdescent : baseEnd_2039588 < baseStart_2039588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039601 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 3, 5]
def baseStart_2039601 : Nat := 118140960795 + 2039601 * 2 ^ 59
def prefixEnd_2039601 : Nat := 4983230072969 + 3 ^ 40 * 2039601 * 2
def baseEnd_2039601 : Nat := 698197104260653190271701

theorem tailTrace_2039601 : CollatzResearch.WordTrace tailWord_2039601 prefixEnd_2039601 698197104260653190271701 := by
  unfold tailWord_2039601
  simp only [CollatzResearch.WordTrace]
  refine ⟨74390359883881387963454657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49593573255920925308969771 74390359883881387963454657)
  ·
    refine ⟨55792769912911040972590993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74390359883881387963454657 55792769912911040972590993)
    ·
      refine ⟨41844577434683280729443245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55792769912911040972590993 41844577434683280729443245)
      ·
        refine ⟨15691716538006230273541217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41844577434683280729443245 15691716538006230273541217)
        ·
          refine ⟨11768787403504672705155913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15691716538006230273541217 11768787403504672705155913)
          ·
            refine ⟨8826590552628504528866935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11768787403504672705155913 8826590552628504528866935)
            ·
              refine ⟨13239885828942756793300403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8826590552628504528866935 13239885828942756793300403)
              ·
                refine ⟨19859828743414135189950605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13239885828942756793300403 19859828743414135189950605)
                ·
                  refine ⟨7447435778780300696231477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19859828743414135189950605 7447435778780300696231477)
                  ·
                    refine ⟨698197104260653190271701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7447435778780300696231477 698197104260653190271701)
                    ·
                      rfl

theorem cell22_2039601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_2039601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039601 prefixEnd_2039601 := by exact prefixLift 2039601
  have htrace : WordTrace (prefixWord ++ tailWord_2039601) baseStart_2039601 baseEnd_2039601 := by
    simpa [prefixWord, tailWord_2039601, baseEnd_2039601] using wordTrace_append hprefix tailTrace_2039601
  have hstable : (prefixWord ++ tailWord_2039601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039601).length < 2 ^ (prefixWord ++ tailWord_2039601).sum := by decide
  have hdescent : baseEnd_2039601 < baseStart_2039601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039648 : List Nat := [2, 1, 1, 3, 3, 3, 3, 6]
def baseStart_2039648 : Nat := 118140960795 + 2039648 * 2 ^ 59
def prefixEnd_2039648 : Nat := 4983230072969 + 3 ^ 40 * 2039648 * 2
def baseEnd_2039648 : Nat := 77579243702351192705173

theorem tailTrace_2039648 : CollatzResearch.WordTrace tailWord_2039648 prefixEnd_2039648 77579243702351192705173 := by
  unfold tailWord_2039648
  simp only [CollatzResearch.WordTrace]
  refine ⟨37196037057355557495207799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49594716076474076660277065 37196037057355557495207799)
  ·
    refine ⟨55794055586033336242811699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37196037057355557495207799 55794055586033336242811699)
    ·
      refine ⟨83691083379050004364217549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55794055586033336242811699 83691083379050004364217549)
      ·
        refine ⟨31384156267143751636581581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83691083379050004364217549 31384156267143751636581581)
        ·
          refine ⟨11769058600178906863718093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31384156267143751636581581 11769058600178906863718093)
          ·
            refine ⟨4413396975067090073894285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11769058600178906863718093 4413396975067090073894285)
            ·
              refine ⟨1655023865650158777710357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4413396975067090073894285 1655023865650158777710357)
              ·
                refine ⟨77579243702351192705173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1655023865650158777710357 77579243702351192705173)
                ·
                  rfl

theorem cell22_2039648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 6].length) (baseStart_2039648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039648 prefixEnd_2039648 := by exact prefixLift 2039648
  have htrace : WordTrace (prefixWord ++ tailWord_2039648) baseStart_2039648 baseEnd_2039648 := by
    simpa [prefixWord, tailWord_2039648, baseEnd_2039648] using wordTrace_append hprefix tailTrace_2039648
  have hstable : (prefixWord ++ tailWord_2039648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039648).length < 2 ^ (prefixWord ++ tailWord_2039648).sum := by decide
  have hdescent : baseEnd_2039648 < baseStart_2039648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039650 : List Nat := [3, 3, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_2039650 : Nat := 118140960795 + 2039650 * 2 ^ 59
def prefixEnd_2039650 : Nat := 4983230072969 + 3 ^ 40 * 2039650 * 2
def baseEnd_2039650 : Nat := 698213877962033395796551

theorem tailTrace_2039650 : CollatzResearch.WordTrace tailWord_2039650 prefixEnd_2039650 698213877962033395796551 := by
  unfold tailWord_2039650
  simp only [CollatzResearch.WordTrace]
  refine ⟨18598036765175967332997101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49594764707135912887992269 18598036765175967332997101)
  ·
    refine ⟨6974263786940987749873913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18598036765175967332997101 6974263786940987749873913)
    ·
      refine ⟨5230697840205740812405435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6974263786940987749873913 5230697840205740812405435)
      ·
        refine ⟨7846046760308611218608153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5230697840205740812405435 7846046760308611218608153)
        ·
          refine ⟨5884535070231458413956115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7846046760308611218608153 5884535070231458413956115)
          ·
            refine ⟨8826802605347187620934173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5884535070231458413956115 8826802605347187620934173)
            ·
              refine ⟨3310050977005195357850315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8826802605347187620934173 3310050977005195357850315)
              ·
                refine ⟨4965076465507793036775473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3310050977005195357850315 4965076465507793036775473)
                ·
                  refine ⟨3723807349130844777581605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4965076465507793036775473 3723807349130844777581605)
                  ·
                    refine ⟨698213877962033395796551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3723807349130844777581605 698213877962033395796551)
                    ·
                      rfl

theorem cell22_2039650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_2039650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039650 prefixEnd_2039650 := by exact prefixLift 2039650
  have htrace : WordTrace (prefixWord ++ tailWord_2039650) baseStart_2039650 baseEnd_2039650 := by
    simpa [prefixWord, tailWord_2039650, baseEnd_2039650] using wordTrace_append hprefix tailTrace_2039650
  have hstable : (prefixWord ++ tailWord_2039650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039650).length < 2 ^ (prefixWord ++ tailWord_2039650).sum := by decide
  have hdescent : baseEnd_2039650 < baseStart_2039650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039680 : List Nat := [2, 1, 1, 2, 1, 2, 3, 6, 1, 3]
def baseStart_2039680 : Nat := 118140960795 + 2039680 * 2 ^ 59
def prefixEnd_2039680 : Nat := 4983230072969 + 3 ^ 40 * 2039680 * 2
def baseEnd_2039680 : Nat := 698224147575123317546459

theorem tailTrace_2039680 : CollatzResearch.WordTrace tailWord_2039680 prefixEnd_2039680 698224147575123317546459 := by
  unfold tailWord_2039680
  simp only [CollatzResearch.WordTrace]
  refine ⟨37196620625297592227790247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49595494167063456303720329 37196620625297592227790247)
  ·
    refine ⟨55794930937946388341685371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37196620625297592227790247 55794930937946388341685371)
    ·
      refine ⟨83692396406919582512528057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55794930937946388341685371 83692396406919582512528057)
      ·
        refine ⟨62769297305189686884396043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83692396406919582512528057 62769297305189686884396043)
        ·
          refine ⟨94153945957784530326594065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62769297305189686884396043 94153945957784530326594065)
          ·
            refine ⟨70615459468338397744945549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94153945957784530326594065 70615459468338397744945549)
            ·
              refine ⟨26480797300626899154354581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70615459468338397744945549 26480797300626899154354581)
              ·
                refine ⟨1241287373466885897860371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26480797300626899154354581 1241287373466885897860371)
                ·
                  refine ⟨1861931060200328846790557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1241287373466885897860371 1861931060200328846790557)
                  ·
                    refine ⟨698224147575123317546459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1861931060200328846790557 698224147575123317546459)
                    ·
                      rfl

theorem cell22_2039680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 1, 3].length) (baseStart_2039680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039680 prefixEnd_2039680 := by exact prefixLift 2039680
  have htrace : WordTrace (prefixWord ++ tailWord_2039680) baseStart_2039680 baseEnd_2039680 := by
    simpa [prefixWord, tailWord_2039680, baseEnd_2039680] using wordTrace_append hprefix tailTrace_2039680
  have hstable : (prefixWord ++ tailWord_2039680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039680).length < 2 ^ (prefixWord ++ tailWord_2039680).sum := by decide
  have hdescent : baseEnd_2039680 < baseStart_2039680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039770 : List Nat := [3, 1, 1, 2, 5, 1, 1, 2, 1, 5]
def baseStart_2039770 : Nat := 118140960795 + 2039770 * 2 ^ 59
def prefixEnd_2039770 : Nat := 4983230072969 + 3 ^ 40 * 2039770 * 2
def baseEnd_2039770 : Nat := 698254956414393082796183

theorem tailTrace_2039770 : CollatzResearch.WordTrace tailWord_2039770 prefixEnd_2039770 698254956414393082796183 := by
  unfold tailWord_2039770
  simp only [CollatzResearch.WordTrace]
  refine ⟨18599130955067282456589191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49597682546846086550904509 18599130955067282456589191)
  ·
    refine ⟨27898696432600923684883787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18599130955067282456589191 27898696432600923684883787)
    ·
      refine ⟨41848044648901385527325681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27898696432600923684883787 41848044648901385527325681)
      ·
        refine ⟨31386033486676039145494261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41848044648901385527325681 31386033486676039145494261)
        ·
          refine ⟨2942440639375878669890087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31386033486676039145494261 2942440639375878669890087)
          ·
            refine ⟨4413660959063818004835131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2942440639375878669890087 4413660959063818004835131)
            ·
              refine ⟨6620491438595727007252697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4413660959063818004835131 6620491438595727007252697)
              ·
                refine ⟨4965368578946795255439523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6620491438595727007252697 4965368578946795255439523)
                ·
                  refine ⟨7448052868420192883159285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4965368578946795255439523 7448052868420192883159285)
                  ·
                    refine ⟨698254956414393082796183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7448052868420192883159285 698254956414393082796183)
                    ·
                      rfl

theorem cell22_2039770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_2039770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039770 prefixEnd_2039770 := by exact prefixLift 2039770
  have htrace : WordTrace (prefixWord ++ tailWord_2039770) baseStart_2039770 baseEnd_2039770 := by
    simpa [prefixWord, tailWord_2039770, baseEnd_2039770] using wordTrace_append hprefix tailTrace_2039770
  have hstable : (prefixWord ++ tailWord_2039770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039770).length < 2 ^ (prefixWord ++ tailWord_2039770).sum := by decide
  have hdescent : baseEnd_2039770 < baseStart_2039770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039783 : List Nat := [1, 1, 5, 2, 3, 10]
def baseStart_2039783 : Nat := 118140960795 + 2039783 * 2 ^ 59
def prefixEnd_2039783 : Nat := 4983230072969 + 3 ^ 40 * 2039783 * 2
def baseEnd_2039783 : Nat := 8620486500988461508903

theorem tailTrace_2039783 : CollatzResearch.WordTrace tailWord_2039783 prefixEnd_2039783 8620486500988461508903 := by
  unfold tailWord_2039783
  simp only [CollatzResearch.WordTrace]
  refine ⟨74396997969222033046580003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49597998646148022031053335 74396997969222033046580003)
  ·
    refine ⟨111595496953833049569870005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74396997969222033046580003 111595496953833049569870005)
    ·
      refine ⟨10462077839421848397175313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111595496953833049569870005 10462077839421848397175313)
      ·
        refine ⟨7846558379566386297881485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10462077839421848397175313 7846558379566386297881485)
        ·
          refine ⟨2942459392337394861705557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7846558379566386297881485 2942459392337394861705557)
          ·
            refine ⟨8620486500988461508903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2942459392337394861705557 8620486500988461508903)
            ·
              rfl

theorem cell22_2039783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 10].length) (baseStart_2039783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039783 prefixEnd_2039783 := by exact prefixLift 2039783
  have htrace : WordTrace (prefixWord ++ tailWord_2039783) baseStart_2039783 baseEnd_2039783 := by
    simpa [prefixWord, tailWord_2039783, baseEnd_2039783] using wordTrace_append hprefix tailTrace_2039783
  have hstable : (prefixWord ++ tailWord_2039783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039783).length < 2 ^ (prefixWord ++ tailWord_2039783).sum := by decide
  have hdescent : baseEnd_2039783 < baseStart_2039783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039789 : List Nat := [1, 5, 1, 4, 1, 1, 1, 4, 4]
def baseStart_2039789 : Nat := 118140960795 + 2039789 * 2 ^ 59
def prefixEnd_2039789 : Nat := 4983230072969 + 3 ^ 40 * 2039789 * 2
def baseEnd_2039789 : Nat := 232753820167561122190375

theorem tailTrace_2039789 : CollatzResearch.WordTrace tailWord_2039789 prefixEnd_2039789 232753820167561122190375 := by
  unfold tailWord_2039789
  simp only [CollatzResearch.WordTrace]
  refine ⟨74397216807200296071298421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49598144538133530714198947 74397216807200296071298421)
  ·
    refine ⟨6974739075675027756684227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74397216807200296071298421 6974739075675027756684227)
    ·
      refine ⟨10462108613512541635026341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6974739075675027756684227 10462108613512541635026341)
      ·
        refine ⟨1961645365033601556567439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10462108613512541635026341 1961645365033601556567439)
        ·
          refine ⟨2942468047550402334851159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1961645365033601556567439 2942468047550402334851159)
          ·
            refine ⟨4413702071325603502276739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2942468047550402334851159 4413702071325603502276739)
            ·
              refine ⟨6620553106988405253415109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4413702071325603502276739 6620553106988405253415109)
              ·
                refine ⟨1241353707560325985015333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6620553106988405253415109 1241353707560325985015333)
                ·
                  refine ⟨232753820167561122190375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1241353707560325985015333 232753820167561122190375)
                  ·
                    rfl

theorem cell22_2039789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_2039789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039789 prefixEnd_2039789 := by exact prefixLift 2039789
  have htrace : WordTrace (prefixWord ++ tailWord_2039789) baseStart_2039789 baseEnd_2039789 := by
    simpa [prefixWord, tailWord_2039789, baseEnd_2039789] using wordTrace_append hprefix tailTrace_2039789
  have hstable : (prefixWord ++ tailWord_2039789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039789).length < 2 ^ (prefixWord ++ tailWord_2039789).sum := by decide
  have hdescent : baseEnd_2039789 < baseStart_2039789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039815 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 5, 3]
def baseStart_2039815 : Nat := 118140960795 + 2039815 * 2 ^ 59
def prefixEnd_2039815 : Nat := 4983230072969 + 3 ^ 40 * 2039815 * 2
def baseEnd_2039815 : Nat := 698270360834027965421045

theorem tailTrace_2039815 : CollatzResearch.WordTrace tailWord_2039815 prefixEnd_2039815 698270360834027965421045 := by
  unfold tailWord_2039815
  simp only [CollatzResearch.WordTrace]
  refine ⟨74398165105106102511744899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49598776736737401674496599 74398165105106102511744899)
  ·
    refine ⟨111597247657659153767617349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74398165105106102511744899 111597247657659153767617349)
    ·
      refine ⟨20924483935811091331428253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111597247657659153767617349 20924483935811091331428253)
      ·
        refine ⟨7846681475929159249285595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20924483935811091331428253 7846681475929159249285595)
        ·
          refine ⟨11770022213893738873928393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7846681475929159249285595 11770022213893738873928393)
          ·
            refine ⟨8827516660420304155446295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11770022213893738873928393 8827516660420304155446295)
            ·
              refine ⟨13241274990630456233169443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8827516660420304155446295 13241274990630456233169443)
              ·
                refine ⟨19861912485945684349754165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13241274990630456233169443 19861912485945684349754165)
                ·
                  refine ⟨1862054295557407907789453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19861912485945684349754165 1862054295557407907789453)
                  ·
                    refine ⟨698270360834027965421045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1862054295557407907789453 698270360834027965421045)
                    ·
                      rfl

theorem cell22_2039815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_2039815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039815 prefixEnd_2039815 := by exact prefixLift 2039815
  have htrace : WordTrace (prefixWord ++ tailWord_2039815) baseStart_2039815 baseEnd_2039815 := by
    simpa [prefixWord, tailWord_2039815, baseEnd_2039815] using wordTrace_append hprefix tailTrace_2039815
  have hstable : (prefixWord ++ tailWord_2039815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039815).length < 2 ^ (prefixWord ++ tailWord_2039815).sum := by decide
  have hdescent : baseEnd_2039815 < baseStart_2039815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039843 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 4, 5]
def baseStart_2039843 : Nat := 118140960795 + 2039843 * 2 ^ 59
def prefixEnd_2039843 : Nat := 4983230072969 + 3 ^ 40 * 2039843 * 2
def baseEnd_2039843 : Nat := 698279945806245225720959

theorem tailTrace_2039843 : CollatzResearch.WordTrace tailWord_2039843 prefixEnd_2039843 698279945806245225720959 := by
  unfold tailWord_2039843
  simp only [CollatzResearch.WordTrace]
  refine ⟨74399186349004663293764183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49599457566003108862509455 74399186349004663293764183)
  ·
    refine ⟨111598779523506994940646275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74399186349004663293764183 111598779523506994940646275)
    ·
      refine ⟨167398169285260492410969413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111598779523506994940646275 167398169285260492410969413)
      ·
        refine ⟨31387156740986342327056765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167398169285260492410969413 31387156740986342327056765)
        ·
          refine ⟨11770183777869878372646287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31387156740986342327056765 11770183777869878372646287)
          ·
            refine ⟨17655275666804817558969431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11770183777869878372646287 17655275666804817558969431)
            ·
              refine ⟨26482913500207226338454147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17655275666804817558969431 26482913500207226338454147)
              ·
                refine ⟨39724370250310839507681221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26482913500207226338454147 39724370250310839507681221)
                ·
                  refine ⟨7448319421933282407690229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39724370250310839507681221 7448319421933282407690229)
                  ·
                    refine ⟨698279945806245225720959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7448319421933282407690229 698279945806245225720959)
                    ·
                      rfl

theorem cell22_2039843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 5].length) (baseStart_2039843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039843 prefixEnd_2039843 := by exact prefixLift 2039843
  have htrace : WordTrace (prefixWord ++ tailWord_2039843) baseStart_2039843 baseEnd_2039843 := by
    simpa [prefixWord, tailWord_2039843, baseEnd_2039843] using wordTrace_append hprefix tailTrace_2039843
  have hstable : (prefixWord ++ tailWord_2039843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039843).length < 2 ^ (prefixWord ++ tailWord_2039843).sum := by decide
  have hdescent : baseEnd_2039843 < baseStart_2039843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039845 : List Nat := [1, 3, 1, 2, 2, 3, 3, 2, 5]
def baseStart_2039845 : Nat := 118140960795 + 2039845 * 2 ^ 59
def prefixEnd_2039845 : Nat := 4983230072969 + 3 ^ 40 * 2039845 * 2
def baseEnd_2039845 : Nat := 232760210149039295723651

theorem tailTrace_2039845 : CollatzResearch.WordTrace tailWord_2039845 prefixEnd_2039845 232760210149039295723651 := by
  unfold tailWord_2039845
  simp only [CollatzResearch.WordTrace]
  refine ⟨74399259294997417635336989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49599506196664945090224659 74399259294997417635336989)
  ·
    refine ⟨27899722235624031613251371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74399259294997417635336989 27899722235624031613251371)
    ·
      refine ⟨41849583353436047419877057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27899722235624031613251371 41849583353436047419877057)
      ·
        refine ⟨31387187515077035564907793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41849583353436047419877057 31387187515077035564907793)
        ·
          refine ⟨23540390636307776673680845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31387187515077035564907793 23540390636307776673680845)
          ·
            refine ⟨8827646488615416252630317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23540390636307776673680845 8827646488615416252630317)
            ·
              refine ⟨3310367433230781094736369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8827646488615416252630317 3310367433230781094736369)
              ·
                refine ⟨2482775574923085821052277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3310367433230781094736369 2482775574923085821052277)
                ·
                  refine ⟨232760210149039295723651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2482775574923085821052277 232760210149039295723651)
                  ·
                    rfl

theorem cell22_2039845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_2039845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039845 prefixEnd_2039845 := by exact prefixLift 2039845
  have htrace : WordTrace (prefixWord ++ tailWord_2039845) baseStart_2039845 baseEnd_2039845 := by
    simpa [prefixWord, tailWord_2039845, baseEnd_2039845] using wordTrace_append hprefix tailTrace_2039845
  have hstable : (prefixWord ++ tailWord_2039845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039845).length < 2 ^ (prefixWord ++ tailWord_2039845).sum := by decide
  have hdescent : baseEnd_2039845 < baseStart_2039845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039903 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 3, 6]
def baseStart_2039903 : Nat := 118140960795 + 2039903 * 2 ^ 59
def prefixEnd_2039903 : Nat := 4983230072969 + 3 ^ 40 * 2039903 * 2
def baseEnd_2039903 : Nat := 698300485032425069220775

theorem tailTrace_2039903 : CollatzResearch.WordTrace tailWord_2039903 prefixEnd_2039903 698300485032425069220775 := by
  unfold tailWord_2039903
  simp only [CollatzResearch.WordTrace]
  refine ⟨74401374728787293540948363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49600916485858195693965575 74401374728787293540948363)
  ·
    refine ⟨111602062093180940311422545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74401374728787293540948363 111602062093180940311422545)
    ·
      refine ⟨83701546569885705233566909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111602062093180940311422545 83701546569885705233566909)
      ·
        refine ⟨31388079963707139462587591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83701546569885705233566909 31388079963707139462587591)
        ·
          refine ⟨47082119945560709193881387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31388079963707139462587591 47082119945560709193881387)
          ·
            refine ⟨70623179918341063790822081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47082119945560709193881387 70623179918341063790822081)
            ·
              refine ⟨52967384938755797843116561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70623179918341063790822081 52967384938755797843116561)
              ·
                refine ⟨39725538704066848382337421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52967384938755797843116561 39725538704066848382337421)
                ·
                  refine ⟨14897077014025068143376533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39725538704066848382337421 14897077014025068143376533)
                  ·
                    refine ⟨698300485032425069220775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14897077014025068143376533 698300485032425069220775)
                    ·
                      rfl

theorem cell22_2039903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_2039903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039903 prefixEnd_2039903 := by exact prefixLift 2039903
  have htrace : WordTrace (prefixWord ++ tailWord_2039903) baseStart_2039903 baseEnd_2039903 := by
    simpa [prefixWord, tailWord_2039903, baseEnd_2039903] using wordTrace_append hprefix tailTrace_2039903
  have hstable : (prefixWord ++ tailWord_2039903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039903).length < 2 ^ (prefixWord ++ tailWord_2039903).sum := by decide
  have hdescent : baseEnd_2039903 < baseStart_2039903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039965 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_2039965 : Nat := 118140960795 + 2039965 * 2 ^ 59
def prefixEnd_2039965 : Nat := 4983230072969 + 3 ^ 40 * 2039965 * 2
def baseEnd_2039965 : Nat := 698321708899477574170585

theorem tailTrace_2039965 : CollatzResearch.WordTrace tailWord_2039965 prefixEnd_2039965 698321708899477574170585 := by
  unfold tailWord_2039965
  simp only [CollatzResearch.WordTrace]
  refine ⟨74403636054562678129705349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49602424036375118753136899 74403636054562678129705349)
  ·
    refine ⟨13950681760230502149319753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74403636054562678129705349 13950681760230502149319753)
    ·
      refine ⟨10463011320172876611989815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13950681760230502149319753 10463011320172876611989815)
      ·
        refine ⟨15694516980259314917984723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10463011320172876611989815 15694516980259314917984723)
        ·
          refine ⟨23541775470388972376977085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15694516980259314917984723 23541775470388972376977085)
          ·
            refine ⟨8828165801395864641366407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23541775470388972376977085 8828165801395864641366407)
            ·
              refine ⟨13242248702093796962049611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8828165801395864641366407 13242248702093796962049611)
              ·
                refine ⟨19863373053140695443074417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13242248702093796962049611 19863373053140695443074417)
                ·
                  refine ⟨14897529789855521582305813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19863373053140695443074417 14897529789855521582305813)
                  ·
                    refine ⟨698321708899477574170585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14897529789855521582305813 698321708899477574170585)
                    ·
                      rfl

theorem cell22_2039965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_2039965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2039965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2039965 prefixEnd_2039965 := by exact prefixLift 2039965
  have htrace : WordTrace (prefixWord ++ tailWord_2039965) baseStart_2039965 baseEnd_2039965 := by
    simpa [prefixWord, tailWord_2039965, baseEnd_2039965] using wordTrace_append hprefix tailTrace_2039965
  have hstable : (prefixWord ++ tailWord_2039965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039965).length < 2 ^ (prefixWord ++ tailWord_2039965).sum := by decide
  have hdescent : baseEnd_2039965 < baseStart_2039965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040014 : List Nat := [4, 1, 1, 1, 4, 3, 1, 2, 5]
def baseStart_2040014 : Nat := 118140960795 + 2040014 * 2 ^ 59
def prefixEnd_2040014 : Nat := 4983230072969 + 3 ^ 40 * 2040014 * 2
def baseEnd_2040014 : Nat := 232779494200285926565145

theorem tailTrace_2040014 : CollatzResearch.WordTrace tailWord_2040014 prefixEnd_2040014 232779494200285926565145 := by
  unfold tailWord_2040014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9300677903923144937279887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49603615487590106332159397 9300677903923144937279887)
  ·
    refine ⟨13951016855884717405919831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9300677903923144937279887 13951016855884717405919831)
    ·
      refine ⟨20926525283827076108879747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13951016855884717405919831 20926525283827076108879747)
      ·
        refine ⟨31389787925740614163319621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20926525283827076108879747 31389787925740614163319621)
        ·
          refine ⟨5885585236076365155622429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31389787925740614163319621 5885585236076365155622429)
          ·
            refine ⟨2207094463528636933358411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5885585236076365155622429 2207094463528636933358411)
            ·
              refine ⟨3310641695292955400037617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2207094463528636933358411 3310641695292955400037617)
              ·
                refine ⟨2482981271469716550028213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3310641695292955400037617 2482981271469716550028213)
                ·
                  refine ⟨232779494200285926565145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2482981271469716550028213 232779494200285926565145)
                  ·
                    rfl

theorem cell22_2040014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_2040014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040014 prefixEnd_2040014 := by exact prefixLift 2040014
  have htrace : WordTrace (prefixWord ++ tailWord_2040014) baseStart_2040014 baseEnd_2040014 := by
    simpa [prefixWord, tailWord_2040014, baseEnd_2040014] using wordTrace_append hprefix tailTrace_2040014
  have hstable : (prefixWord ++ tailWord_2040014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040014).length < 2 ^ (prefixWord ++ tailWord_2040014).sum := by decide
  have hdescent : baseEnd_2040014 < baseStart_2040014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040025 : List Nat := [1, 2, 1, 2, 3, 1, 3, 3, 6]
def baseStart_2040025 : Nat := 118140960795 + 2040025 * 2 ^ 59
def prefixEnd_2040025 : Nat := 4983230072969 + 3 ^ 40 * 2040025 * 2
def baseEnd_2040025 : Nat := 232780749375219139223467

theorem tailTrace_2040025 : CollatzResearch.WordTrace tailWord_2040025 prefixEnd_2040025 232780749375219139223467 := by
  unfold tailWord_2040025
  simp only [CollatzResearch.WordTrace]
  refine ⟨74405824434345308376889529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49603882956230205584593019 74405824434345308376889529)
  ·
    refine ⟨55804368325758981282667147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74405824434345308376889529 55804368325758981282667147)
    ·
      refine ⟨83706552488638471924000721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55804368325758981282667147 83706552488638471924000721)
      ·
        refine ⟨62779914366478853943000541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83706552488638471924000721 62779914366478853943000541)
        ·
          refine ⟨23542467887429570228625203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62779914366478853943000541 23542467887429570228625203)
          ·
            refine ⟨35313701831144355342937805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23542467887429570228625203 35313701831144355342937805)
            ·
              refine ⟨13242638186679133253601677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35313701831144355342937805 13242638186679133253601677)
              ·
                refine ⟨4965989320004674970100629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13242638186679133253601677 4965989320004674970100629)
                ·
                  refine ⟨232780749375219139223467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4965989320004674970100629 232780749375219139223467)
                  ·
                    rfl

theorem cell22_2040025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 6].length) (baseStart_2040025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040025 prefixEnd_2040025 := by exact prefixLift 2040025
  have htrace : WordTrace (prefixWord ++ tailWord_2040025) baseStart_2040025 baseEnd_2040025 := by
    simpa [prefixWord, tailWord_2040025, baseEnd_2040025] using wordTrace_append hprefix tailTrace_2040025
  have hstable : (prefixWord ++ tailWord_2040025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040025).length < 2 ^ (prefixWord ++ tailWord_2040025).sum := by decide
  have hdescent : baseEnd_2040025 < baseStart_2040025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040072 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 4, 4]
def baseStart_2040072 : Nat := 118140960795 + 2040072 * 2 ^ 59
def prefixEnd_2040072 : Nat := 4983230072969 + 3 ^ 40 * 2040072 * 2
def baseEnd_2040072 : Nat := 698358337186164961745257

theorem tailTrace_2040072 : CollatzResearch.WordTrace tailWord_2040072 prefixEnd_2040072 698358337186164961745257 := by
  unfold tailWord_2040072
  simp only [CollatzResearch.WordTrace]
  refine ⟨37203769332587517701925235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49605025776783356935900313 37203769332587517701925235)
  ·
    refine ⟨55805653998881276552887853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37203769332587517701925235 55805653998881276552887853)
    ·
      refine ⟨20927120249580478707332945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55805653998881276552887853 20927120249580478707332945)
      ·
        refine ⟨15695340187185359030499709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20927120249580478707332945 15695340187185359030499709)
        ·
          refine ⟨5885752570194509636437391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15695340187185359030499709 5885752570194509636437391)
          ·
            refine ⟨8828628855291764454656087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5885752570194509636437391 8828628855291764454656087)
            ·
              refine ⟨13242943282937646681984131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8828628855291764454656087 13242943282937646681984131)
              ·
                refine ⟨19864414924406470022976197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13242943282937646681984131 19864414924406470022976197)
                ·
                  refine ⟨3724577798326213129308037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19864414924406470022976197 3724577798326213129308037)
                  ·
                    refine ⟨698358337186164961745257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3724577798326213129308037 698358337186164961745257)
                    ·
                      rfl

theorem cell22_2040072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_2040072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040072 prefixEnd_2040072 := by exact prefixLift 2040072
  have htrace : WordTrace (prefixWord ++ tailWord_2040072) baseStart_2040072 baseEnd_2040072 := by
    simpa [prefixWord, tailWord_2040072, baseEnd_2040072] using wordTrace_append hprefix tailTrace_2040072
  have hstable : (prefixWord ++ tailWord_2040072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040072).length < 2 ^ (prefixWord ++ tailWord_2040072).sum := by decide
  have hdescent : baseEnd_2040072 < baseStart_2040072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040087 : List Nat := [1, 1, 3, 4, 1, 3, 2, 7]
def baseStart_2040087 : Nat := 118140960795 + 2040087 * 2 ^ 59
def prefixEnd_2040087 : Nat := 4983230072969 + 3 ^ 40 * 2040087 * 2
def baseEnd_2040087 : Nat := 77595941332523324735579

theorem tailTrace_2040087 : CollatzResearch.WordTrace tailWord_2040087 prefixEnd_2040087 77595941332523324735579 := by
  unfold tailWord_2040087
  simp only [CollatzResearch.WordTrace]
  refine ⟨74408085760120692965646515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49605390506747128643764343 74408085760120692965646515)
  ·
    refine ⟨111612128640181039448469773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74408085760120692965646515 111612128640181039448469773)
    ·
      refine ⟨41854548240067889793176165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111612128640181039448469773 41854548240067889793176165)
      ·
        refine ⟨7847727795012729336220531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41854548240067889793176165 7847727795012729336220531)
        ·
          refine ⟨11771591692519094004330797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7847727795012729336220531 11771591692519094004330797)
          ·
            refine ⟨4414346884694660251624049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11771591692519094004330797 4414346884694660251624049)
            ·
              refine ⟨3310760163520995188718037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4414346884694660251624049 3310760163520995188718037)
              ·
                refine ⟨77595941332523324735579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3310760163520995188718037 77595941332523324735579)
                ·
                  rfl

theorem cell22_2040087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 7].length) (baseStart_2040087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040087 prefixEnd_2040087 := by exact prefixLift 2040087
  have htrace : WordTrace (prefixWord ++ tailWord_2040087) baseStart_2040087 baseEnd_2040087 := by
    simpa [prefixWord, tailWord_2040087, baseEnd_2040087] using wordTrace_append hprefix tailTrace_2040087
  have hstable : (prefixWord ++ tailWord_2040087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040087).length < 2 ^ (prefixWord ++ tailWord_2040087).sum := by decide
  have hdescent : baseEnd_2040087 < baseStart_2040087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040106 : List Nat := [3, 1, 4, 2, 2, 1, 2, 1, 2, 4]
def baseStart_2040106 : Nat := 118140960795 + 2040106 * 2 ^ 59
def prefixEnd_2040106 : Nat := 4983230072969 + 3 ^ 40 * 2040106 * 2
def baseEnd_2040106 : Nat := 698369976081000206395153

theorem tailTrace_2040106 : CollatzResearch.WordTrace tailWord_2040106 prefixEnd_2040106 698369976081000206395153 := by
  unfold tailWord_2040106
  simp only [CollatzResearch.WordTrace]
  refine ⟨18602194686762964802647043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49605852498034572807058781 18602194686762964802647043)
  ·
    refine ⟨27903292030144447203970565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18602194686762964802647043 27903292030144447203970565)
    ·
      refine ⟨5231867255652083850744481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27903292030144447203970565 5231867255652083850744481)
      ·
        refine ⟨3923900441739062888058361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5231867255652083850744481 3923900441739062888058361)
        ·
          refine ⟨2942925331304297166043771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3923900441739062888058361 2942925331304297166043771)
          ·
            refine ⟨4414387996956445749065657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2942925331304297166043771 4414387996956445749065657)
            ·
              refine ⟨3310790997717334311799243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4414387996956445749065657 3310790997717334311799243)
              ·
                refine ⟨4966186496576001467698865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3310790997717334311799243 4966186496576001467698865)
                ·
                  refine ⟨3724639872432001100774149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4966186496576001467698865 3724639872432001100774149)
                  ·
                    refine ⟨698369976081000206395153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3724639872432001100774149 698369976081000206395153)
                    ·
                      rfl

theorem cell22_2040106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_2040106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040106 prefixEnd_2040106 := by exact prefixLift 2040106
  have htrace : WordTrace (prefixWord ++ tailWord_2040106) baseStart_2040106 baseEnd_2040106 := by
    simpa [prefixWord, tailWord_2040106, baseEnd_2040106] using wordTrace_append hprefix tailTrace_2040106
  have hstable : (prefixWord ++ tailWord_2040106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040106).length < 2 ^ (prefixWord ++ tailWord_2040106).sum := by decide
  have hdescent : baseEnd_2040106 < baseStart_2040106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040301 : List Nat := [1, 5, 1, 3, 1, 1, 1, 4, 5]
def baseStart_2040301 : Nat := 118140960795 + 2040301 * 2 ^ 59
def prefixEnd_2040301 : Nat := 4983230072969 + 3 ^ 40 * 2040301 * 2
def baseEnd_2040301 : Nat := 232812242855361565923185

theorem tailTrace_2040301 : CollatzResearch.WordTrace tailWord_2040301 prefixEnd_2040301 232812242855361565923185 := by
  unfold tailWord_2040301
  simp only [CollatzResearch.WordTrace]
  refine ⟨74415890981345407513936757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49610593987563605009291171 74415890981345407513936757)
  ·
    refine ⟨6976489779501131954431571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74415890981345407513936757 6976489779501131954431571)
    ·
      refine ⟨10464734669251697931647357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6976489779501131954431571 10464734669251697931647357)
      ·
        refine ⟨3924275500969386724367759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10464734669251697931647357 3924275500969386724367759)
        ·
          refine ⟨5886413251454080086551639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3924275500969386724367759 5886413251454080086551639)
          ·
            refine ⟨8829619877181120129827459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5886413251454080086551639 8829619877181120129827459)
            ·
              refine ⟨13244429815771680194741189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8829619877181120129827459 13244429815771680194741189)
              ·
                refine ⟨2483330590457190036513973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13244429815771680194741189 2483330590457190036513973)
                ·
                  refine ⟨232812242855361565923185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2483330590457190036513973 232812242855361565923185)
                  ·
                    rfl

theorem cell22_2040301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_2040301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040301 prefixEnd_2040301 := by exact prefixLift 2040301
  have htrace : WordTrace (prefixWord ++ tailWord_2040301) baseStart_2040301 baseEnd_2040301 := by
    simpa [prefixWord, tailWord_2040301, baseEnd_2040301] using wordTrace_append hprefix tailTrace_2040301
  have hstable : (prefixWord ++ tailWord_2040301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040301).length < 2 ^ (prefixWord ++ tailWord_2040301).sum := by decide
  have hdescent : baseEnd_2040301 < baseStart_2040301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040346 : List Nat := [3, 1, 1, 3, 1, 1, 3, 5, 4]
def baseStart_2040346 : Nat := 118140960795 + 2040346 * 2 ^ 59
def prefixEnd_2040346 : Nat := 4983230072969 + 3 ^ 40 * 2040346 * 2
def baseEnd_2040346 : Nat := 232817377661906526798139

theorem tailTrace_2040346 : CollatzResearch.WordTrace tailWord_2040346 prefixEnd_2040346 232817377661906526798139 := by
  unfold tailWord_2040346
  simp only [CollatzResearch.WordTrace]
  refine ⟨18604383066545595049831223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49611688177454920132883261 18604383066545595049831223)
  ·
    refine ⟨27906574599818392574746835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18604383066545595049831223 27906574599818392574746835)
    ·
      refine ⟨41859861899727588862120253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27906574599818392574746835 41859861899727588862120253)
      ·
        refine ⟨15697448212397845823295095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41859861899727588862120253 15697448212397845823295095)
        ·
          refine ⟨23546172318596768734942643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15697448212397845823295095 23546172318596768734942643)
          ·
            refine ⟨35319258477895153102413965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23546172318596768734942643 35319258477895153102413965)
            ·
              refine ⟨13244721929210682413405237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35319258477895153102413965 13244721929210682413405237)
              ·
                refine ⟨1241692680863501476256741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13244721929210682413405237 1241692680863501476256741)
                ·
                  refine ⟨232817377661906526798139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1241692680863501476256741 232817377661906526798139)
                  ·
                    rfl

theorem cell22_2040346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_2040346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040346 prefixEnd_2040346 := by exact prefixLift 2040346
  have htrace : WordTrace (prefixWord ++ tailWord_2040346) baseStart_2040346 baseEnd_2040346 := by
    simpa [prefixWord, tailWord_2040346, baseEnd_2040346] using wordTrace_append hprefix tailTrace_2040346
  have hstable : (prefixWord ++ tailWord_2040346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040346).length < 2 ^ (prefixWord ++ tailWord_2040346).sum := by decide
  have hdescent : baseEnd_2040346 < baseStart_2040346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040348 : List Nat := [2, 2, 3, 1, 2, 2, 4, 1, 1, 4]
def baseStart_2040348 : Nat := 118140960795 + 2040348 * 2 ^ 59
def prefixEnd_2040348 : Nat := 4983230072969 + 3 ^ 40 * 2040348 * 2
def baseEnd_2040348 : Nat := 698452817626592241844411

theorem tailTrace_2040348 : CollatzResearch.WordTrace tailWord_2040348 prefixEnd_2040348 698452817626592241844411 := by
  unfold tailWord_2040348
  simp only [CollatzResearch.WordTrace]
  refine ⟨37208802606087567270448849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49611736808116756360598465 37208802606087567270448849)
  ·
    refine ⟨27906601954565675452836637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37208802606087567270448849 27906601954565675452836637)
    ·
      refine ⟨10464975732962128294813739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27906601954565675452836637 10464975732962128294813739)
      ·
        refine ⟨15697463599443192442220609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10464975732962128294813739 15697463599443192442220609)
        ·
          refine ⟨11773097699582394331665457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15697463599443192442220609 11773097699582394331665457)
          ·
            refine ⟨8829823274686795748749093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11773097699582394331665457 8829823274686795748749093)
            ·
              refine ⟨1655591864003774202890455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8829823274686795748749093 1655591864003774202890455)
              ·
                refine ⟨2483387796005661304335683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655591864003774202890455 2483387796005661304335683)
                ·
                  refine ⟨3725081694008491956503525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2483387796005661304335683 3725081694008491956503525)
                  ·
                    refine ⟨698452817626592241844411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3725081694008491956503525 698452817626592241844411)
                    ·
                      rfl

theorem cell22_2040348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_2040348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040348 prefixEnd_2040348 := by exact prefixLift 2040348
  have htrace : WordTrace (prefixWord ++ tailWord_2040348) baseStart_2040348 baseEnd_2040348 := by
    simpa [prefixWord, tailWord_2040348, baseEnd_2040348] using wordTrace_append hprefix tailTrace_2040348
  have hstable : (prefixWord ++ tailWord_2040348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040348).length < 2 ^ (prefixWord ++ tailWord_2040348).sum := by decide
  have hdescent : baseEnd_2040348 < baseStart_2040348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040391 : List Nat := [1, 1, 4, 1, 4, 1, 4, 6]
def baseStart_2040391 : Nat := 118140960795 + 2040391 * 2 ^ 59
def prefixEnd_2040391 : Nat := 4983230072969 + 3 ^ 40 * 2040391 * 2
def baseEnd_2040391 : Nat := 77607504156150495891031

theorem tailTrace_2040391 : CollatzResearch.WordTrace tailWord_2040391 prefixEnd_2040391 77607504156150495891031 := by
  unfold tailWord_2040391
  simp only [CollatzResearch.WordTrace]
  refine ⟨74419173551019352884713027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49612782367346235256475351 74419173551019352884713027)
  ·
    refine ⟨111628760326529029327069541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74419173551019352884713027 111628760326529029327069541)
    ·
      refine ⟨20930392561224192998825539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111628760326529029327069541 20930392561224192998825539)
      ·
        refine ⟨31395588841836289498238309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20930392561224192998825539 31395588841836289498238309)
        ·
          refine ⟨5886672907844304280919683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31395588841836289498238309 5886672907844304280919683)
          ·
            refine ⟨8830009361766456421379525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5886672907844304280919683 8830009361766456421379525)
            ·
              refine ⟨1655626755331210579008661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8830009361766456421379525 1655626755331210579008661)
              ·
                refine ⟨77607504156150495891031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1655626755331210579008661 77607504156150495891031)
                ·
                  rfl

theorem cell22_2040391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 6].length) (baseStart_2040391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040391 prefixEnd_2040391 := by exact prefixLift 2040391
  have htrace : WordTrace (prefixWord ++ tailWord_2040391) baseStart_2040391 baseEnd_2040391 := by
    simpa [prefixWord, tailWord_2040391, baseEnd_2040391] using wordTrace_append hprefix tailTrace_2040391
  have hstable : (prefixWord ++ tailWord_2040391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040391).length < 2 ^ (prefixWord ++ tailWord_2040391).sum := by decide
  have hdescent : baseEnd_2040391 < baseStart_2040391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040414 : List Nat := [4, 4, 1, 2, 2, 1, 1, 1, 6]
def baseStart_2040414 : Nat := 118140960795 + 2040414 * 2 ^ 59
def prefixEnd_2040414 : Nat := 4983230072969 + 3 ^ 40 * 2040414 * 2
def baseEnd_2040414 : Nat := 232825136925130023231403

theorem tailTrace_2040414 : CollatzResearch.WordTrace tailWord_2040414 prefixEnd_2040414 232825136925130023231403 := by
  unfold tailWord_2040414
  simp only [CollatzResearch.WordTrace]
  refine ⟨9302501553742003476600037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49613341619957351875200197 9302501553742003476600037)
  ·
    refine ⟨1744219041326625651862507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9302501553742003476600037 1744219041326625651862507)
    ·
      refine ⟨2616328561989938477793761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1744219041326625651862507 2616328561989938477793761)
      ·
        refine ⟨1962246421492453858345321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2616328561989938477793761 1962246421492453858345321)
        ·
          refine ⟨1471684816119340393758991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1962246421492453858345321 1471684816119340393758991)
          ·
            refine ⟨2207527224179010590638487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1471684816119340393758991 2207527224179010590638487)
            ·
              refine ⟨3311290836268515885957731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2207527224179010590638487 3311290836268515885957731)
              ·
                refine ⟨4966936254402773828936597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3311290836268515885957731 4966936254402773828936597)
                ·
                  refine ⟨232825136925130023231403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4966936254402773828936597 232825136925130023231403)
                  ·
                    rfl

theorem cell22_2040414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_2040414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040414 prefixEnd_2040414 := by exact prefixLift 2040414
  have htrace : WordTrace (prefixWord ++ tailWord_2040414) baseStart_2040414 baseEnd_2040414 := by
    simpa [prefixWord, tailWord_2040414, baseEnd_2040414] using wordTrace_append hprefix tailTrace_2040414
  have hstable : (prefixWord ++ tailWord_2040414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040414).length < 2 ^ (prefixWord ++ tailWord_2040414).sum := by decide
  have hdescent : baseEnd_2040414 < baseStart_2040414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040419 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 7]
def baseStart_2040419 : Nat := 118140960795 + 2040419 * 2 ^ 59
def prefixEnd_2040419 : Nat := 4983230072969 + 3 ^ 40 * 2040419 * 2
def baseEnd_2040419 : Nat := 232825707459190574439731

theorem tailTrace_2040419 : CollatzResearch.WordTrace tailWord_2040419 prefixEnd_2040419 232825707459190574439731 := by
  unfold tailWord_2040419
  simp only [CollatzResearch.WordTrace]
  refine ⟨74420194794917913666732311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49613463196611942444488207 74420194794917913666732311)
  ·
    refine ⟨111630292192376870500098467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74420194794917913666732311 111630292192376870500098467)
    ·
      refine ⟨167445438288565305750147701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111630292192376870500098467 167445438288565305750147701)
      ·
        refine ⟨15698009839552997414076347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167445438288565305750147701 15698009839552997414076347)
        ·
          refine ⟨23547014759329496121114521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15698009839552997414076347 23547014759329496121114521)
          ·
            refine ⟨17660261069497122090835891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23547014759329496121114521 17660261069497122090835891)
            ·
              refine ⟨26490391604245683136253837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17660261069497122090835891 26490391604245683136253837)
              ·
                refine ⟨9933896851592131176095189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26490391604245683136253837 9933896851592131176095189)
                ·
                  refine ⟨232825707459190574439731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9933896851592131176095189 232825707459190574439731)
                  ·
                    rfl

theorem cell22_2040419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 7].length) (baseStart_2040419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040419 prefixEnd_2040419 := by exact prefixLift 2040419
  have htrace : WordTrace (prefixWord ++ tailWord_2040419) baseStart_2040419 baseEnd_2040419 := by
    simpa [prefixWord, tailWord_2040419, baseEnd_2040419] using wordTrace_append hprefix tailTrace_2040419
  have hstable : (prefixWord ++ tailWord_2040419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040419).length < 2 ^ (prefixWord ++ tailWord_2040419).sum := by decide
  have hdescent : baseEnd_2040419 < baseStart_2040419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040496 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 6, 3]
def baseStart_2040496 : Nat := 118140960795 + 2040496 * 2 ^ 59
def prefixEnd_2040496 : Nat := 4983230072969 + 3 ^ 40 * 2040496 * 2
def baseEnd_2040496 : Nat := 698503481051169189143957

theorem tailTrace_2040496 : CollatzResearch.WordTrace tailWord_2040496 prefixEnd_2040496 698503481051169189143957 := by
  unfold tailWord_2040496
  simp only [CollatzResearch.WordTrace]
  refine ⟨37211501607819477908642671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49615335477092637211523561 37211501607819477908642671)
  ·
    refine ⟨55817252411729216862964007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37211501607819477908642671 55817252411729216862964007)
    ·
      refine ⟨83725878617593825294446011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55817252411729216862964007 83725878617593825294446011)
      ·
        refine ⟨125588817926390737941669017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83725878617593825294446011 125588817926390737941669017)
        ·
          refine ⟨94191613444793053456251763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125588817926390737941669017 94191613444793053456251763)
          ·
            refine ⟨141287420167189580184377645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94191613444793053456251763 141287420167189580184377645)
            ·
              refine ⟨52982782562696092569141617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141287420167189580184377645 52982782562696092569141617)
              ·
                refine ⟨39737086922022069426856213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52982782562696092569141617 39737086922022069426856213)
                ·
                  refine ⟨1862675949469784504383885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39737086922022069426856213 1862675949469784504383885)
                  ·
                    refine ⟨698503481051169189143957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1862675949469784504383885 698503481051169189143957)
                    ·
                      rfl

theorem cell22_2040496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 6, 3].length) (baseStart_2040496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040496 prefixEnd_2040496 := by exact prefixLift 2040496
  have htrace : WordTrace (prefixWord ++ tailWord_2040496) baseStart_2040496 baseEnd_2040496 := by
    simpa [prefixWord, tailWord_2040496, baseEnd_2040496] using wordTrace_append hprefix tailTrace_2040496
  have hstable : (prefixWord ++ tailWord_2040496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040496).length < 2 ^ (prefixWord ++ tailWord_2040496).sum := by decide
  have hdescent : baseEnd_2040496 < baseStart_2040496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040511 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 1, 6]
def baseStart_2040511 : Nat := 118140960795 + 2040511 * 2 ^ 59
def prefixEnd_2040511 : Nat := 4983230072969 + 3 ^ 40 * 2040511 * 2
def baseEnd_2040511 : Nat := 698508615857714150018911

theorem tailTrace_2040511 : CollatzResearch.WordTrace tailWord_2040511 prefixEnd_2040511 698508615857714150018911 := by
  unfold tailWord_2040511
  simp only [CollatzResearch.WordTrace]
  refine ⟨74423550310584613379081387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49615700207056408919387591 74423550310584613379081387)
  ·
    refine ⟨111635325465876920068622081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74423550310584613379081387 111635325465876920068622081)
    ·
      refine ⟨83726494099407690051466561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111635325465876920068622081 83726494099407690051466561)
      ·
        refine ⟨62794870574555767538599921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83726494099407690051466561 62794870574555767538599921)
        ·
          refine ⟨47096152930916825653949941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62794870574555767538599921 47096152930916825653949941)
          ·
            refine ⟨4415264337273452405057807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47096152930916825653949941 4415264337273452405057807)
            ·
              refine ⟨6622896505910178607586711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4415264337273452405057807 6622896505910178607586711)
              ·
                refine ⟨9934344758865267911380067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6622896505910178607586711 9934344758865267911380067)
                ·
                  refine ⟨14901517138297901867070101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9934344758865267911380067 14901517138297901867070101)
                  ·
                    refine ⟨698508615857714150018911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14901517138297901867070101 698508615857714150018911)
                    ·
                      rfl

theorem cell22_2040511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_2040511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040511 prefixEnd_2040511 := by exact prefixLift 2040511
  have htrace : WordTrace (prefixWord ++ tailWord_2040511) baseStart_2040511 baseEnd_2040511 := by
    simpa [prefixWord, tailWord_2040511, baseEnd_2040511] using wordTrace_append hprefix tailTrace_2040511
  have hstable : (prefixWord ++ tailWord_2040511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040511).length < 2 ^ (prefixWord ++ tailWord_2040511).sum := by decide
  have hdescent : baseEnd_2040511 < baseStart_2040511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040526 : List Nat := [4, 1, 1, 1, 3, 3, 9]
def baseStart_2040526 : Nat := 118140960795 + 2040526 * 2 ^ 59
def prefixEnd_2040526 : Nat := 4983230072969 + 3 ^ 40 * 2040526 * 2
def baseEnd_2040526 : Nat := 25870879654231818921995

theorem tailTrace_2040526 : CollatzResearch.WordTrace tailWord_2040526 prefixEnd_2040526 25870879654231818921995 := by
  unfold tailWord_2040526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9303012175691283867609679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49616064937020180627251621 9303012175691283867609679)
  ·
    refine ⟨13954518263536925801414519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9303012175691283867609679 13954518263536925801414519)
    ·
      refine ⟨20931777395305388702121779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13954518263536925801414519 20931777395305388702121779)
      ·
        refine ⟨31397666092958083053182669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20931777395305388702121779 31397666092958083053182669)
        ·
          refine ⟨11774124784859281144943501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31397666092958083053182669 11774124784859281144943501)
          ·
            refine ⟨4415296794322230429353813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11774124784859281144943501 4415296794322230429353813)
            ·
              refine ⟨25870879654231818921995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4415296794322230429353813 25870879654231818921995)
              ·
                rfl

theorem cell22_2040526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 9].length) (baseStart_2040526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040526 prefixEnd_2040526 := by exact prefixLift 2040526
  have htrace : WordTrace (prefixWord ++ tailWord_2040526) baseStart_2040526 baseEnd_2040526 := by
    simpa [prefixWord, tailWord_2040526, baseEnd_2040526] using wordTrace_append hprefix tailTrace_2040526
  have hstable : (prefixWord ++ tailWord_2040526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040526).length < 2 ^ (prefixWord ++ tailWord_2040526).sum := by decide
  have hdescent : baseEnd_2040526 < baseStart_2040526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040530 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 4, 3]
def baseStart_2040530 : Nat := 118140960795 + 2040530 * 2 ^ 59
def prefixEnd_2040530 : Nat := 4983230072969 + 3 ^ 40 * 2040530 * 2
def baseEnd_2040530 : Nat := 698515119946004433793853

theorem tailTrace_2040530 : CollatzResearch.WordTrace tailWord_2040530 prefixEnd_2040530 698515119946004433793853 := by
  unfold tailWord_2040530
  simp only [CollatzResearch.WordTrace]
  refine ⟨18606060824378944906005761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49616162198343853082682029 18606060824378944906005761)
  ·
    refine ⟨13954545618284208679504321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18606060824378944906005761 13954545618284208679504321)
    ·
      refine ⟨10465909213713156509628241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13954545618284208679504321 10465909213713156509628241)
      ·
        refine ⟨7849431910284867382221181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10465909213713156509628241 7849431910284867382221181)
        ·
          refine ⟨2943536966356825268332943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7849431910284867382221181 2943536966356825268332943)
          ·
            refine ⟨4415305449535237902499415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2943536966356825268332943 4415305449535237902499415)
            ·
              refine ⟨6622958174302856853749123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4415305449535237902499415 6622958174302856853749123)
              ·
                refine ⟨9934437261454285280623685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6622958174302856853749123 9934437261454285280623685)
                ·
                  refine ⟨1862706986522678490116941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9934437261454285280623685 1862706986522678490116941)
                  ·
                    refine ⟨698515119946004433793853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1862706986522678490116941 698515119946004433793853)
                    ·
                      rfl

theorem cell22_2040530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_2040530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040530 prefixEnd_2040530 := by exact prefixLift 2040530
  have htrace : WordTrace (prefixWord ++ tailWord_2040530) baseStart_2040530 baseEnd_2040530 := by
    simpa [prefixWord, tailWord_2040530, baseEnd_2040530] using wordTrace_append hprefix tailTrace_2040530
  have hstable : (prefixWord ++ tailWord_2040530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040530).length < 2 ^ (prefixWord ++ tailWord_2040530).sum := by decide
  have hdescent : baseEnd_2040530 < baseStart_2040530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040547 : List Nat := [1, 1, 1, 7, 1, 2, 3, 1, 2, 3]
def baseStart_2040547 : Nat := 118140960795 + 2040547 * 2 ^ 59
def prefixEnd_2040547 : Nat := 4983230072969 + 3 ^ 40 * 2040547 * 2
def baseEnd_2040547 : Nat := 698520939393422056118801

theorem tailTrace_2040547 : CollatzResearch.WordTrace tailWord_2040547 prefixEnd_2040547 698520939393422056118801 := by
  unfold tailWord_2040547
  simp only [CollatzResearch.WordTrace]
  refine ⟨74424863338454191527391895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49616575558969461018261263 74424863338454191527391895)
  ·
    refine ⟨111637295007681287291087843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74424863338454191527391895 111637295007681287291087843)
    ·
      refine ⟨167455942511521930936631765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111637295007681287291087843 167455942511521930936631765)
      ·
        refine ⟨3924748652613795256327307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 167455942511521930936631765 3924748652613795256327307)
        ·
          refine ⟨5887122978920692884490961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3924748652613795256327307 5887122978920692884490961)
          ·
            refine ⟨4415342234190519663368221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5887122978920692884490961 4415342234190519663368221)
            ·
              refine ⟨1655753337821444873763083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4415342234190519663368221 1655753337821444873763083)
              ·
                refine ⟨2483630006732167310644625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655753337821444873763083 2483630006732167310644625)
                ·
                  refine ⟨1862722505049125482983469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2483630006732167310644625 1862722505049125482983469)
                  ·
                    refine ⟨698520939393422056118801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1862722505049125482983469 698520939393422056118801)
                    ·
                      rfl

theorem cell22_2040547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 2, 3].length) (baseStart_2040547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040547 prefixEnd_2040547 := by exact prefixLift 2040547
  have htrace : WordTrace (prefixWord ++ tailWord_2040547) baseStart_2040547 baseEnd_2040547 := by
    simpa [prefixWord, tailWord_2040547, baseEnd_2040547] using wordTrace_append hprefix tailTrace_2040547
  have hstable : (prefixWord ++ tailWord_2040547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040547).length < 2 ^ (prefixWord ++ tailWord_2040547).sum := by decide
  have hdescent : baseEnd_2040547 < baseStart_2040547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040665 : List Nat := [1, 2, 1, 2, 2, 4, 2, 3, 2, 3]
def baseStart_2040665 : Nat := 118140960795 + 2040665 * 2 ^ 59
def prefixEnd_2040665 : Nat := 4983230072969 + 3 ^ 40 * 2040665 * 2
def baseEnd_2040665 : Nat := 698561333204909081668439

theorem tailTrace_2040665 : CollatzResearch.WordTrace tailWord_2040665 prefixEnd_2040665 698561333204909081668439 := by
  unfold tailWord_2040665
  simp only [CollatzResearch.WordTrace]
  refine ⟨74429167152026697680187449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49619444768017798453458299 74429167152026697680187449)
  ·
    refine ⟨55821875364020023260140587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74429167152026697680187449 55821875364020023260140587)
    ·
      refine ⟨83732813046030034890210881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55821875364020023260140587 83732813046030034890210881)
      ·
        refine ⟨62799609784522526167658161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83732813046030034890210881 62799609784522526167658161)
        ·
          refine ⟨47099707338391894625743621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62799609784522526167658161 47099707338391894625743621)
          ·
            refine ⟨8831195125948480242326929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47099707338391894625743621 8831195125948480242326929)
            ·
              refine ⟨6623396344461360181745197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8831195125948480242326929 6623396344461360181745197)
              ·
                refine ⟨2483773629173010068154449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6623396344461360181745197 2483773629173010068154449)
                ·
                  refine ⟨1862830221879757551115837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2483773629173010068154449 1862830221879757551115837)
                  ·
                    refine ⟨698561333204909081668439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1862830221879757551115837 698561333204909081668439)
                    ·
                      rfl

theorem cell22_2040665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 3].length) (baseStart_2040665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040665 prefixEnd_2040665 := by exact prefixLift 2040665
  have htrace : WordTrace (prefixWord ++ tailWord_2040665) baseStart_2040665 baseEnd_2040665 := by
    simpa [prefixWord, tailWord_2040665, baseEnd_2040665] using wordTrace_append hprefix tailTrace_2040665
  have hstable : (prefixWord ++ tailWord_2040665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040665).length < 2 ^ (prefixWord ++ tailWord_2040665).sum := by decide
  have hdescent : baseEnd_2040665 < baseStart_2040665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040680 : List Nat := [2, 1, 4, 2, 1, 2, 3, 1, 2, 4]
def baseStart_2040680 : Nat := 118140960795 + 2040680 * 2 ^ 59
def prefixEnd_2040680 : Nat := 4983230072969 + 3 ^ 40 * 2040680 * 2
def baseEnd_2040680 : Nat := 698566468011454042543393

theorem tailTrace_2040680 : CollatzResearch.WordTrace tailWord_2040680 prefixEnd_2040680 698566468011454042543393 := by
  unfold tailWord_2040680
  simp only [CollatzResearch.WordTrace]
  refine ⟨37214857123486177620991747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49619809497981570161322329 37214857123486177620991747)
  ·
    refine ⟨55822285685229266431487621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37214857123486177620991747 55822285685229266431487621)
    ·
      refine ⟨10466678565980487455903929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55822285685229266431487621 10466678565980487455903929)
      ·
        refine ⟨7850008924485365591927947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10466678565980487455903929 7850008924485365591927947)
        ·
          refine ⟨11775013386728048387891921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7850008924485365591927947 11775013386728048387891921)
          ·
            refine ⟨8831260040046036290918941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11775013386728048387891921 8831260040046036290918941)
            ·
              refine ⟨3311722515017263609094603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8831260040046036290918941 3311722515017263609094603)
              ·
                refine ⟨4967583772525895413641905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3311722515017263609094603 4967583772525895413641905)
                ·
                  refine ⟨3725687829394421560231429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4967583772525895413641905 3725687829394421560231429)
                  ·
                    refine ⟨698566468011454042543393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3725687829394421560231429 698566468011454042543393)
                    ·
                      rfl

theorem cell22_2040680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_2040680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040680 prefixEnd_2040680 := by exact prefixLift 2040680
  have htrace : WordTrace (prefixWord ++ tailWord_2040680) baseStart_2040680 baseEnd_2040680 := by
    simpa [prefixWord, tailWord_2040680, baseEnd_2040680] using wordTrace_append hprefix tailTrace_2040680
  have hstable : (prefixWord ++ tailWord_2040680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040680).length < 2 ^ (prefixWord ++ tailWord_2040680).sum := by decide
  have hdescent : baseEnd_2040680 < baseStart_2040680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040686 : List Nat := [4, 1, 2, 3, 3, 1, 2, 1, 1, 4]
def baseStart_2040686 : Nat := 118140960795 + 2040686 * 2 ^ 59
def prefixEnd_2040686 : Nat := 4983230072969 + 3 ^ 40 * 2040686 * 2
def baseEnd_2040686 : Nat := 698568521934072026893375

theorem tailTrace_2040686 : CollatzResearch.WordTrace tailWord_2040686 prefixEnd_2040686 698568521934072026893375 := by
  unfold tailWord_2040686
  simp only [CollatzResearch.WordTrace]
  refine ⟨9303741635618827283337739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49619955389967078844467941 9303741635618827283337739)
  ·
    refine ⟨13955612453428240925006609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9303741635618827283337739 13955612453428240925006609)
    ·
      refine ⟨10466709340071180693754957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13955612453428240925006609 10466709340071180693754957)
      ·
        refine ⟨3925016002526692760158109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10466709340071180693754957 3925016002526692760158109)
        ·
          refine ⟨1471881000947509785059291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3925016002526692760158109 1471881000947509785059291)
          ·
            refine ⟨2207821501421264677588937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1471881000947509785059291 2207821501421264677588937)
            ·
              refine ⟨1655866126065948508191703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2207821501421264677588937 1655866126065948508191703)
              ·
                refine ⟨2483799189098922762287555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655866126065948508191703 2483799189098922762287555)
                ·
                  refine ⟨3725698783648384143431333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2483799189098922762287555 3725698783648384143431333)
                  ·
                    refine ⟨698568521934072026893375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3725698783648384143431333 698568521934072026893375)
                    ·
                      rfl

theorem cell22_2040686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_2040686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040686 prefixEnd_2040686 := by exact prefixLift 2040686
  have htrace : WordTrace (prefixWord ++ tailWord_2040686) baseStart_2040686 baseEnd_2040686 := by
    simpa [prefixWord, tailWord_2040686, baseEnd_2040686] using wordTrace_append hprefix tailTrace_2040686
  have hstable : (prefixWord ++ tailWord_2040686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040686).length < 2 ^ (prefixWord ++ tailWord_2040686).sum := by decide
  have hdescent : baseEnd_2040686 < baseStart_2040686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040813 : List Nat := [1, 5, 1, 15]
def baseStart_2040813 : Nat := 118140960795 + 2040813 * 2 ^ 59
def prefixEnd_2040813 : Nat := 4983230072969 + 3 ^ 40 * 2040813 * 2
def baseEnd_2040813 : Nat := 958315496062395101465

theorem tailTrace_2040813 : CollatzResearch.WordTrace tailWord_2040813 prefixEnd_2040813 958315496062395101465 := by
  unfold tailWord_2040813
  simp only [CollatzResearch.WordTrace]
  refine ⟨74434565155490518956575093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49623043436993679304383395 74434565155490518956575093)
  ·
    refine ⟨6978240483327236152178915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74434565155490518956575093 6978240483327236152178915)
    ·
      refine ⟨10467360724990854228268373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6978240483327236152178915 10467360724990854228268373)
      ·
        refine ⟨958315496062395101465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 10467360724990854228268373 958315496062395101465)
        ·
          rfl

theorem cell22_2040813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 15].length) (baseStart_2040813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040813 prefixEnd_2040813 := by exact prefixLift 2040813
  have htrace : WordTrace (prefixWord ++ tailWord_2040813) baseStart_2040813 baseEnd_2040813 := by
    simpa [prefixWord, tailWord_2040813, baseEnd_2040813] using wordTrace_append hprefix tailTrace_2040813
  have hstable : (prefixWord ++ tailWord_2040813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040813).length < 2 ^ (prefixWord ++ tailWord_2040813).sum := by decide
  have hdescent : baseEnd_2040813 < baseStart_2040813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040815 : List Nat := [1, 1, 2, 1, 4, 3, 2, 2, 2, 4]
def baseStart_2040815 : Nat := 118140960795 + 2040815 * 2 ^ 59
def prefixEnd_2040815 : Nat := 4983230072969 + 3 ^ 40 * 2040815 * 2
def baseEnd_2040815 : Nat := 698612681270358690417979

theorem tailTrace_2040815 : CollatzResearch.WordTrace tailWord_2040815 prefixEnd_2040815 698612681270358690417979 := by
  unfold tailWord_2040815
  simp only [CollatzResearch.WordTrace]
  refine ⟨74434638101483273298147899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49623092067655515532098599 74434638101483273298147899)
  ·
    refine ⟨111651957152224909947221849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74434638101483273298147899 111651957152224909947221849)
    ·
      refine ⟨83738967864168682460416387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111651957152224909947221849 83738967864168682460416387)
      ·
        refine ⟨125608451796253023690624581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83738967864168682460416387 125608451796253023690624581)
        ·
          refine ⟨23551584711797441941992109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125608451796253023690624581 23551584711797441941992109)
          ·
            refine ⟨8831844266924040728247041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23551584711797441941992109 8831844266924040728247041)
            ·
              refine ⟨6623883200193030546185281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8831844266924040728247041 6623883200193030546185281)
              ·
                refine ⟨4967912400144772909638961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6623883200193030546185281 4967912400144772909638961)
                ·
                  refine ⟨3725934300108579682229221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4967912400144772909638961 3725934300108579682229221)
                  ·
                    refine ⟨698612681270358690417979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3725934300108579682229221 698612681270358690417979)
                    ·
                      rfl

theorem cell22_2040815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_2040815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040815 prefixEnd_2040815 := by exact prefixLift 2040815
  have htrace : WordTrace (prefixWord ++ tailWord_2040815) baseStart_2040815 baseEnd_2040815 := by
    simpa [prefixWord, tailWord_2040815, baseEnd_2040815] using wordTrace_append hprefix tailTrace_2040815
  have hstable : (prefixWord ++ tailWord_2040815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040815).length < 2 ^ (prefixWord ++ tailWord_2040815).sum := by decide
  have hdescent : baseEnd_2040815 < baseStart_2040815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040817 : List Nat := [1, 2, 2, 2, 4, 1, 1, 4, 2, 3]
def baseStart_2040817 : Nat := 118140960795 + 2040817 * 2 ^ 59
def prefixEnd_2040817 : Nat := 4983230072969 + 3 ^ 40 * 2040817 * 2
def baseEnd_2040817 : Nat := 698613365911231351867973

theorem tailTrace_2040817 : CollatzResearch.WordTrace tailWord_2040817 prefixEnd_2040817 698613365911231351867973 := by
  unfold tailWord_2040817
  simp only [CollatzResearch.WordTrace]
  refine ⟨74434711047476027639720705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49623140698317351759813803 74434711047476027639720705)
  ·
    refine ⟨55826033285607020729790529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74434711047476027639720705 55826033285607020729790529)
    ·
      refine ⟨41869524964205265547342897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55826033285607020729790529 41869524964205265547342897)
      ·
        refine ⟨31402143723153949160507173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41869524964205265547342897 31402143723153949160507173)
        ·
          refine ⟨5887901948091365467595095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31402143723153949160507173 5887901948091365467595095)
          ·
            refine ⟨8831852922137048201392643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5887901948091365467595095 8831852922137048201392643)
            ·
              refine ⟨13247779383205572302088965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8831852922137048201392643 13247779383205572302088965)
              ·
                refine ⟨2483958634351044806641681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13247779383205572302088965 2483958634351044806641681)
                ·
                  refine ⟨1862968975763283604981261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2483958634351044806641681 1862968975763283604981261)
                  ·
                    refine ⟨698613365911231351867973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1862968975763283604981261 698613365911231351867973)
                    ·
                      rfl

theorem cell22_2040817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_2040817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040817 prefixEnd_2040817 := by exact prefixLift 2040817
  have htrace : WordTrace (prefixWord ++ tailWord_2040817) baseStart_2040817 baseEnd_2040817 := by
    simpa [prefixWord, tailWord_2040817, baseEnd_2040817] using wordTrace_append hprefix tailTrace_2040817
  have hstable : (prefixWord ++ tailWord_2040817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040817).length < 2 ^ (prefixWord ++ tailWord_2040817).sum := by decide
  have hdescent : baseEnd_2040817 < baseStart_2040817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040873 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 2, 11]
def baseStart_2040873 : Nat := 118140960795 + 2040873 * 2 ^ 59
def prefixEnd_2040873 : Nat := 4983230072969 + 3 ^ 40 * 2040873 * 2
def baseEnd_2040873 : Nat := 698632535855665872467801

theorem tailTrace_2040873 : CollatzResearch.WordTrace tailWord_2040873 prefixEnd_2040873 698632535855665872467801 := by
  unfold tailWord_2040873
  simp only [CollatzResearch.WordTrace]
  refine ⟨74436753535273149203759273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49624502356848766135839515 74436753535273149203759273)
  ·
    refine ⟨55827565151454861902819455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74436753535273149203759273 55827565151454861902819455)
    ·
      refine ⟨83741347727182292854229183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55827565151454861902819455 83741347727182292854229183)
      ·
        refine ⟨125612021590773439281343775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83741347727182292854229183 125612021590773439281343775)
        ·
          refine ⟨188418032386160158922015663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125612021590773439281343775 188418032386160158922015663)
          ·
            refine ⟨282627048579240238383023495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188418032386160158922015663 282627048579240238383023495)
            ·
              refine ⟨423940572868860357574535243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282627048579240238383023495 423940572868860357574535243)
              ·
                refine ⟨635910859303290536361802865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423940572868860357574535243 635910859303290536361802865)
                ·
                  refine ⟨476933144477467902271352149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 635910859303290536361802865 476933144477467902271352149)
                  ·
                    refine ⟨698632535855665872467801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 476933144477467902271352149 698632535855665872467801)
                    ·
                      rfl

theorem cell22_2040873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_2040873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040873 prefixEnd_2040873 := by exact prefixLift 2040873
  have htrace : WordTrace (prefixWord ++ tailWord_2040873) baseStart_2040873 baseEnd_2040873 := by
    simpa [prefixWord, tailWord_2040873, baseEnd_2040873] using wordTrace_append hprefix tailTrace_2040873
  have hstable : (prefixWord ++ tailWord_2040873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040873).length < 2 ^ (prefixWord ++ tailWord_2040873).sum := by decide
  have hdescent : baseEnd_2040873 < baseStart_2040873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040890 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 2, 5]
def baseStart_2040890 : Nat := 118140960795 + 2040890 * 2 ^ 59
def prefixEnd_2040890 : Nat := 4983230072969 + 3 ^ 40 * 2040890 * 2
def baseEnd_2040890 : Nat := 698638355303083494792749

theorem tailTrace_2040890 : CollatzResearch.WordTrace tailWord_2040890 prefixEnd_2040890 698638355303083494792749 := by
  unfold tailWord_2040890
  simp only [CollatzResearch.WordTrace]
  refine ⟨18609343394052890276782031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49624915717474374071418749 18609343394052890276782031)
  ·
    refine ⟨27914015091079335415173047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18609343394052890276782031 27914015091079335415173047)
    ·
      refine ⟨41871022636619003122759571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27914015091079335415173047 41871022636619003122759571)
      ·
        refine ⟨62806533954928504684139357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41871022636619003122759571 62806533954928504684139357)
        ·
          refine ⟨23552450233098189256552259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62806533954928504684139357 23552450233098189256552259)
          ·
            refine ⟨35328675349647283884828389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23552450233098189256552259 35328675349647283884828389)
            ·
              refine ⟨6624126628058865728405323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35328675349647283884828389 6624126628058865728405323)
              ·
                refine ⟨9936189942088298592607985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6624126628058865728405323 9936189942088298592607985)
                ·
                  refine ⟨7452142456566223944455989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9936189942088298592607985 7452142456566223944455989)
                  ·
                    refine ⟨698638355303083494792749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7452142456566223944455989 698638355303083494792749)
                    ·
                      rfl

theorem cell22_2040890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_2040890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040890 prefixEnd_2040890 := by exact prefixLift 2040890
  have htrace : WordTrace (prefixWord ++ tailWord_2040890) baseStart_2040890 baseEnd_2040890 := by
    simpa [prefixWord, tailWord_2040890, baseEnd_2040890] using wordTrace_append hprefix tailTrace_2040890
  have hstable : (prefixWord ++ tailWord_2040890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040890).length < 2 ^ (prefixWord ++ tailWord_2040890).sum := by decide
  have hdescent : baseEnd_2040890 < baseStart_2040890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040937 : List Nat := [1, 2, 1, 1, 1, 8, 1, 1, 6]
def baseStart_2040937 : Nat := 118140960795 + 2040937 * 2 ^ 59
def prefixEnd_2040937 : Nat := 4983230072969 + 3 ^ 40 * 2040937 * 2
def baseEnd_2040937 : Nat := 232884814787863679622535

theorem tailTrace_2040937 : CollatzResearch.WordTrace tailWord_2040937 prefixEnd_2040937 232884814787863679622535 := by
  unfold tailWord_2040937
  simp only [CollatzResearch.WordTrace]
  refine ⟨74439087807041288134089065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49626058538027525422726043 74439087807041288134089065)
  ·
    refine ⟨55829315855280966100566799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74439087807041288134089065 55829315855280966100566799)
    ·
      refine ⟨83743973782921449150850199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55829315855280966100566799 83743973782921449150850199)
      ·
        refine ⟨125615960674382173726275299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83743973782921449150850199 125615960674382173726275299)
        ·
          refine ⟨188423941011573260589412949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125615960674382173726275299 188423941011573260589412949)
          ·
            refine ⟨2208093058729374147532183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 188423941011573260589412949 2208093058729374147532183)
            ·
              refine ⟨3312139588094061221298275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2208093058729374147532183 3312139588094061221298275)
              ·
                refine ⟨4968209382141091831947413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3312139588094061221298275 4968209382141091831947413)
                ·
                  refine ⟨232884814787863679622535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4968209382141091831947413 232884814787863679622535)
                  ·
                    rfl

theorem cell22_2040937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 6].length) (baseStart_2040937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040937 prefixEnd_2040937 := by exact prefixLift 2040937
  have htrace : WordTrace (prefixWord ++ tailWord_2040937) baseStart_2040937 baseEnd_2040937 := by
    simpa [prefixWord, tailWord_2040937, baseEnd_2040937] using wordTrace_append hprefix tailTrace_2040937
  have hstable : (prefixWord ++ tailWord_2040937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040937).length < 2 ^ (prefixWord ++ tailWord_2040937).sum := by decide
  have hdescent : baseEnd_2040937 < baseStart_2040937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040986 : List Nat := [3, 1, 1, 5, 1, 2, 2, 2, 2, 3]
def baseStart_2040986 : Nat := 118140960795 + 2040986 * 2 ^ 59
def prefixEnd_2040986 : Nat := 4983230072969 + 3 ^ 40 * 2040986 * 2
def baseEnd_2040986 : Nat := 698671218064971244392455

theorem tailTrace_2040986 : CollatzResearch.WordTrace tailWord_2040986 prefixEnd_2040986 698671218064971244392455 := by
  unfold tailWord_2040986
  simp only [CollatzResearch.WordTrace]
  refine ⟨18610218745965942375655703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49627249989242513001748541 18610218745965942375655703)
  ·
    refine ⟨27915328118948913563483555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18610218745965942375655703 27915328118948913563483555)
    ·
      refine ⟨41872992178423370345225333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27915328118948913563483555 41872992178423370345225333)
      ·
        refine ⟨3925593016727190969864875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41872992178423370345225333 3925593016727190969864875)
        ·
          refine ⟨5888389525090786454797313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3925593016727190969864875 5888389525090786454797313)
          ·
            refine ⟨4416292143818089841097985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5888389525090786454797313 4416292143818089841097985)
            ·
              refine ⟨3312219107863567380823489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4416292143818089841097985 3312219107863567380823489)
              ·
                refine ⟨2484164330897675535617617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3312219107863567380823489 2484164330897675535617617)
                ·
                  refine ⟨1863123248173256651713213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2484164330897675535617617 1863123248173256651713213)
                  ·
                    refine ⟨698671218064971244392455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1863123248173256651713213 698671218064971244392455)
                    ·
                      rfl

theorem cell22_2040986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_2040986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040986 prefixEnd_2040986 := by exact prefixLift 2040986
  have htrace : WordTrace (prefixWord ++ tailWord_2040986) baseStart_2040986 baseEnd_2040986 := by
    simpa [prefixWord, tailWord_2040986, baseEnd_2040986] using wordTrace_append hprefix tailTrace_2040986
  have hstable : (prefixWord ++ tailWord_2040986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040986).length < 2 ^ (prefixWord ++ tailWord_2040986).sum := by decide
  have hdescent : baseEnd_2040986 < baseStart_2040986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040999 : List Nat := [1, 1, 6, 2, 1, 3, 1, 7]
def baseStart_2040999 : Nat := 118140960795 + 2040999 * 2 ^ 59
def prefixEnd_2040999 : Nat := 4983230072969 + 3 ^ 40 * 2040999 * 2
def baseEnd_2040999 : Nat := 77630629803404838201935

theorem tailTrace_2040999 : CollatzResearch.WordTrace tailWord_2040999 prefixEnd_2040999 77630629803404838201935 := by
  unfold tailWord_2040999
  simp only [CollatzResearch.WordTrace]
  refine ⟨74441349132816672722846051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49627566088544448481897367 74441349132816672722846051)
  ·
    refine ⟨111662023699225009084269077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74441349132816672722846051 111662023699225009084269077)
    ·
      refine ⟨5234157360901172300825113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111662023699225009084269077 5234157360901172300825113)
      ·
        refine ⟨3925618020675879225618835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5234157360901172300825113 3925618020675879225618835)
        ·
          refine ⟨5888427031013818838428253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3925618020675879225618835 5888427031013818838428253)
          ·
            refine ⟨2208160136630182064410595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5888427031013818838428253 2208160136630182064410595)
            ·
              refine ⟨3312240204945273096615893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2208160136630182064410595 3312240204945273096615893)
              ·
                refine ⟨77630629803404838201935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3312240204945273096615893 77630629803404838201935)
                ·
                  rfl

theorem cell22_2040999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 7].length) (baseStart_2040999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2040999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2040999 prefixEnd_2040999 := by exact prefixLift 2040999
  have htrace : WordTrace (prefixWord ++ tailWord_2040999) baseStart_2040999 baseEnd_2040999 := by
    simpa [prefixWord, tailWord_2040999, baseEnd_2040999] using wordTrace_append hprefix tailTrace_2040999
  have hstable : (prefixWord ++ tailWord_2040999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040999).length < 2 ^ (prefixWord ++ tailWord_2040999).sum := by decide
  have hdescent : baseEnd_2040999 < baseStart_2040999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041037 : List Nat := [1, 6, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_2041037 : Nat := 118140960795 + 2041037 * 2 ^ 59
def prefixEnd_2041037 : Nat := 4983230072969 + 3 ^ 40 * 2041037 * 2
def baseEnd_2041037 : Nat := 698688676407224111367299

theorem tailTrace_2041037 : CollatzResearch.WordTrace tailWord_2041037 prefixEnd_2041037 698688676407224111367299 := by
  unfold tailWord_2041037
  simp only [CollatzResearch.WordTrace]
  refine ⟨74442735106679005212729365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49628490071119336808486243 74442735106679005212729365)
  ·
    refine ⟨3489503208125578369346689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74442735106679005212729365 3489503208125578369346689)
    ·
      refine ⟨2617127406094183777010017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3489503208125578369346689 2617127406094183777010017)
      ·
        refine ⟨1962845554570637832757513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2617127406094183777010017 1962845554570637832757513)
        ·
          refine ⟨1472134165927978374568135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1962845554570637832757513 1472134165927978374568135)
          ·
            refine ⟨2208201248891967561852203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1472134165927978374568135 2208201248891967561852203)
            ·
              refine ⟨3312301873337951342778305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2208201248891967561852203 3312301873337951342778305)
              ·
                refine ⟨2484226405003463507083729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3312301873337951342778305 2484226405003463507083729)
                ·
                  refine ⟨1863169803752597630312797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2484226405003463507083729 1863169803752597630312797)
                  ·
                    refine ⟨698688676407224111367299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1863169803752597630312797 698688676407224111367299)
                    ·
                      rfl

theorem cell22_2041037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_2041037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041037 prefixEnd_2041037 := by exact prefixLift 2041037
  have htrace : WordTrace (prefixWord ++ tailWord_2041037) baseStart_2041037 baseEnd_2041037 := by
    simpa [prefixWord, tailWord_2041037, baseEnd_2041037] using wordTrace_append hprefix tailTrace_2041037
  have hstable : (prefixWord ++ tailWord_2041037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041037).length < 2 ^ (prefixWord ++ tailWord_2041037).sum := by decide
  have hdescent : baseEnd_2041037 < baseStart_2041037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041042 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_2041042 : Nat := 118140960795 + 2041042 * 2 ^ 59
def prefixEnd_2041042 : Nat := 4983230072969 + 3 ^ 40 * 2041042 * 2
def baseEnd_2041042 : Nat := 698690388009405764992283

theorem tailTrace_2041042 : CollatzResearch.WordTrace tailWord_2041042 prefixEnd_2041042 698690388009405764992283 := by
  unfold tailWord_2041042
  simp only [CollatzResearch.WordTrace]
  refine ⟨18610729367915222766665345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49628611647773927377774253 18610729367915222766665345)
  ·
    refine ⟨13958047025936417074999009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18610729367915222766665345 13958047025936417074999009)
    ·
      refine ⟨10468535269452312806249257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13958047025936417074999009 10468535269452312806249257)
      ·
        refine ⟨7851401452089234604686943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10468535269452312806249257 7851401452089234604686943)
        ·
          refine ⟨11777102178133851907030415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7851401452089234604686943 11777102178133851907030415)
          ·
            refine ⟨17665653267200777860545623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11777102178133851907030415 17665653267200777860545623)
            ·
              refine ⟨26498479900801166790818435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17665653267200777860545623 26498479900801166790818435)
              ·
                refine ⟨39747719851201750186227653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26498479900801166790818435 39747719851201750186227653)
                ·
                  refine ⟨7452697472100328159917685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39747719851201750186227653 7452697472100328159917685)
                  ·
                    refine ⟨698690388009405764992283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7452697472100328159917685 698690388009405764992283)
                    ·
                      rfl

theorem cell22_2041042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_2041042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041042 prefixEnd_2041042 := by exact prefixLift 2041042
  have htrace : WordTrace (prefixWord ++ tailWord_2041042) baseStart_2041042 baseEnd_2041042 := by
    simpa [prefixWord, tailWord_2041042, baseEnd_2041042] using wordTrace_append hprefix tailTrace_2041042
  have hstable : (prefixWord ++ tailWord_2041042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041042).length < 2 ^ (prefixWord ++ tailWord_2041042).sum := by decide
  have hdescent : baseEnd_2041042 < baseStart_2041042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041061 : List Nat := [1, 3, 1, 4, 3, 1, 3, 1, 5]
def baseStart_2041061 : Nat := 118140960795 + 2041061 * 2 ^ 59
def prefixEnd_2041061 : Nat := 4983230072969 + 3 ^ 40 * 2041061 * 2
def baseEnd_2041061 : Nat := 232898964032565349589075

theorem tailTrace_2041061 : CollatzResearch.WordTrace tailWord_2041061 prefixEnd_2041061 232898964032565349589075 := by
  unfold tailWord_2041061
  simp only [CollatzResearch.WordTrace]
  refine ⟨74443610458592057311603037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49629073639061371541068691 74443610458592057311603037)
  ·
    refine ⟨27916353921972021491851139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74443610458592057311603037 27916353921972021491851139)
    ·
      refine ⟨41874530882958032237776709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27916353921972021491851139 41874530882958032237776709)
      ·
        refine ⟨7851474540554631044583133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41874530882958032237776709 7851474540554631044583133)
        ·
          refine ⟨2944302952707986641718675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7851474540554631044583133 2944302952707986641718675)
          ·
            refine ⟨4416454429061979962578013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944302952707986641718675 4416454429061979962578013)
            ·
              refine ⟨1656170410898242485966755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4416454429061979962578013 1656170410898242485966755)
              ·
                refine ⟨2484255616347363728950133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656170410898242485966755 2484255616347363728950133)
                ·
                  refine ⟨232898964032565349589075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2484255616347363728950133 232898964032565349589075)
                  ·
                    rfl

theorem cell22_2041061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_2041061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041061 prefixEnd_2041061 := by exact prefixLift 2041061
  have htrace : WordTrace (prefixWord ++ tailWord_2041061) baseStart_2041061 baseEnd_2041061 := by
    simpa [prefixWord, tailWord_2041061, baseEnd_2041061] using wordTrace_append hprefix tailTrace_2041061
  have hstable : (prefixWord ++ tailWord_2041061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041061).length < 2 ^ (prefixWord ++ tailWord_2041061).sum := by decide
  have hdescent : baseEnd_2041061 < baseStart_2041061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041162 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 7]
def baseStart_2041162 : Nat := 118140960795 + 2041162 * 2 ^ 59
def prefixEnd_2041162 : Nat := 4983230072969 + 3 ^ 40 * 2041162 * 2
def baseEnd_2041162 : Nat := 232910488820588483997305

theorem tailTrace_2041162 : CollatzResearch.WordTrace tailWord_2041162 prefixEnd_2041162 232910488820588483997305 := by
  unfold tailWord_2041162
  simp only [CollatzResearch.WordTrace]
  refine ⟨18611823557806537890257435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49631529487484101040686493 18611823557806537890257435)
  ·
    refine ⟨27917735336709806835386153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18611823557806537890257435 27917735336709806835386153)
    ·
      refine ⟨20938301502532355126539615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27917735336709806835386153 20938301502532355126539615)
      ·
        refine ⟨31407452253798532689809423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20938301502532355126539615 31407452253798532689809423)
        ·
          refine ⟨47111178380697799034714135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31407452253798532689809423 47111178380697799034714135)
          ·
            refine ⟨70666767571046698552071203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47111178380697799034714135 70666767571046698552071203)
            ·
              refine ⟨106000151356570047828106805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70666767571046698552071203 106000151356570047828106805)
              ·
                refine ⟨9937514189678441983885013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106000151356570047828106805 9937514189678441983885013)
                ·
                  refine ⟨232910488820588483997305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9937514189678441983885013 232910488820588483997305)
                  ·
                    rfl

theorem cell22_2041162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_2041162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041162 prefixEnd_2041162 := by exact prefixLift 2041162
  have htrace : WordTrace (prefixWord ++ tailWord_2041162) baseStart_2041162 baseEnd_2041162 := by
    simpa [prefixWord, tailWord_2041162, baseEnd_2041162] using wordTrace_append hprefix tailTrace_2041162
  have hstable : (prefixWord ++ tailWord_2041162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041162).length < 2 ^ (prefixWord ++ tailWord_2041162).sum := by decide
  have hdescent : baseEnd_2041162 < baseStart_2041162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041177 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 1, 7]
def baseStart_2041177 : Nat := 118140960795 + 2041177 * 2 ^ 59
def prefixEnd_2041177 : Nat := 4983230072969 + 3 ^ 40 * 2041177 * 2
def baseEnd_2041177 : Nat := 698736601268310412866869

theorem tailTrace_2041177 : CollatzResearch.WordTrace tailWord_2041177 prefixEnd_2041177 698736601268310412866869 := by
  unfold tailWord_2041177
  simp only [CollatzResearch.WordTrace]
  refine ⟨74447841326171809122825785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49631894217447872748550523 74447841326171809122825785)
  ·
    refine ⟨55835880994628856842119339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74447841326171809122825785 55835880994628856842119339)
    ·
      refine ⟨83753821491943285263179009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55835880994628856842119339 83753821491943285263179009)
      ·
        refine ⟨62815366118957463947384257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83753821491943285263179009 62815366118957463947384257)
        ·
          refine ⟨47111524589218097960538193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62815366118957463947384257 47111524589218097960538193)
          ·
            refine ⟨35333643441913573470403645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47111524589218097960538193 35333643441913573470403645)
            ·
              refine ⟨13250116290717590051401367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35333643441913573470403645 13250116290717590051401367)
              ·
                refine ⟨19875174436076385077102051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13250116290717590051401367 19875174436076385077102051)
                ·
                  refine ⟨29812761654114577615653077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19875174436076385077102051 29812761654114577615653077)
                  ·
                    refine ⟨698736601268310412866869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29812761654114577615653077 698736601268310412866869)
                    ·
                      rfl

theorem cell22_2041177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_2041177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041177 prefixEnd_2041177 := by exact prefixLift 2041177
  have htrace : WordTrace (prefixWord ++ tailWord_2041177) baseStart_2041177 baseEnd_2041177 := by
    simpa [prefixWord, tailWord_2041177, baseEnd_2041177] using wordTrace_append hprefix tailTrace_2041177
  have hstable : (prefixWord ++ tailWord_2041177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041177).length < 2 ^ (prefixWord ++ tailWord_2041177).sum := by decide
  have hdescent : baseEnd_2041177 < baseStart_2041177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041207 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 8]
def baseStart_2041207 : Nat := 118140960795 + 2041207 * 2 ^ 59
def prefixEnd_2041207 : Nat := 4983230072969 + 3 ^ 40 * 2041207 * 2
def baseEnd_2041207 : Nat := 232915623627133444872259

theorem tailTrace_2041207 : CollatzResearch.WordTrace tailWord_2041207 prefixEnd_2041207 232915623627133444872259 := by
  unfold tailWord_2041207
  simp only [CollatzResearch.WordTrace]
  refine ⟨74448935516063124246417875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49632623677375416164278583 74448935516063124246417875)
  ·
    refine ⟨111673403274094686369626813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74448935516063124246417875 111673403274094686369626813)
    ·
      refine ⟨41877526227785507388610055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111673403274094686369626813 41877526227785507388610055)
      ·
        refine ⟨62816289341678261082915083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41877526227785507388610055 62816289341678261082915083)
        ·
          refine ⟨94224434012517391624372625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62816289341678261082915083 94224434012517391624372625)
          ·
            refine ⟨70668325509388043718279469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94224434012517391624372625 70668325509388043718279469)
            ·
              refine ⟨26500622066020516394354801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70668325509388043718279469 26500622066020516394354801)
              ·
                refine ⟨19875466549515387295766101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26500622066020516394354801 19875466549515387295766101)
                ·
                  refine ⟨232915623627133444872259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19875466549515387295766101 232915623627133444872259)
                  ·
                    rfl

theorem cell22_2041207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 8].length) (baseStart_2041207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041207 prefixEnd_2041207 := by exact prefixLift 2041207
  have htrace : WordTrace (prefixWord ++ tailWord_2041207) baseStart_2041207 baseEnd_2041207 := by
    simpa [prefixWord, tailWord_2041207, baseEnd_2041207] using wordTrace_append hprefix tailTrace_2041207
  have hstable : (prefixWord ++ tailWord_2041207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041207).length < 2 ^ (prefixWord ++ tailWord_2041207).sum := by decide
  have hdescent : baseEnd_2041207 < baseStart_2041207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041224 : List Nat := [2, 1, 3, 3, 1, 2, 1, 3, 6]
def baseStart_2041224 : Nat := 118140960795 + 2041224 * 2 ^ 59
def prefixEnd_2041224 : Nat := 4983230072969 + 3 ^ 40 * 2041224 * 2
def baseEnd_2041224 : Nat := 232917563442939318980575

theorem tailTrace_2041224 : CollatzResearch.WordTrace tailWord_2041224 prefixEnd_2041224 232917563442939318980575 := by
  unfold tailWord_2041224
  simp only [CollatzResearch.WordTrace]
  refine ⟨37224777778500768074893363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49633037038001024099857817 37224777778500768074893363)
  ·
    refine ⟨55837166667751152112340045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37224777778500768074893363 55837166667751152112340045)
    ·
      refine ⟨20938937500406682042127517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55837166667751152112340045 20938937500406682042127517)
      ·
        refine ⟨7852101562652505765797819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20938937500406682042127517 7852101562652505765797819)
        ·
          refine ⟨11778152343978758648696729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7852101562652505765797819 11778152343978758648696729)
          ·
            refine ⟨8833614257984068986522547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11778152343978758648696729 8833614257984068986522547)
            ·
              refine ⟨13250421386976103479783821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8833614257984068986522547 13250421386976103479783821)
              ·
                refine ⟨4968908020116038804918933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13250421386976103479783821 4968908020116038804918933)
                ·
                  refine ⟨232917563442939318980575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4968908020116038804918933 232917563442939318980575)
                  ·
                    rfl

theorem cell22_2041224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 6].length) (baseStart_2041224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041224 prefixEnd_2041224 := by exact prefixLift 2041224
  have htrace : WordTrace (prefixWord ++ tailWord_2041224) baseStart_2041224 baseEnd_2041224 := by
    simpa [prefixWord, tailWord_2041224, baseEnd_2041224] using wordTrace_append hprefix tailTrace_2041224
  have hstable : (prefixWord ++ tailWord_2041224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041224).length < 2 ^ (prefixWord ++ tailWord_2041224).sum := by decide
  have hdescent : baseEnd_2041224 < baseStart_2041224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041269 : List Nat := [1, 3, 3, 2, 2, 1, 10]
def baseStart_2041269 : Nat := 118140960795 + 2041269 * 2 ^ 59
def prefixEnd_2041269 : Nat := 4983230072969 + 3 ^ 40 * 2041269 * 2
def baseEnd_2041269 : Nat := 25880299805498253317281

theorem tailTrace_2041269 : CollatzResearch.WordTrace tailWord_2041269 prefixEnd_2041269 25880299805498253317281 := by
  unfold tailWord_2041269
  simp only [CollatzResearch.WordTrace]
  refine ⟨74451196841838508835174861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49634131227892339223449907 74451196841838508835174861)
  ·
    refine ⟨27919198815689440813190573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74451196841838508835174861 27919198815689440813190573)
    ·
      refine ⟨10469699555883540304946465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27919198815689440813190573 10469699555883540304946465)
      ·
        refine ⟨7852274666912655228709849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10469699555883540304946465 7852274666912655228709849)
        ·
          refine ⟨5889206000184491421532387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7852274666912655228709849 5889206000184491421532387)
          ·
            refine ⟨8833809000276737132298581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5889206000184491421532387 8833809000276737132298581)
            ·
              refine ⟨25880299805498253317281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8833809000276737132298581 25880299805498253317281)
              ·
                rfl

theorem cell22_2041269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 10].length) (baseStart_2041269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041269 prefixEnd_2041269 := by exact prefixLift 2041269
  have htrace : WordTrace (prefixWord ++ tailWord_2041269) baseStart_2041269 baseEnd_2041269 := by
    simpa [prefixWord, tailWord_2041269, baseEnd_2041269] using wordTrace_append hprefix tailTrace_2041269
  have hstable : (prefixWord ++ tailWord_2041269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041269).length < 2 ^ (prefixWord ++ tailWord_2041269).sum := by decide
  have hdescent : baseEnd_2041269 < baseStart_2041269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041290 : List Nat := [3, 1, 2, 1, 2, 5, 2, 1, 2, 3]
def baseStart_2041290 : Nat := 118140960795 + 2041290 * 2 ^ 59
def prefixEnd_2041290 : Nat := 4983230072969 + 3 ^ 40 * 2041290 * 2
def baseEnd_2041290 : Nat := 698775283477615784791523

theorem tailTrace_2041290 : CollatzResearch.WordTrace tailWord_2041290 prefixEnd_2041290 698775283477615784791523 := by
  unfold tailWord_2041290
  simp only [CollatzResearch.WordTrace]
  refine ⟨18612990693690607355422331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49634641849841619614459549 18612990693690607355422331)
  ·
    refine ⟨27919486040535911033133497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18612990693690607355422331 27919486040535911033133497)
    ·
      refine ⟨20939614530401933274850123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27919486040535911033133497 20939614530401933274850123)
      ·
        refine ⟨31409421795602899912275185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20939614530401933274850123 31409421795602899912275185)
        ·
          refine ⟨23557066346702174934206389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31409421795602899912275185 23557066346702174934206389)
          ·
            refine ⟨2208474970003328900081849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23557066346702174934206389 2208474970003328900081849)
            ·
              refine ⟨1656356227502496675061387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2208474970003328900081849 1656356227502496675061387)
              ·
                refine ⟨2484534341253745012592081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656356227502496675061387 2484534341253745012592081)
                ·
                  refine ⟨1863400755940308759444061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2484534341253745012592081 1863400755940308759444061)
                  ·
                    refine ⟨698775283477615784791523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1863400755940308759444061 698775283477615784791523)
                    ·
                      rfl

theorem cell22_2041290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_2041290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041290 prefixEnd_2041290 := by exact prefixLift 2041290
  have htrace : WordTrace (prefixWord ++ tailWord_2041290) baseStart_2041290 baseEnd_2041290 := by
    simpa [prefixWord, tailWord_2041290, baseEnd_2041290] using wordTrace_append hprefix tailTrace_2041290
  have hstable : (prefixWord ++ tailWord_2041290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041290).length < 2 ^ (prefixWord ++ tailWord_2041290).sum := by decide
  have hdescent : baseEnd_2041290 < baseStart_2041290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041301 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 5, 3]
def baseStart_2041301 : Nat := 118140960795 + 2041301 * 2 ^ 59
def prefixEnd_2041301 : Nat := 4983230072969 + 3 ^ 40 * 2041301 * 2
def baseEnd_2041301 : Nat := 698779049002415422766489

theorem tailTrace_2041301 : CollatzResearch.WordTrace tailWord_2041301 prefixEnd_2041301 698779049002415422766489 := by
  unfold tailWord_2041301
  simp only [CollatzResearch.WordTrace]
  refine ⟨74452363977722578300339757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49634909318481718866893171 74452363977722578300339757)
  ·
    refine ⟨27919636491645966862627409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74452363977722578300339757 27919636491645966862627409)
    ·
      refine ⟨20939727368734475146970557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27919636491645966862627409 20939727368734475146970557)
      ·
        refine ⟨7852397763275428180113959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20939727368734475146970557 7852397763275428180113959)
        ·
          refine ⟨11778596644913142270170939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7852397763275428180113959 11778596644913142270170939)
          ·
            refine ⟨17667894967369713405256409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11778596644913142270170939 17667894967369713405256409)
            ·
              refine ⟨13250921225527285053942307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17667894967369713405256409 13250921225527285053942307)
              ·
                refine ⟨19876381838290927580913461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13250921225527285053942307 19876381838290927580913461)
                ·
                  refine ⟨1863410797339774460710637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19876381838290927580913461 1863410797339774460710637)
                  ·
                    refine ⟨698779049002415422766489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1863410797339774460710637 698779049002415422766489)
                    ·
                      rfl

theorem cell22_2041301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_2041301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041301 prefixEnd_2041301 := by exact prefixLift 2041301
  have htrace : WordTrace (prefixWord ++ tailWord_2041301) baseStart_2041301 baseEnd_2041301 := by
    simpa [prefixWord, tailWord_2041301, baseEnd_2041301] using wordTrace_append hprefix tailTrace_2041301
  have hstable : (prefixWord ++ tailWord_2041301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041301).length < 2 ^ (prefixWord ++ tailWord_2041301).sum := by decide
  have hdescent : baseEnd_2041301 < baseStart_2041301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041361 : List Nat := [1, 2, 2, 1, 1, 2, 4, 4, 1, 4]
def baseStart_2041361 : Nat := 118140960795 + 2041361 * 2 ^ 59
def prefixEnd_2041361 : Nat := 4983230072969 + 3 ^ 40 * 2041361 * 2
def baseEnd_2041361 : Nat := 698799588228595266266305

theorem tailTrace_2041361 : CollatzResearch.WordTrace tailWord_2041361 prefixEnd_2041361 698799588228595266266305 := by
  unfold tailWord_2041361
  simp only [CollatzResearch.WordTrace]
  refine ⟨74454552357505208547523937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49636368238336805698349291 74454552357505208547523937)
  ·
    refine ⟨55840914268128906410642953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74454552357505208547523937 55840914268128906410642953)
    ·
      refine ⟨41880685701096679807982215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55840914268128906410642953 41880685701096679807982215)
      ·
        refine ⟨62821028551645019711973323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41880685701096679807982215 62821028551645019711973323)
        ·
          refine ⟨94231542827467529567959985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62821028551645019711973323 94231542827467529567959985)
          ·
            refine ⟨70673657120600647175969989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94231542827467529567959985 70673657120600647175969989)
            ·
              refine ⟨13251310710112621345494373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70673657120600647175969989 13251310710112621345494373)
              ·
                refine ⟨2484620758146116502280195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13251310710112621345494373 2484620758146116502280195)
                ·
                  refine ⟨3726931137219174753420293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2484620758146116502280195 3726931137219174753420293)
                  ·
                    refine ⟨698799588228595266266305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3726931137219174753420293 698799588228595266266305)
                    ·
                      rfl

theorem cell22_2041361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_2041361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041361 prefixEnd_2041361 := by exact prefixLift 2041361
  have htrace : WordTrace (prefixWord ++ tailWord_2041361) baseStart_2041361 baseEnd_2041361 := by
    simpa [prefixWord, tailWord_2041361, baseEnd_2041361] using wordTrace_append hprefix tailTrace_2041361
  have hstable : (prefixWord ++ tailWord_2041361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041361).length < 2 ^ (prefixWord ++ tailWord_2041361).sum := by decide
  have hdescent : baseEnd_2041361 < baseStart_2041361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041419 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 1, 9]
def baseStart_2041419 : Nat := 118140960795 + 2041419 * 2 ^ 59
def prefixEnd_2041419 : Nat := 4983230072969 + 3 ^ 40 * 2041419 * 2
def baseEnd_2041419 : Nat := 698819442813902448316127

theorem tailTrace_2041419 : CollatzResearch.WordTrace tailWord_2041419 prefixEnd_2041419 698819442813902448316127 := by
  unfold tailWord_2041419
  simp only [CollatzResearch.WordTrace]
  refine ⟨74456667791295084453135311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49637778527530056302090207 74456667791295084453135311)
  ·
    refine ⟨111685001686942626679702967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74456667791295084453135311 111685001686942626679702967)
    ·
      refine ⟨167527502530413940019554451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111685001686942626679702967 167527502530413940019554451)
      ·
        refine ⟨251291253795620910029331677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167527502530413940019554451 251291253795620910029331677)
        ·
          refine ⟨94234220173357841260999379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251291253795620910029331677 94234220173357841260999379)
          ·
            refine ⟨141351330260036761891499069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94234220173357841260999379 141351330260036761891499069)
            ·
              refine ⟨53006748847513785709312151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141351330260036761891499069 53006748847513785709312151)
              ·
                refine ⟨79510123271270678563968227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53006748847513785709312151 79510123271270678563968227)
                ·
                  refine ⟨119265184906906017845952341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79510123271270678563968227 119265184906906017845952341)
                  ·
                    refine ⟨698819442813902448316127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 119265184906906017845952341 698819442813902448316127)
                    ·
                      rfl

theorem cell22_2041419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 9].length) (baseStart_2041419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041419 prefixEnd_2041419 := by exact prefixLift 2041419
  have htrace : WordTrace (prefixWord ++ tailWord_2041419) baseStart_2041419 baseEnd_2041419 := by
    simpa [prefixWord, tailWord_2041419, baseEnd_2041419] using wordTrace_append hprefix tailTrace_2041419
  have hstable : (prefixWord ++ tailWord_2041419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041419).length < 2 ^ (prefixWord ++ tailWord_2041419).sum := by decide
  have hdescent : baseEnd_2041419 < baseStart_2041419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041500 : List Nat := [2, 2, 3, 2, 3, 1, 2, 2, 5]
def baseStart_2041500 : Nat := 118140960795 + 2041500 * 2 ^ 59
def prefixEnd_2041500 : Nat := 4983230072969 + 3 ^ 40 * 2041500 * 2
def baseEnd_2041500 : Nat := 232949056923081745680293

theorem tailTrace_2041500 : CollatzResearch.WordTrace tailWord_2041500 prefixEnd_2041500 232949056923081745680293 := by
  unfold tailWord_2041500
  simp only [CollatzResearch.WordTrace]
  refine ⟨37229811052000817643416977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49639748069334423524555969 37229811052000817643416977)
  ·
    refine ⟨27922358289000613232562733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37229811052000817643416977 27922358289000613232562733)
    ·
      refine ⟨10470884358375229962211025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27922358289000613232562733 10470884358375229962211025)
      ·
        refine ⟨7853163268781422471658269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10470884358375229962211025 7853163268781422471658269)
        ·
          refine ⟨2944936225793033426871851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7853163268781422471658269 2944936225793033426871851)
          ·
            refine ⟨4417404338689550140307777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944936225793033426871851 4417404338689550140307777)
            ·
              refine ⟨3313053254017162605230833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4417404338689550140307777 3313053254017162605230833)
              ·
                refine ⟨2484789940512871953923125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3313053254017162605230833 2484789940512871953923125)
                ·
                  refine ⟨232949056923081745680293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2484789940512871953923125 232949056923081745680293)
                  ·
                    rfl

theorem cell22_2041500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_2041500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041500 prefixEnd_2041500 := by exact prefixLift 2041500
  have htrace : WordTrace (prefixWord ++ tailWord_2041500) baseStart_2041500 baseEnd_2041500 := by
    simpa [prefixWord, tailWord_2041500, baseEnd_2041500] using wordTrace_append hprefix tailTrace_2041500
  have hstable : (prefixWord ++ tailWord_2041500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041500).length < 2 ^ (prefixWord ++ tailWord_2041500).sum := by decide
  have hdescent : baseEnd_2041500 < baseStart_2041500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041504 : List Nat := [2, 1, 1, 4, 3, 3, 2, 2, 1, 3]
def baseStart_2041504 : Nat := 118140960795 + 2041504 * 2 ^ 59
def prefixEnd_2041504 : Nat := 4983230072969 + 3 ^ 40 * 2041504 * 2
def baseEnd_2041504 : Nat := 698848540050990559940867

theorem tailTrace_2041504 : CollatzResearch.WordTrace tailWord_2041504 prefixEnd_2041504 698848540050990559940867 := by
  unfold tailWord_2041504
  simp only [CollatzResearch.WordTrace]
  refine ⟨37229883997993571984989783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49639845330658095979986377 37229883997993571984989783)
  ·
    refine ⟨55844825996990357977484675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37229883997993571984989783 55844825996990357977484675)
    ·
      refine ⟨83767238995485536966227013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55844825996990357977484675 83767238995485536966227013)
      ·
        refine ⟨15706357311653538181167565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83767238995485536966227013 15706357311653538181167565)
        ·
          refine ⟨5889883991870076817937837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15706357311653538181167565 5889883991870076817937837)
          ·
            refine ⟨2208706496951278806726689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5889883991870076817937837 2208706496951278806726689)
            ·
              refine ⟨1656529872713459105045017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2208706496951278806726689 1656529872713459105045017)
              ·
                refine ⟨1242397404535094328783763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1656529872713459105045017 1242397404535094328783763)
                ·
                  refine ⟨1863596106802641493175645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1242397404535094328783763 1863596106802641493175645)
                  ·
                    refine ⟨698848540050990559940867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1863596106802641493175645 698848540050990559940867)
                    ·
                      rfl

theorem cell22_2041504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 1, 3].length) (baseStart_2041504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041504 prefixEnd_2041504 := by exact prefixLift 2041504
  have htrace : WordTrace (prefixWord ++ tailWord_2041504) baseStart_2041504 baseEnd_2041504 := by
    simpa [prefixWord, tailWord_2041504, baseEnd_2041504] using wordTrace_append hprefix tailTrace_2041504
  have hstable : (prefixWord ++ tailWord_2041504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041504).length < 2 ^ (prefixWord ++ tailWord_2041504).sum := by decide
  have hdescent : baseEnd_2041504 < baseStart_2041504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041538 : List Nat := [3, 5, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_2041538 : Nat := 118140960795 + 2041538 * 2 ^ 59
def prefixEnd_2041538 : Nat := 4983230072969 + 3 ^ 40 * 2041538 * 2
def baseEnd_2041538 : Nat := 698860178945825804590763

theorem tailTrace_2041538 : CollatzResearch.WordTrace tailWord_2041538 prefixEnd_2041538 698860178945825804590763 := by
  unfold tailWord_2041538
  simp only [CollatzResearch.WordTrace]
  refine ⟨18615252019465991944179317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49640672051909311851144845 18615252019465991944179317)
  ·
    refine ⟨1745179876824936744766811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18615252019465991944179317 1745179876824936744766811)
    ·
      refine ⟨2617769815237405117150217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1745179876824936744766811 2617769815237405117150217)
      ·
        refine ⟨1963327361428053837862663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2617769815237405117150217 1963327361428053837862663)
        ·
          refine ⟨2944991042142080756793995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1963327361428053837862663 2944991042142080756793995)
          ·
            refine ⟨4417486563213121135190993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944991042142080756793995 4417486563213121135190993)
            ·
              refine ⟨3313114922409840851393245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4417486563213121135190993 3313114922409840851393245)
              ·
                refine ⟨1242418095903690319272467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3313114922409840851393245 1242418095903690319272467)
                ·
                  refine ⟨1863627143855535478908701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1242418095903690319272467 1863627143855535478908701)
                  ·
                    refine ⟨698860178945825804590763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1863627143855535478908701 698860178945825804590763)
                    ·
                      rfl

theorem cell22_2041538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_2041538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041538 prefixEnd_2041538 := by exact prefixLift 2041538
  have htrace : WordTrace (prefixWord ++ tailWord_2041538) baseStart_2041538 baseEnd_2041538 := by
    simpa [prefixWord, tailWord_2041538, baseEnd_2041538] using wordTrace_append hprefix tailTrace_2041538
  have hstable : (prefixWord ++ tailWord_2041538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041538).length < 2 ^ (prefixWord ++ tailWord_2041538).sum := by decide
  have hdescent : baseEnd_2041538 < baseStart_2041538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041541 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 1, 6]
def baseStart_2041541 : Nat := 118140960795 + 2041541 * 2 ^ 59
def prefixEnd_2041541 : Nat := 4983230072969 + 3 ^ 40 * 2041541 * 2
def baseEnd_2041541 : Nat := 698861205907134796765753

theorem tailTrace_2041541 : CollatzResearch.WordTrace tailWord_2041541 prefixEnd_2041541 698861205907134796765753 := by
  unfold tailWord_2041541
  simp only [CollatzResearch.WordTrace]
  refine ⟨74461117496853099289076477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49640744997902066192717651 74461117496853099289076477)
  ·
    refine ⟨27922919061319912233403679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74461117496853099289076477 27922919061319912233403679)
    ·
      refine ⟨41884378591979868350105519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27922919061319912233403679 41884378591979868350105519)
      ·
        refine ⟨62826567887969802525158279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41884378591979868350105519 62826567887969802525158279)
        ·
          refine ⟨94239851831954703787737419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62826567887969802525158279 94239851831954703787737419)
          ·
            refine ⟨141359777747932055681606129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94239851831954703787737419 141359777747932055681606129)
            ·
              refine ⟨106019833310949041761204597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141359777747932055681606129 106019833310949041761204597)
              ·
                refine ⟨9939359372901472665112931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106019833310949041761204597 9939359372901472665112931)
                ·
                  refine ⟨14909039059352208997669397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9939359372901472665112931 14909039059352208997669397)
                  ·
                    refine ⟨698861205907134796765753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14909039059352208997669397 698861205907134796765753)
                    ·
                      rfl

theorem cell22_2041541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_2041541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041541 prefixEnd_2041541 := by exact prefixLift 2041541
  have htrace : WordTrace (prefixWord ++ tailWord_2041541) baseStart_2041541 baseEnd_2041541 := by
    simpa [prefixWord, tailWord_2041541, baseEnd_2041541] using wordTrace_append hprefix tailTrace_2041541
  have hstable : (prefixWord ++ tailWord_2041541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041541).length < 2 ^ (prefixWord ++ tailWord_2041541).sum := by decide
  have hdescent : baseEnd_2041541 < baseStart_2041541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041543 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 4, 3]
def baseStart_2041543 : Nat := 118140960795 + 2041543 * 2 ^ 59
def prefixEnd_2041543 : Nat := 4983230072969 + 3 ^ 40 * 2041543 * 2
def baseEnd_2041543 : Nat := 698861890548007458215747

theorem tailTrace_2041543 : CollatzResearch.WordTrace tailWord_2041543 prefixEnd_2041543 698861890548007458215747 := by
  unfold tailWord_2041543
  simp only [CollatzResearch.WordTrace]
  refine ⟨74461190442845853630649283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49640793628563902420432855 74461190442845853630649283)
  ·
    refine ⟨111691785664268780445973925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74461190442845853630649283 111691785664268780445973925)
    ·
      refine ⟨20942209812050396333620111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111691785664268780445973925 20942209812050396333620111)
      ·
        refine ⟨31413314718075594500430167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20942209812050396333620111 31413314718075594500430167)
        ·
          refine ⟨47119972077113391750645251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31413314718075594500430167 47119972077113391750645251)
          ·
            refine ⟨70679958115670087625967877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47119972077113391750645251 70679958115670087625967877)
            ·
              refine ⟨13252492146688141429868977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70679958115670087625967877 13252492146688141429868977)
              ·
                refine ⟨9939369110016106072401733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13252492146688141429868977 9939369110016106072401733)
                ·
                  refine ⟨1863631708128019888575325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9939369110016106072401733 1863631708128019888575325)
                  ·
                    refine ⟨698861890548007458215747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1863631708128019888575325 698861890548007458215747)
                    ·
                      rfl

theorem cell22_2041543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_2041543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041543 prefixEnd_2041543 := by exact prefixLift 2041543
  have htrace : WordTrace (prefixWord ++ tailWord_2041543) baseStart_2041543 baseEnd_2041543 := by
    simpa [prefixWord, tailWord_2041543, baseEnd_2041543] using wordTrace_append hprefix tailTrace_2041543
  have hstable : (prefixWord ++ tailWord_2041543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041543).length < 2 ^ (prefixWord ++ tailWord_2041543).sum := by decide
  have hdescent : baseEnd_2041543 < baseStart_2041543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041590 : List Nat := [5, 1, 1, 1, 1, 3, 4, 6]
def baseStart_2041590 : Nat := 118140960795 + 2041590 * 2 ^ 59
def prefixEnd_2041590 : Nat := 4983230072969 + 3 ^ 40 * 2041590 * 2
def baseEnd_2041590 : Nat := 77653108845390555810067

theorem tailTrace_2041590 : CollatzResearch.WordTrace tailWord_2041590 prefixEnd_2041590 77653108845390555810067 := by
  unfold tailWord_2041590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4653931542104723791100639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49641936449117053771740149 4653931542104723791100639)
  ·
    refine ⟨6980897313157085686650959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4653931542104723791100639 6980897313157085686650959)
    ·
      refine ⟨10471345969735628529976439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6980897313157085686650959 10471345969735628529976439)
      ·
        refine ⟨15707018954603442794964659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10471345969735628529976439 15707018954603442794964659)
        ·
          refine ⟨23560528431905164192446989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15707018954603442794964659 23560528431905164192446989)
          ·
            refine ⟨8835198161964436572167621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23560528431905164192446989 8835198161964436572167621)
            ·
              refine ⟨1656599655368331857281429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8835198161964436572167621 1656599655368331857281429)
              ·
                refine ⟨77653108845390555810067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1656599655368331857281429 77653108845390555810067)
                ·
                  rfl

theorem cell22_2041590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_2041590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041590 prefixEnd_2041590 := by exact prefixLift 2041590
  have htrace : WordTrace (prefixWord ++ tailWord_2041590) baseStart_2041590 baseEnd_2041590 := by
    simpa [prefixWord, tailWord_2041590, baseEnd_2041590] using wordTrace_append hprefix tailTrace_2041590
  have hstable : (prefixWord ++ tailWord_2041590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041590).length < 2 ^ (prefixWord ++ tailWord_2041590).sum := by decide
  have hdescent : baseEnd_2041590 < baseStart_2041590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
