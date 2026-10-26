import V185TrunkScan22Chunk208

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1864016 : List Nat := [2, 1, 1, 1, 1, 7, 1, 3, 2, 3]
def baseStart_1864016 : Nat := 118140960795 + 1864016 * 2 ^ 59
def prefixEnd_1864016 : Nat := 4983230072969 + 3 ^ 40 * 1864016 * 2
def baseEnd_1864016 : Nat := 638090770447522841685035

theorem tailTrace_1864016 : CollatzResearch.WordTrace tailWord_1864016 prefixEnd_1864016 638090770447522841685035 := by
  unfold tailWord_1864016
  simp only [CollatzResearch.WordTrace]
  refine ⟨33993124407497927716441951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45324165876663903621922601 33993124407497927716441951)
  ·
    refine ⟨50989686611246891574662927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33993124407497927716441951 50989686611246891574662927)
    ·
      refine ⟨76484529916870337361994391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50989686611246891574662927 76484529916870337361994391)
      ·
        refine ⟨114726794875305506042991587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76484529916870337361994391 114726794875305506042991587)
        ·
          refine ⟨172090192312958259064487381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114726794875305506042991587 172090192312958259064487381)
          ·
            refine ⟨4033363882334959196823923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 172090192312958259064487381 4033363882334959196823923)
            ·
              refine ⟨6050045823502438795235885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4033363882334959196823923 6050045823502438795235885)
              ·
                refine ⟨2268767183813414548213457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6050045823502438795235885 2268767183813414548213457)
                ·
                  refine ⟨1701575387860060911160093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2268767183813414548213457 1701575387860060911160093)
                  ·
                    refine ⟨638090770447522841685035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1701575387860060911160093 638090770447522841685035)
                    ·
                      rfl

theorem cell22_1864016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 2, 3].length) (baseStart_1864016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864016 prefixEnd_1864016 := by exact prefixLift 1864016
  have htrace : WordTrace (prefixWord ++ tailWord_1864016) baseStart_1864016 baseEnd_1864016 := by
    simpa [prefixWord, tailWord_1864016, baseEnd_1864016] using wordTrace_append hprefix tailTrace_1864016
  have hstable : (prefixWord ++ tailWord_1864016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864016).length < 2 ^ (prefixWord ++ tailWord_1864016).sum := by decide
  have hdescent : baseEnd_1864016 < baseStart_1864016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864078 : List Nat := [4, 1, 1, 4, 1, 2, 1, 2, 3, 3]
def baseStart_1864078 : Nat := 118140960795 + 1864078 * 2 ^ 59
def prefixEnd_1864078 : Nat := 4983230072969 + 3 ^ 40 * 1864078 * 2
def baseEnd_1864078 : Nat := 638111994314575346634845

theorem tailTrace_1864078 : CollatzResearch.WordTrace tailWord_1864078 prefixEnd_1864078 638111994314575346634845 := by
  unfold tailWord_1864078
  simp only [CollatzResearch.WordTrace]
  refine ⟨8498563767596405002705111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45325673427180826681093925 8498563767596405002705111)
  ·
    refine ⟨12747845651394607504057667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8498563767596405002705111 12747845651394607504057667)
    ·
      refine ⟨19121768477091911256086501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12747845651394607504057667 19121768477091911256086501)
      ·
        refine ⟨3585331589454733360516219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19121768477091911256086501 3585331589454733360516219)
        ·
          refine ⟨5377997384182100040774329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3585331589454733360516219 5377997384182100040774329)
          ·
            refine ⟨4033498038136575030580747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5377997384182100040774329 4033498038136575030580747)
            ·
              refine ⟨6050247057204862545871121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4033498038136575030580747 6050247057204862545871121)
              ·
                refine ⟨4537685292903646909403341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6050247057204862545871121 4537685292903646909403341)
                ·
                  refine ⟨1701631984838867591026253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4537685292903646909403341 1701631984838867591026253)
                  ·
                    refine ⟨638111994314575346634845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1701631984838867591026253 638111994314575346634845)
                    ·
                      rfl

theorem cell22_1864078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_1864078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864078 prefixEnd_1864078 := by exact prefixLift 1864078
  have htrace : WordTrace (prefixWord ++ tailWord_1864078) baseStart_1864078 baseEnd_1864078 := by
    simpa [prefixWord, tailWord_1864078, baseEnd_1864078] using wordTrace_append hprefix tailTrace_1864078
  have hstable : (prefixWord ++ tailWord_1864078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864078).length < 2 ^ (prefixWord ++ tailWord_1864078).sum := by decide
  have hdescent : baseEnd_1864078 < baseStart_1864078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864119 : List Nat := [1, 1, 3, 1, 3, 3, 1, 3, 6]
def baseStart_1864119 : Nat := 118140960795 + 1864119 * 2 ^ 59
def prefixEnd_1864119 : Nat := 4983230072969 + 3 ^ 40 * 1864119 * 2
def baseEnd_1864119 : Nat := 212708676484154968786573

theorem tailTrace_1864119 : CollatzResearch.WordTrace tailWord_1864119 prefixEnd_1864119 212708676484154968786573 := by
  unfold tailWord_1864119
  simp only [CollatzResearch.WordTrace]
  refine ⟨67990005533622704023883411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45326670355748469349255607 67990005533622704023883411)
  ·
    refine ⟨101985008300434056035825117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67990005533622704023883411 101985008300434056035825117)
    ·
      refine ⟨38244378112662771013434419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101985008300434056035825117 38244378112662771013434419)
      ·
        refine ⟨57366567168994156520151629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38244378112662771013434419 57366567168994156520151629)
        ·
          refine ⟨21512462688372808695056861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57366567168994156520151629 21512462688372808695056861)
          ·
            refine ⟨8067173508139803260646323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21512462688372808695056861 8067173508139803260646323)
            ·
              refine ⟨12100760262209704890969485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8067173508139803260646323 12100760262209704890969485)
              ·
                refine ⟨4537785098328639334113557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12100760262209704890969485 4537785098328639334113557)
                ·
                  refine ⟨212708676484154968786573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4537785098328639334113557 212708676484154968786573)
                  ·
                    rfl

theorem cell22_1864119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 6].length) (baseStart_1864119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864119 prefixEnd_1864119 := by exact prefixLift 1864119
  have htrace : WordTrace (prefixWord ++ tailWord_1864119) baseStart_1864119 baseEnd_1864119 := by
    simpa [prefixWord, tailWord_1864119, baseEnd_1864119] using wordTrace_append hprefix tailTrace_1864119
  have hstable : (prefixWord ++ tailWord_1864119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864119).length < 2 ^ (prefixWord ++ tailWord_1864119).sum := by decide
  have hdescent : baseEnd_1864119 < baseStart_1864119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864170 : List Nat := [3, 1, 3, 1, 3, 2, 3, 2, 4]
def baseStart_1864170 : Nat := 118140960795 + 1864170 * 2 ^ 59
def prefixEnd_1864170 : Nat := 4983230072969 + 3 ^ 40 * 1864170 * 2
def baseEnd_1864170 : Nat := 212714495931572591111521

theorem tailTrace_1864170 : CollatzResearch.WordTrace tailWord_1864170 prefixEnd_1864170 212714495931572591111521 := by
  unfold tailWord_1864170
  simp only [CollatzResearch.WordTrace]
  refine ⟨16997966414109484933497491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45327910437625293155993309 16997966414109484933497491)
  ·
    refine ⟨25496949621164227400246237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16997966414109484933497491 25496949621164227400246237)
    ·
      refine ⟨9561356107936585275092339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25496949621164227400246237 9561356107936585275092339)
      ·
        refine ⟨14342034161904877912638509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9561356107936585275092339 14342034161904877912638509)
        ·
          refine ⟨5378262810714329217239441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14342034161904877912638509 5378262810714329217239441)
          ·
            refine ⟨4033697108035746912929581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5378262810714329217239441 4033697108035746912929581)
            ·
              refine ⟨1512636415513405092348593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4033697108035746912929581 1512636415513405092348593)
              ·
                refine ⟨1134477311635053819261445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1512636415513405092348593 1134477311635053819261445)
                ·
                  refine ⟨212714495931572591111521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1134477311635053819261445 212714495931572591111521)
                  ·
                    rfl

theorem cell22_1864170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_1864170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864170 prefixEnd_1864170 := by exact prefixLift 1864170
  have htrace : WordTrace (prefixWord ++ tailWord_1864170) baseStart_1864170 baseEnd_1864170 := by
    simpa [prefixWord, tailWord_1864170, baseEnd_1864170] using wordTrace_append hprefix tailTrace_1864170
  have hstable : (prefixWord ++ tailWord_1864170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864170).length < 2 ^ (prefixWord ++ tailWord_1864170).sum := by decide
  have hdescent : baseEnd_1864170 < baseStart_1864170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864209 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 7]
def baseStart_1864209 : Nat := 118140960795 + 1864209 * 2 ^ 59
def prefixEnd_1864209 : Nat := 4983230072969 + 3 ^ 40 * 1864209 * 2
def baseEnd_1864209 : Nat := 212718946097244890536481

theorem tailTrace_1864209 : CollatzResearch.WordTrace tailWord_1864209 prefixEnd_1864209 212718946097244890536481 := by
  unfold tailWord_1864209
  simp only [CollatzResearch.WordTrace]
  refine ⟨67993288103296649394659681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45328858735531099596439787 67993288103296649394659681)
  ·
    refine ⟨50994966077472487045994761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67993288103296649394659681 50994966077472487045994761)
    ·
      refine ⟨38246224558104365284496071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50994966077472487045994761 38246224558104365284496071)
      ·
        refine ⟨57369336837156547926744107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38246224558104365284496071 57369336837156547926744107)
        ·
          refine ⟨86054005255734821890116161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57369336837156547926744107 86054005255734821890116161)
          ·
            refine ⟨64540503941801116417587121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86054005255734821890116161 64540503941801116417587121)
            ·
              refine ⟨48405377956350837313190341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64540503941801116417587121 48405377956350837313190341)
              ·
                refine ⟨9076008366815781996223189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48405377956350837313190341 9076008366815781996223189)
                ·
                  refine ⟨212718946097244890536481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9076008366815781996223189 212718946097244890536481)
                  ·
                    rfl

theorem cell22_1864209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 7].length) (baseStart_1864209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864209 prefixEnd_1864209 := by exact prefixLift 1864209
  have htrace : WordTrace (prefixWord ++ tailWord_1864209) baseStart_1864209 baseEnd_1864209 := by
    simpa [prefixWord, tailWord_1864209, baseEnd_1864209] using wordTrace_append hprefix tailTrace_1864209
  have hstable : (prefixWord ++ tailWord_1864209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864209).length < 2 ^ (prefixWord ++ tailWord_1864209).sum := by decide
  have hdescent : baseEnd_1864209 < baseStart_1864209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864256 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 3, 4]
def baseStart_1864256 : Nat := 118140960795 + 1864256 * 2 ^ 59
def prefixEnd_1864256 : Nat := 4983230072969 + 3 ^ 40 * 1864256 * 2
def baseEnd_1864256 : Nat := 638172927352242215684299

theorem tailTrace_1864256 : CollatzResearch.WordTrace tailWord_1864256 prefixEnd_1864256 638172927352242215684299 := by
  unfold tailWord_1864256
  simp only [CollatzResearch.WordTrace]
  refine ⟨33997501167063188210810311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45330001556084250947747081 33997501167063188210810311)
  ·
    refine ⟨50996251750594782316215467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33997501167063188210810311 50996251750594782316215467)
    ·
      refine ⟨76494377625892173474323201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50996251750594782316215467 76494377625892173474323201)
      ·
        refine ⟨57370783219419130105742401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76494377625892173474323201 57370783219419130105742401)
        ·
          refine ⟨43028087414564347579306801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57370783219419130105742401 43028087414564347579306801)
          ·
            refine ⟨32271065560923260684480101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43028087414564347579306801 32271065560923260684480101)
            ·
              refine ⟨6050824792673111378340019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32271065560923260684480101 6050824792673111378340019)
              ·
                refine ⟨9076237189009667067510029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6050824792673111378340019 9076237189009667067510029)
                ·
                  refine ⟨3403588945878625150316261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9076237189009667067510029 3403588945878625150316261)
                  ·
                    refine ⟨638172927352242215684299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3403588945878625150316261 638172927352242215684299)
                    ·
                      rfl

theorem cell22_1864256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_1864256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864256 prefixEnd_1864256 := by exact prefixLift 1864256
  have htrace : WordTrace (prefixWord ++ tailWord_1864256) baseStart_1864256 baseEnd_1864256 := by
    simpa [prefixWord, tailWord_1864256, baseEnd_1864256] using wordTrace_append hprefix tailTrace_1864256
  have hstable : (prefixWord ++ tailWord_1864256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864256).length < 2 ^ (prefixWord ++ tailWord_1864256).sum := by decide
  have hdescent : baseEnd_1864256 < baseStart_1864256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864273 : List Nat := [1, 2, 2, 1, 3, 4, 1, 3, 1, 4]
def baseStart_1864273 : Nat := 118140960795 + 1864273 * 2 ^ 59
def prefixEnd_1864273 : Nat := 4983230072969 + 3 ^ 40 * 1864273 * 2
def baseEnd_1864273 : Nat := 638178746799659838009247

theorem tailTrace_1864273 : CollatzResearch.WordTrace tailWord_1864273 prefixEnd_1864273 638178746799659838009247 := by
  unfold tailWord_1864273
  simp only [CollatzResearch.WordTrace]
  refine ⟨67995622375064788324989473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45330414916709858883326315 67995622375064788324989473)
  ·
    refine ⟨50996716781298591243742105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67995622375064788324989473 50996716781298591243742105)
    ·
      refine ⟨38247537585973943432806579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50996716781298591243742105 38247537585973943432806579)
      ·
        refine ⟨57371306378960915149209869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38247537585973943432806579 57371306378960915149209869)
        ·
          refine ⟨21514239892110343180953701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57371306378960915149209869 21514239892110343180953701)
          ·
            refine ⟨4033919979770689346428819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21514239892110343180953701 4033919979770689346428819)
            ·
              refine ⟨6050879969656034019643229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4033919979770689346428819 6050879969656034019643229)
              ·
                refine ⟨2269079988621012757366211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6050879969656034019643229 2269079988621012757366211)
                ·
                  refine ⟨3403619982931519136049317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2269079988621012757366211 3403619982931519136049317)
                  ·
                    refine ⟨638178746799659838009247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3403619982931519136049317 638178746799659838009247)
                    ·
                      rfl

theorem cell22_1864273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_1864273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864273 prefixEnd_1864273 := by exact prefixLift 1864273
  have htrace : WordTrace (prefixWord ++ tailWord_1864273) baseStart_1864273 baseEnd_1864273 := by
    simpa [prefixWord, tailWord_1864273, baseEnd_1864273] using wordTrace_append hprefix tailTrace_1864273
  have hstable : (prefixWord ++ tailWord_1864273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864273).length < 2 ^ (prefixWord ++ tailWord_1864273).sum := by decide
  have hdescent : baseEnd_1864273 < baseStart_1864273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864288 : List Nat := [2, 1, 1, 3, 2, 1, 4, 4, 4]
def baseStart_1864288 : Nat := 118140960795 + 1864288 * 2 ^ 59
def prefixEnd_1864288 : Nat := 4983230072969 + 3 ^ 40 * 1864288 * 2
def baseEnd_1864288 : Nat := 212727960535401599628067

theorem tailTrace_1864288 : CollatzResearch.WordTrace tailWord_1864288 prefixEnd_1864288 212727960535401599628067 := by
  unfold tailWord_1864288
  simp only [CollatzResearch.WordTrace]
  refine ⟨33998084735005222943392759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45330779646673630591190345 33998084735005222943392759)
  ·
    refine ⟨50997127102507834415089139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33998084735005222943392759 50997127102507834415089139)
    ·
      refine ⟨76495690653761751622633709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50997127102507834415089139 76495690653761751622633709)
      ·
        refine ⟨28685883995160656858487641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76495690653761751622633709 28685883995160656858487641)
        ·
          refine ⟨21514412996370492643865731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28685883995160656858487641 21514412996370492643865731)
          ·
            refine ⟨32271619494555738965798597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21514412996370492643865731 32271619494555738965798597)
            ·
              refine ⟨6050928655229201056087237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32271619494555738965798597 6050928655229201056087237)
              ·
                refine ⟨1134549122855475198016357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6050928655229201056087237 1134549122855475198016357)
                ·
                  refine ⟨212727960535401599628067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1134549122855475198016357 212727960535401599628067)
                  ·
                    rfl

theorem cell22_1864288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 4].length) (baseStart_1864288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864288 prefixEnd_1864288 := by exact prefixLift 1864288
  have htrace : WordTrace (prefixWord ++ tailWord_1864288) baseStart_1864288 baseEnd_1864288 := by
    simpa [prefixWord, tailWord_1864288, baseEnd_1864288] using wordTrace_append hprefix tailTrace_1864288
  have hstable : (prefixWord ++ tailWord_1864288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864288).length < 2 ^ (prefixWord ++ tailWord_1864288).sum := by decide
  have hdescent : baseEnd_1864288 < baseStart_1864288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864303 : List Nat := [1, 1, 2, 1, 3, 2, 2, 5, 2, 3]
def baseStart_1864303 : Nat := 118140960795 + 1864303 * 2 ^ 59
def prefixEnd_1864303 : Nat := 4983230072969 + 3 ^ 40 * 1864303 * 2
def baseEnd_1864303 : Nat := 638189016412749759759155

theorem tailTrace_1864303 : CollatzResearch.WordTrace tailWord_1864303 prefixEnd_1864303 638189016412749759759155 := by
  unfold tailWord_1864303
  simp only [CollatzResearch.WordTrace]
  refine ⟨67996716564956103448581563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45331144376637402299054375 67996716564956103448581563)
  ·
    refine ⟨101995074847434155172872345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67996716564956103448581563 101995074847434155172872345)
    ·
      refine ⟨76496306135575616379654259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101995074847434155172872345 76496306135575616379654259)
      ·
        refine ⟨114744459203363424569481389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76496306135575616379654259 114744459203363424569481389)
        ·
          refine ⟨43029172201261284213555521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114744459203363424569481389 43029172201261284213555521)
          ·
            refine ⟨32271879150945963160166641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43029172201261284213555521 32271879150945963160166641)
            ·
              refine ⟨24203909363209472370124981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32271879150945963160166641 24203909363209472370124981)
              ·
                refine ⟨2269116502800888034699217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24203909363209472370124981 2269116502800888034699217)
                ·
                  refine ⟨1701837377100666026024413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2269116502800888034699217 1701837377100666026024413)
                  ·
                    refine ⟨638189016412749759759155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1701837377100666026024413 638189016412749759759155)
                    ·
                      rfl

theorem cell22_1864303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 3].length) (baseStart_1864303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864303 prefixEnd_1864303 := by exact prefixLift 1864303
  have htrace : WordTrace (prefixWord ++ tailWord_1864303) baseStart_1864303 baseEnd_1864303 := by
    simpa [prefixWord, tailWord_1864303, baseEnd_1864303] using wordTrace_append hprefix tailTrace_1864303
  have hstable : (prefixWord ++ tailWord_1864303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864303).length < 2 ^ (prefixWord ++ tailWord_1864303).sum := by decide
  have hdescent : baseEnd_1864303 < baseStart_1864303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864376 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 6, 5]
def baseStart_1864376 : Nat := 118140960795 + 1864376 * 2 ^ 59
def prefixEnd_1864376 : Nat := 4983230072969 + 3 ^ 40 * 1864376 * 2
def baseEnd_1864376 : Nat := 638214005804601902683931

theorem tailTrace_1864376 : CollatzResearch.WordTrace tailWord_1864376 prefixEnd_1864376 638214005804601902683931 := by
  unfold tailWord_1864376
  simp only [CollatzResearch.WordTrace]
  refine ⟨33999689546845818457994491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45332919395794424610659321 33999689546845818457994491)
  ·
    refine ⟨50999534320268727686991737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33999689546845818457994491 50999534320268727686991737)
    ·
      refine ⟨38249650740201545765243803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50999534320268727686991737 38249650740201545765243803)
      ·
        refine ⟨57374476110302318647865705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38249650740201545765243803 57374476110302318647865705)
        ·
          refine ⟨43030857082726738985899279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57374476110302318647865705 43030857082726738985899279)
          ·
            refine ⟨64546285624090108478848919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43030857082726738985899279 64546285624090108478848919)
            ·
              refine ⟨96819428436135162718273379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64546285624090108478848919 96819428436135162718273379)
              ·
                refine ⟨145229142654202744077410069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96819428436135162718273379 145229142654202744077410069)
                ·
                  refine ⟨6807616061915753628628597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 145229142654202744077410069 6807616061915753628628597)
                  ·
                    refine ⟨638214005804601902683931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6807616061915753628628597 638214005804601902683931)
                    ·
                      rfl

theorem cell22_1864376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_1864376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864376 prefixEnd_1864376 := by exact prefixLift 1864376
  have htrace : WordTrace (prefixWord ++ tailWord_1864376) baseStart_1864376 baseEnd_1864376 := by
    simpa [prefixWord, tailWord_1864376, baseEnd_1864376] using wordTrace_append hprefix tailTrace_1864376
  have hstable : (prefixWord ++ tailWord_1864376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864376).length < 2 ^ (prefixWord ++ tailWord_1864376).sum := by decide
  have hdescent : baseEnd_1864376 < baseStart_1864376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864382 : List Nat := [4, 2, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_1864382 : Nat := 118140960795 + 1864382 * 2 ^ 59
def prefixEnd_1864382 : Nat := 4983230072969 + 3 ^ 40 * 1864382 * 2
def baseEnd_1864382 : Nat := 638216059727219887033913

theorem tailTrace_1864382 : CollatzResearch.WordTrace tailWord_1864382 prefixEnd_1864382 638216059727219887033913 := by
  unfold tailWord_1864382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8499949741458737492588425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45333065287779933293804933 8499949741458737492588425)
  ·
    refine ⟨6374962306094053119441319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8499949741458737492588425 6374962306094053119441319)
    ·
      refine ⟨9562443459141079679161979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6374962306094053119441319 9562443459141079679161979)
      ·
        refine ⟨14343665188711619518742969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9562443459141079679161979 14343665188711619518742969)
        ·
          refine ⟨10757748891533714639057227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14343665188711619518742969 10757748891533714639057227)
          ·
            refine ⟨16136623337300571958585841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10757748891533714639057227 16136623337300571958585841)
            ·
              refine ⟨12102467502975428968939381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16136623337300571958585841 12102467502975428968939381)
              ·
                refine ⟨1134606328403946465838067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12102467502975428968939381 1134606328403946465838067)
                ·
                  refine ⟨1701909492605919698757101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134606328403946465838067 1701909492605919698757101)
                  ·
                    refine ⟨638216059727219887033913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1701909492605919698757101 638216059727219887033913)
                    ·
                      rfl

theorem cell22_1864382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_1864382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864382 prefixEnd_1864382 := by exact prefixLift 1864382
  have htrace : WordTrace (prefixWord ++ tailWord_1864382) baseStart_1864382 baseEnd_1864382 := by
    simpa [prefixWord, tailWord_1864382, baseEnd_1864382] using wordTrace_append hprefix tailTrace_1864382
  have hstable : (prefixWord ++ tailWord_1864382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864382).length < 2 ^ (prefixWord ++ tailWord_1864382).sum := by decide
  have hdescent : baseEnd_1864382 < baseStart_1864382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864408 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 3, 4]
def baseStart_1864408 : Nat := 118140960795 + 1864408 * 2 ^ 59
def prefixEnd_1864408 : Nat := 4983230072969 + 3 ^ 40 * 1864408 * 2
def baseEnd_1864408 : Nat := 638224960058564485883833

theorem tailTrace_1864408 : CollatzResearch.WordTrace tailWord_1864408 prefixEnd_1864408 638224960058564485883833 := by
  unfold tailWord_1864408
  simp only [CollatzResearch.WordTrace]
  refine ⟨34000273114787853190576939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45333697486383804254102585 34000273114787853190576939)
  ·
    refine ⟨51000409672181779785865409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34000273114787853190576939 51000409672181779785865409)
    ·
      refine ⟨38250307254136334839399057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51000409672181779785865409 38250307254136334839399057)
      ·
        refine ⟨28687730440602251129549293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38250307254136334839399057 28687730440602251129549293)
        ·
          refine ⟨10757898915225844173580985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28687730440602251129549293 10757898915225844173580985)
          ·
            refine ⟨8068424186419383130185739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10757898915225844173580985 8068424186419383130185739)
            ·
              refine ⟨12102636279629074695278609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8068424186419383130185739 12102636279629074695278609)
              ·
                refine ⟨9076977209721806021458957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12102636279629074695278609 9076977209721806021458957)
                ·
                  refine ⟨3403866453645677258047109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9076977209721806021458957 3403866453645677258047109)
                  ·
                    refine ⟨638224960058564485883833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3403866453645677258047109 638224960058564485883833)
                    ·
                      rfl

theorem cell22_1864408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_1864408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864408 prefixEnd_1864408 := by exact prefixLift 1864408
  have htrace : WordTrace (prefixWord ++ tailWord_1864408) baseStart_1864408 baseEnd_1864408 := by
    simpa [prefixWord, tailWord_1864408, baseEnd_1864408] using wordTrace_append hprefix tailTrace_1864408
  have hstable : (prefixWord ++ tailWord_1864408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864408).length < 2 ^ (prefixWord ++ tailWord_1864408).sum := by decide
  have hdescent : baseEnd_1864408 < baseStart_1864408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864440 : List Nat := [2, 1, 2, 1, 1, 2, 6, 3, 4]
def baseStart_1864440 : Nat := 118140960795 + 1864440 * 2 ^ 59
def prefixEnd_1864440 : Nat := 4983230072969 + 3 ^ 40 * 1864440 * 2
def baseEnd_1864440 : Nat := 212745304770842356361245

theorem tailTrace_1864440 : CollatzResearch.WordTrace tailWord_1864440 prefixEnd_1864440 212745304770842356361245 := by
  unfold tailWord_1864440
  simp only [CollatzResearch.WordTrace]
  refine ⟨34000856682729887923159387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45334475576973183897545849 34000856682729887923159387)
  ·
    refine ⟨51001285024094831884739081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34000856682729887923159387 51001285024094831884739081)
    ·
      refine ⟨38250963768071123913554311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51001285024094831884739081 38250963768071123913554311)
      ·
        refine ⟨57376445652106685870331467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38250963768071123913554311 57376445652106685870331467)
        ·
          refine ⟨86064668478160028805497201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57376445652106685870331467 86064668478160028805497201)
          ·
            refine ⟨64548501358620021604122901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86064668478160028805497201 64548501358620021604122901)
            ·
              refine ⟨3025711001185313512693261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64548501358620021604122901 3025711001185313512693261)
              ·
                refine ⟨1134641625444492567259973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3025711001185313512693261 1134641625444492567259973)
                ·
                  refine ⟨212745304770842356361245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1134641625444492567259973 212745304770842356361245)
                  ·
                    rfl

theorem cell22_1864440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 4].length) (baseStart_1864440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864440 prefixEnd_1864440 := by exact prefixLift 1864440
  have htrace : WordTrace (prefixWord ++ tailWord_1864440) baseStart_1864440 baseEnd_1864440 := by
    simpa [prefixWord, tailWord_1864440, baseEnd_1864440] using wordTrace_append hprefix tailTrace_1864440
  have hstable : (prefixWord ++ tailWord_1864440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864440).length < 2 ^ (prefixWord ++ tailWord_1864440).sum := by decide
  have hdescent : baseEnd_1864440 < baseStart_1864440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864453 : List Nat := [1, 3, 1, 1, 2, 1, 1, 6, 2, 4]
def baseStart_1864453 : Nat := 118140960795 + 1864453 * 2 ^ 59
def prefixEnd_1864453 : Nat := 4983230072969 + 3 ^ 40 * 1864453 * 2
def baseEnd_1864453 : Nat := 638240364478199368508695

theorem tailTrace_1864453 : CollatzResearch.WordTrace tailWord_1864453 prefixEnd_1864453 638240364478199368508695 := by
  unfold tailWord_1864453
  simp only [CollatzResearch.WordTrace]
  refine ⟨68002187514412679066542013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45334791676275119377694675 68002187514412679066542013)
  ·
    refine ⟨25500820317904754649953255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68002187514412679066542013 25500820317904754649953255)
    ·
      refine ⟨38251230476857131974929883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25500820317904754649953255 38251230476857131974929883)
      ·
        refine ⟨57376845715285697962394825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38251230476857131974929883 57376845715285697962394825)
        ·
          refine ⟨43032634286464273471796119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57376845715285697962394825 43032634286464273471796119)
          ·
            refine ⟨64548951429696410207694179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43032634286464273471796119 64548951429696410207694179)
            ·
              refine ⟨96823427144544615311541269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64548951429696410207694179 96823427144544615311541269)
              ·
                refine ⟨4538598147400528842728497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96823427144544615311541269 4538598147400528842728497)
                ·
                  refine ⟨3403948610550396632046373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4538598147400528842728497 3403948610550396632046373)
                  ·
                    refine ⟨638240364478199368508695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3403948610550396632046373 638240364478199368508695)
                    ·
                      rfl

theorem cell22_1864453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_1864453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864453 prefixEnd_1864453 := by exact prefixLift 1864453
  have htrace : WordTrace (prefixWord ++ tailWord_1864453) baseStart_1864453 baseEnd_1864453 := by
    simpa [prefixWord, tailWord_1864453, baseEnd_1864453] using wordTrace_append hprefix tailTrace_1864453
  have hstable : (prefixWord ++ tailWord_1864453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864453).length < 2 ^ (prefixWord ++ tailWord_1864453).sum := by decide
  have hdescent : baseEnd_1864453 < baseStart_1864453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864502 : List Nat := [5, 1, 2, 2, 2, 2, 8]
def baseStart_1864502 : Nat := 118140960795 + 1864502 * 2 ^ 59
def prefixEnd_1864502 : Nat := 4983230072969 + 3 ^ 40 * 1864502 * 2
def baseEnd_1864502 : Nat := 23639153265910354593835

theorem tailTrace_1864502 : CollatzResearch.WordTrace tailWord_1864502 prefixEnd_1864502 23639153265910354593835 := by
  unfold tailWord_1864502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4250248418202197527192235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45335983127490106956717173 4250248418202197527192235)
  ·
    refine ⟨6375372627303296290788353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4250248418202197527192235 6375372627303296290788353)
    ·
      refine ⟨4781529470477472218091265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6375372627303296290788353 4781529470477472218091265)
      ·
        refine ⟨3586147102858104163568449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4781529470477472218091265 3586147102858104163568449)
        ·
          refine ⟨2689610327143578122676337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3586147102858104163568449 2689610327143578122676337)
          ·
            refine ⟨2017207745357683592007253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2689610327143578122676337 2017207745357683592007253)
            ·
              refine ⟨23639153265910354593835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2017207745357683592007253 23639153265910354593835)
              ·
                rfl

theorem cell22_1864502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 8].length) (baseStart_1864502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864502 prefixEnd_1864502 := by exact prefixLift 1864502
  have htrace : WordTrace (prefixWord ++ tailWord_1864502) baseStart_1864502 baseEnd_1864502 := by
    simpa [prefixWord, tailWord_1864502, baseEnd_1864502] using wordTrace_append hprefix tailTrace_1864502
  have hstable : (prefixWord ++ tailWord_1864502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864502).length < 2 ^ (prefixWord ++ tailWord_1864502).sum := by decide
  have hdescent : baseEnd_1864502 < baseStart_1864502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864528 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 2, 5]
def baseStart_1864528 : Nat := 118140960795 + 1864528 * 2 ^ 59
def prefixEnd_1864528 : Nat := 4983230072969 + 3 ^ 40 * 1864528 * 2
def baseEnd_1864528 : Nat := 638266038510924172883465

theorem tailTrace_1864528 : CollatzResearch.WordTrace tailWord_1864528 prefixEnd_1864528 638266038510924172883465 := by
  unfold tailWord_1864528
  simp only [CollatzResearch.WordTrace]
  refine ⟨34002461494570483437761119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45336615326093977917014825 34002461494570483437761119)
  ·
    refine ⟨51003692241855725156641679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34002461494570483437761119 51003692241855725156641679)
    ·
      refine ⟨76505538362783587734962519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51003692241855725156641679 76505538362783587734962519)
      ·
        refine ⟨114758307544175381602443779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76505538362783587734962519 114758307544175381602443779)
        ·
          refine ⟨172137461316263072403665669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114758307544175381602443779 172137461316263072403665669)
          ·
            refine ⟨32275773996799326075687313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172137461316263072403665669 32275773996799326075687313)
            ·
              refine ⟨24206830497599494556765485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32275773996799326075687313 24206830497599494556765485)
              ·
                refine ⟨9077561436599810458787057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24206830497599494556765485 9077561436599810458787057)
                ·
                  refine ⟨6808171077449857844090293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9077561436599810458787057 6808171077449857844090293)
                  ·
                    refine ⟨638266038510924172883465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6808171077449857844090293 638266038510924172883465)
                    ·
                      rfl

theorem cell22_1864528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_1864528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864528 prefixEnd_1864528 := by exact prefixLift 1864528
  have htrace : WordTrace (prefixWord ++ tailWord_1864528) baseStart_1864528 baseEnd_1864528 := by
    simpa [prefixWord, tailWord_1864528, baseEnd_1864528] using wordTrace_append hprefix tailTrace_1864528
  have hstable : (prefixWord ++ tailWord_1864528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864528).length < 2 ^ (prefixWord ++ tailWord_1864528).sum := by decide
  have hdescent : baseEnd_1864528 < baseStart_1864528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864530 : List Nat := [3, 2, 2, 1, 1, 2, 3, 3, 5]
def baseStart_1864530 : Nat := 118140960795 + 1864530 * 2 ^ 59
def prefixEnd_1864530 : Nat := 4983230072969 + 3 ^ 40 * 1864530 * 2
def baseEnd_1864530 : Nat := 212755574383932278111153

theorem tailTrace_1864530 : CollatzResearch.WordTrace tailWord_1864530 prefixEnd_1864530 212755574383932278111153 := by
  unfold tailWord_1864530
  simp only [CollatzResearch.WordTrace]
  refine ⟨17001248983783430304273761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45336663956755814144730029 17001248983783430304273761)
  ·
    refine ⟨12750936737837572728205321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17001248983783430304273761 12750936737837572728205321)
    ·
      refine ⟨9563202553378179546153991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12750936737837572728205321 9563202553378179546153991)
      ·
        refine ⟨14344803830067269319230987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9563202553378179546153991 14344803830067269319230987)
        ·
          refine ⟨21517205745100903978846481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14344803830067269319230987 21517205745100903978846481)
          ·
            refine ⟨16137904308825677984134861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21517205745100903978846481 16137904308825677984134861)
            ·
              refine ⟨6051714115809629244050573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16137904308825677984134861 6051714115809629244050573)
              ·
                refine ⟨2269392793428610966518965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6051714115809629244050573 2269392793428610966518965)
                ·
                  refine ⟨212755574383932278111153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2269392793428610966518965 212755574383932278111153)
                  ·
                    rfl

theorem cell22_1864530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_1864530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864530 prefixEnd_1864530 := by exact prefixLift 1864530
  have htrace : WordTrace (prefixWord ++ tailWord_1864530) baseStart_1864530 baseEnd_1864530 := by
    simpa [prefixWord, tailWord_1864530, baseEnd_1864530] using wordTrace_append hprefix tailTrace_1864530
  have hstable : (prefixWord ++ tailWord_1864530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864530).length < 2 ^ (prefixWord ++ tailWord_1864530).sum := by decide
  have hdescent : baseEnd_1864530 < baseStart_1864530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864560 : List Nat := [2, 1, 1, 1, 4, 1, 2, 5, 1, 4]
def baseStart_1864560 : Nat := 118140960795 + 1864560 * 2 ^ 59
def prefixEnd_1864560 : Nat := 4983230072969 + 3 ^ 40 * 1864560 * 2
def baseEnd_1864560 : Nat := 638276992764886756083367

theorem tailTrace_1864560 : CollatzResearch.WordTrace tailWord_1864560 prefixEnd_1864560 638276992764886756083367 := by
  unfold tailWord_1864560
  simp only [CollatzResearch.WordTrace]
  refine ⟨34003045062512518170343567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45337393416683357560458089 34003045062512518170343567)
  ·
    refine ⟨51004567593768777255515351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34003045062512518170343567 51004567593768777255515351)
    ·
      refine ⟨76506851390653165883273027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51004567593768777255515351 76506851390653165883273027)
      ·
        refine ⟨114760277085979748824909541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76506851390653165883273027 114760277085979748824909541)
        ·
          refine ⟨21517551953621202904670539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114760277085979748824909541 21517551953621202904670539)
          ·
            refine ⟨32276327930431804357005809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21517551953621202904670539 32276327930431804357005809)
            ·
              refine ⟨24207245947823853267754357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32276327930431804357005809 24207245947823853267754357)
              ·
                refine ⟨2269429307608486243851971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24207245947823853267754357 2269429307608486243851971)
                ·
                  refine ⟨3404143961412729365777957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2269429307608486243851971 3404143961412729365777957)
                  ·
                    refine ⟨638276992764886756083367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3404143961412729365777957 638276992764886756083367)
                    ·
                      rfl

theorem cell22_1864560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 1, 4].length) (baseStart_1864560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864560 prefixEnd_1864560 := by exact prefixLift 1864560
  have htrace : WordTrace (prefixWord ++ tailWord_1864560) baseStart_1864560 baseEnd_1864560 := by
    simpa [prefixWord, tailWord_1864560, baseEnd_1864560] using wordTrace_append hprefix tailTrace_1864560
  have hstable : (prefixWord ++ tailWord_1864560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864560).length < 2 ^ (prefixWord ++ tailWord_1864560).sum := by decide
  have hdescent : baseEnd_1864560 < baseStart_1864560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864605 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_1864605 : Nat := 118140960795 + 1864605 * 2 ^ 59
def prefixEnd_1864605 : Nat := 4983230072969 + 3 ^ 40 * 1864605 * 2
def baseEnd_1864605 : Nat := 638292397184521638708229

theorem tailTrace_1864605 : CollatzResearch.WordTrace tailWord_1864605 prefixEnd_1864605 638292397184521638708229 := by
  unfold tailWord_1864605
  simp only [CollatzResearch.WordTrace]
  refine ⟨68007731409862009026075269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45338487606574672684050179 68007731409862009026075269)
  ·
    refine ⟨12751449639349126692389113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68007731409862009026075269 12751449639349126692389113)
    ·
      refine ⟨9563587229511845019291835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12751449639349126692389113 9563587229511845019291835)
      ·
        refine ⟨14345380844267767528937753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9563587229511845019291835 14345380844267767528937753)
        ·
          refine ⟨10759035633200825646703315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14345380844267767528937753 10759035633200825646703315)
          ·
            refine ⟨16138553449801238470054973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10759035633200825646703315 16138553449801238470054973)
            ·
              refine ⟨6051957543675464426270615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16138553449801238470054973 6051957543675464426270615)
              ·
                refine ⟨9077936315513196639405923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6051957543675464426270615 9077936315513196639405923)
                ·
                  refine ⟨13616904473269794959108885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9077936315513196639405923 13616904473269794959108885)
                  ·
                    refine ⟨638292397184521638708229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13616904473269794959108885 638292397184521638708229)
                    ·
                      rfl

theorem cell22_1864605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_1864605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864605 prefixEnd_1864605 := by exact prefixLift 1864605
  have htrace : WordTrace (prefixWord ++ tailWord_1864605) baseStart_1864605 baseEnd_1864605 := by
    simpa [prefixWord, tailWord_1864605, baseEnd_1864605] using wordTrace_append hprefix tailTrace_1864605
  have hstable : (prefixWord ++ tailWord_1864605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864605).length < 2 ^ (prefixWord ++ tailWord_1864605).sum := by decide
  have hdescent : baseEnd_1864605 < baseStart_1864605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864609 : List Nat := [1, 2, 3, 4, 1, 2, 2, 3, 4]
def baseStart_1864609 : Nat := 118140960795 + 1864609 * 2 ^ 59
def prefixEnd_1864609 : Nat := 4983230072969 + 3 ^ 40 * 1864609 * 2
def baseEnd_1864609 : Nat := 212764588822088987202739

theorem tailTrace_1864609 : CollatzResearch.WordTrace tailWord_1864609 prefixEnd_1864609 212764588822088987202739 := by
  unfold tailWord_1864609
  simp only [CollatzResearch.WordTrace]
  refine ⟨68007877301847517709220881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45338584867898345139480587 68007877301847517709220881)
  ·
    refine ⟨51005907976385638281915661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68007877301847517709220881 51005907976385638281915661)
    ·
      refine ⟨19127215491144614355718373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51005907976385638281915661 19127215491144614355718373)
      ·
        refine ⟨3586352904589615191697195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19127215491144614355718373 3586352904589615191697195)
        ·
          refine ⟨5379529356884422787545793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3586352904589615191697195 5379529356884422787545793)
          ·
            refine ⟨4034647017663317090659345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5379529356884422787545793 4034647017663317090659345)
            ·
              refine ⟨3025985263247487817994509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4034647017663317090659345 3025985263247487817994509)
              ·
                refine ⟨1134744473717807931747941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3025985263247487817994509 1134744473717807931747941)
                ·
                  refine ⟨212764588822088987202739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1134744473717807931747941 212764588822088987202739)
                  ·
                    rfl

theorem cell22_1864609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 4].length) (baseStart_1864609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864609 prefixEnd_1864609 := by exact prefixLift 1864609
  have htrace : WordTrace (prefixWord ++ tailWord_1864609) baseStart_1864609 baseEnd_1864609 := by
    simpa [prefixWord, tailWord_1864609, baseEnd_1864609] using wordTrace_append hprefix tailTrace_1864609
  have hstable : (prefixWord ++ tailWord_1864609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864609).length < 2 ^ (prefixWord ++ tailWord_1864609).sum := by decide
  have hdescent : baseEnd_1864609 < baseStart_1864609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864652 : List Nat := [2, 2, 1, 4, 1, 1, 1, 4, 3, 3]
def baseStart_1864652 : Nat := 118140960795 + 1864652 * 2 ^ 59
def prefixEnd_1864652 : Nat := 4983230072969 + 3 ^ 40 * 1864652 * 2
def baseEnd_1864652 : Nat := 638308486245029182783085

theorem tailTrace_1864652 : CollatzResearch.WordTrace tailWord_1864652 prefixEnd_1864652 638308486245029182783085 := by
  unfold tailWord_1864652
  simp only [CollatzResearch.WordTrace]
  refine ⟨34004722820345868026518105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45339630427127824035357473 34004722820345868026518105)
  ·
    refine ⟨25503542115259401019888579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34004722820345868026518105 25503542115259401019888579)
    ·
      refine ⟨38255313172889101529832869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25503542115259401019888579 38255313172889101529832869)
      ·
        refine ⟨7172871219916706536843663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38255313172889101529832869 7172871219916706536843663)
        ·
          refine ⟨10759306829875059805265495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7172871219916706536843663 10759306829875059805265495)
          ·
            refine ⟨16138960244812589707898243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10759306829875059805265495 16138960244812589707898243)
            ·
              refine ⟨24208440367218884561847365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16138960244812589707898243 24208440367218884561847365)
              ·
                refine ⟨4539082568853540855346381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24208440367218884561847365 4539082568853540855346381)
                ·
                  refine ⟨1702155963320077820754893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4539082568853540855346381 1702155963320077820754893)
                  ·
                    refine ⟨638308486245029182783085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1702155963320077820754893 638308486245029182783085)
                    ·
                      rfl

theorem cell22_1864652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_1864652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864652 prefixEnd_1864652 := by exact prefixLift 1864652
  have htrace : WordTrace (prefixWord ++ tailWord_1864652) baseStart_1864652 baseEnd_1864652 := by
    simpa [prefixWord, tailWord_1864652, baseEnd_1864652] using wordTrace_append hprefix tailTrace_1864652
  have hstable : (prefixWord ++ tailWord_1864652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864652).length < 2 ^ (prefixWord ++ tailWord_1864652).sum := by decide
  have hdescent : baseEnd_1864652 < baseStart_1864652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864665 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 7]
def baseStart_1864665 : Nat := 118140960795 + 1864665 * 2 ^ 59
def prefixEnd_1864665 : Nat := 4983230072969 + 3 ^ 40 * 1864665 * 2
def baseEnd_1864665 : Nat := 212770978803567160736015

theorem tailTrace_1864665 : CollatzResearch.WordTrace tailWord_1864665 prefixEnd_1864665 212770978803567160736015 := by
  unfold tailWord_1864665
  simp only [CollatzResearch.WordTrace]
  refine ⟨68009919789644639273259449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45339946526429759515506299 68009919789644639273259449)
  ·
    refine ⟨51007439842233479454944587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68009919789644639273259449 51007439842233479454944587)
    ·
      refine ⟨76511159763350219182416881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51007439842233479454944587 76511159763350219182416881)
      ·
        refine ⟨57383369822512664386812661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76511159763350219182416881 57383369822512664386812661)
        ·
          refine ⟨5379690920860562286263687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57383369822512664386812661 5379690920860562286263687)
          ·
            refine ⟨8069536381290843429395531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5379690920860562286263687 8069536381290843429395531)
            ·
              refine ⟨12104304571936265144093297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8069536381290843429395531 12104304571936265144093297)
              ·
                refine ⟨9078228428952198858069973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12104304571936265144093297 9078228428952198858069973)
                ·
                  refine ⟨212770978803567160736015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9078228428952198858069973 212770978803567160736015)
                  ·
                    rfl

theorem cell22_1864665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 7].length) (baseStart_1864665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864665 prefixEnd_1864665 := by exact prefixLift 1864665
  have htrace : WordTrace (prefixWord ++ tailWord_1864665) baseStart_1864665 baseEnd_1864665 := by
    simpa [prefixWord, tailWord_1864665, baseEnd_1864665] using wordTrace_append hprefix tailTrace_1864665
  have hstable : (prefixWord ++ tailWord_1864665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864665).length < 2 ^ (prefixWord ++ tailWord_1864665).sum := by decide
  have hdescent : baseEnd_1864665 < baseStart_1864665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864680 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 4, 5]
def baseStart_1864680 : Nat := 118140960795 + 1864680 * 2 ^ 59
def prefixEnd_1864680 : Nat := 4983230072969 + 3 ^ 40 * 1864680 * 2
def baseEnd_1864680 : Nat := 638318071217246443082999

theorem tailTrace_1864680 : CollatzResearch.WordTrace tailWord_1864680 prefixEnd_1864680 638318071217246443082999 := by
  unfold tailWord_1864680
  simp only [CollatzResearch.WordTrace]
  refine ⟨34005233442295148417527747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45340311256393531223370329 34005233442295148417527747)
  ·
    refine ⟨51007850163442722626291621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34005233442295148417527747 51007850163442722626291621)
    ·
      refine ⟨9563971905645510492429679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51007850163442722626291621 9563971905645510492429679)
      ·
        refine ⟨14345957858468265738644519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9563971905645510492429679 14345957858468265738644519)
        ·
          refine ⟨21518936787702398607966779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14345957858468265738644519 21518936787702398607966779)
          ·
            refine ⟨32278405181553597911950169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21518936787702398607966779 32278405181553597911950169)
            ·
              refine ⟨24208803886165198433962627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32278405181553597911950169 24208803886165198433962627)
              ·
                refine ⟨36313205829247797650943941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24208803886165198433962627 36313205829247797650943941)
                ·
                  refine ⟨6808726092983962059551989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36313205829247797650943941 6808726092983962059551989)
                  ·
                    refine ⟨638318071217246443082999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6808726092983962059551989 638318071217246443082999)
                    ·
                      rfl

theorem cell22_1864680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_1864680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864680 prefixEnd_1864680 := by exact prefixLift 1864680
  have htrace : WordTrace (prefixWord ++ tailWord_1864680) baseStart_1864680 baseEnd_1864680 := by
    simpa [prefixWord, tailWord_1864680, baseEnd_1864680] using wordTrace_append hprefix tailTrace_1864680
  have hstable : (prefixWord ++ tailWord_1864680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864680).length < 2 ^ (prefixWord ++ tailWord_1864680).sum := by decide
  have hdescent : baseEnd_1864680 < baseStart_1864680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864686 : List Nat := [4, 1, 2, 1, 4, 2, 1, 1, 3, 3]
def baseStart_1864686 : Nat := 118140960795 + 1864686 * 2 ^ 59
def prefixEnd_1864686 : Nat := 4983230072969 + 3 ^ 40 * 1864686 * 2
def baseEnd_1864686 : Nat := 638320125139864427432981

theorem tailTrace_1864686 : CollatzResearch.WordTrace tailWord_1864686 prefixEnd_1864686 638320125139864427432981 := by
  unfold tailWord_1864686
  simp only [CollatzResearch.WordTrace]
  refine ⟨8501335715321069982471739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45340457148379039906515941 8501335715321069982471739)
  ·
    refine ⟨12752003572981604973707609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8501335715321069982471739 12752003572981604973707609)
    ·
      refine ⟨9564002679736203730280707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12752003572981604973707609 9564002679736203730280707)
      ·
        refine ⟨14346004019604305595421061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9564002679736203730280707 14346004019604305595421061)
        ·
          refine ⟨2689875753675807299141449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14346004019604305595421061 2689875753675807299141449)
          ·
            refine ⟨2017406815256855474356087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2689875753675807299141449 2017406815256855474356087)
            ·
              refine ⟨3026110222885283211534131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2017406815256855474356087 3026110222885283211534131)
              ·
                refine ⟨4539165334327924817301197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3026110222885283211534131 4539165334327924817301197)
                ·
                  refine ⟨1702187000372971806487949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4539165334327924817301197 1702187000372971806487949)
                  ·
                    refine ⟨638320125139864427432981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1702187000372971806487949 638320125139864427432981)
                    ·
                      rfl

theorem cell22_1864686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_1864686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864686 prefixEnd_1864686 := by exact prefixLift 1864686
  have htrace : WordTrace (prefixWord ++ tailWord_1864686) baseStart_1864686 baseEnd_1864686 := by
    simpa [prefixWord, tailWord_1864686, baseEnd_1864686] using wordTrace_append hprefix tailTrace_1864686
  have hstable : (prefixWord ++ tailWord_1864686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864686).length < 2 ^ (prefixWord ++ tailWord_1864686).sum := by decide
  have hdescent : baseEnd_1864686 < baseStart_1864686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864712 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 3, 4]
def baseStart_1864712 : Nat := 118140960795 + 1864712 * 2 ^ 59
def prefixEnd_1864712 : Nat := 4983230072969 + 3 ^ 40 * 1864712 * 2
def baseEnd_1864712 : Nat := 638329025471209026282901

theorem tailTrace_1864712 : CollatzResearch.WordTrace tailWord_1864712 prefixEnd_1864712 638329025471209026282901 := by
  unfold tailWord_1864712
  simp only [CollatzResearch.WordTrace]
  refine ⟨34005817010237183150110195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45341089346982910866813593 34005817010237183150110195)
  ·
    refine ⟨51008725515355774725165293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34005817010237183150110195 51008725515355774725165293)
    ·
      refine ⟨19128272068258415521936985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51008725515355774725165293 19128272068258415521936985)
      ·
        refine ⟨14346204051193811641452739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19128272068258415521936985 14346204051193811641452739)
        ·
          refine ⟨21519306076790717462179109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14346204051193811641452739 21519306076790717462179109)
          ·
            refine ⟨4034869889398259524158583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21519306076790717462179109 4034869889398259524158583)
            ·
              refine ⟨6052304834097389286237875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4034869889398259524158583 6052304834097389286237875)
              ·
                refine ⟨9078457251146083929356813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6052304834097389286237875 9078457251146083929356813)
                ·
                  refine ⟨3404421469179781473508805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9078457251146083929356813 3404421469179781473508805)
                  ·
                    refine ⟨638329025471209026282901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3404421469179781473508805 638329025471209026282901)
                    ·
                      rfl

theorem cell22_1864712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_1864712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864712 prefixEnd_1864712 := by exact prefixLift 1864712
  have htrace : WordTrace (prefixWord ++ tailWord_1864712) baseStart_1864712 baseEnd_1864712 := by
    simpa [prefixWord, tailWord_1864712, baseEnd_1864712] using wordTrace_append hprefix tailTrace_1864712
  have hstable : (prefixWord ++ tailWord_1864712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864712).length < 2 ^ (prefixWord ++ tailWord_1864712).sum := by decide
  have hdescent : baseEnd_1864712 < baseStart_1864712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864881 : List Nat := [1, 2, 2, 5, 1, 1, 3, 2, 1, 4]
def baseStart_1864881 : Nat := 118140960795 + 1864881 * 2 ^ 59
def prefixEnd_1864881 : Nat := 4983230072969 + 3 ^ 40 * 1864881 * 2
def baseEnd_1864881 : Nat := 638386877624948918807383

theorem tailTrace_1864881 : CollatzResearch.WordTrace tailWord_1864881 prefixEnd_1864881 638386877624948918807383 := by
  unfold tailWord_1864881
  simp only [CollatzResearch.WordTrace]
  refine ⟨68017797956862108163122497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45345198637908072108748331 68017797956862108163122497)
  ·
    refine ⟨51013348467646581122341873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68017797956862108163122497 51013348467646581122341873)
    ·
      refine ⟨38260011350734935841756405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51013348467646581122341873 38260011350734935841756405)
      ·
        refine ⟨3586876064131400235164663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38260011350734935841756405 3586876064131400235164663)
        ·
          refine ⟨5380314096197100352746995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3586876064131400235164663 5380314096197100352746995)
          ·
            refine ⟨8070471144295650529120493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5380314096197100352746995 8070471144295650529120493)
            ·
              refine ⟨3026426679110868948420185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8070471144295650529120493 3026426679110868948420185)
              ·
                refine ⟨2269820009333151711315139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3026426679110868948420185 2269820009333151711315139)
                ·
                  refine ⟨3404730013999727566972709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2269820009333151711315139 3404730013999727566972709)
                  ·
                    refine ⟨638386877624948918807383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3404730013999727566972709 638386877624948918807383)
                    ·
                      rfl

theorem cell22_1864881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_1864881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864881 prefixEnd_1864881 := by exact prefixLift 1864881
  have htrace : WordTrace (prefixWord ++ tailWord_1864881) baseStart_1864881 baseEnd_1864881 := by
    simpa [prefixWord, tailWord_1864881, baseEnd_1864881] using wordTrace_append hprefix tailTrace_1864881
  have hstable : (prefixWord ++ tailWord_1864881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864881).length < 2 ^ (prefixWord ++ tailWord_1864881).sum := by decide
  have hdescent : baseEnd_1864881 < baseStart_1864881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864894 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_1864894 : Nat := 118140960795 + 1864894 * 2 ^ 59
def prefixEnd_1864894 : Nat := 4983230072969 + 3 ^ 40 * 1864894 * 2
def baseEnd_1864894 : Nat := 638391327790621218232343

theorem tailTrace_1864894 : CollatzResearch.WordTrace tailWord_1864894 prefixEnd_1864894 638391327790621218232343 := by
  unfold tailWord_1864894
  simp only [CollatzResearch.WordTrace]
  refine ⟨8502284013226876422918217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45345514737210007588897157 8502284013226876422918217)
  ·
    refine ⟨6376713009920157317188663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8502284013226876422918217 6376713009920157317188663)
    ·
      refine ⟨9565069514880235975782995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6376713009920157317188663 9565069514880235975782995)
      ·
        refine ⟨14347604272320353963674493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9565069514880235975782995 14347604272320353963674493)
        ·
          refine ⟨5380351602120132736377935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14347604272320353963674493 5380351602120132736377935)
          ·
            refine ⟨8070527403180199104566903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5380351602120132736377935 8070527403180199104566903)
            ·
              refine ⟨12105791104770298656850355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8070527403180199104566903 12105791104770298656850355)
              ·
                refine ⟨18158686657155447985275533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12105791104770298656850355 18158686657155447985275533)
                ·
                  refine ⟨6809507496433292994478325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18158686657155447985275533 6809507496433292994478325)
                  ·
                    refine ⟨638391327790621218232343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6809507496433292994478325 638391327790621218232343)
                    ·
                      rfl

theorem cell22_1864894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_1864894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864894 prefixEnd_1864894 := by exact prefixLift 1864894
  have htrace : WordTrace (prefixWord ++ tailWord_1864894) baseStart_1864894 baseEnd_1864894 := by
    simpa [prefixWord, tailWord_1864894, baseEnd_1864894] using wordTrace_append hprefix tailTrace_1864894
  have hstable : (prefixWord ++ tailWord_1864894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864894).length < 2 ^ (prefixWord ++ tailWord_1864894).sum := by decide
  have hdescent : baseEnd_1864894 < baseStart_1864894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864922 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 2, 7]
def baseStart_1864922 : Nat := 118140960795 + 1864922 * 2 ^ 59
def prefixEnd_1864922 : Nat := 4983230072969 + 3 ^ 40 * 1864922 * 2
def baseEnd_1864922 : Nat := 638400912762838478532257

theorem tailTrace_1864922 : CollatzResearch.WordTrace tailWord_1864922 prefixEnd_1864922 638400912762838478532257 := by
  unfold tailWord_1864922
  simp only [CollatzResearch.WordTrace]
  refine ⟨17004823337428393041341255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45346195566475714776910013 17004823337428393041341255)
  ·
    refine ⟨25507235006142589562011883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17004823337428393041341255 25507235006142589562011883)
    ·
      refine ⟨38260852509213884343017825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25507235006142589562011883 38260852509213884343017825)
      ·
        refine ⟨28695639381910413257263369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38260852509213884343017825 28695639381910413257263369)
        ·
          refine ⟨21521729536432809942947527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28695639381910413257263369 21521729536432809942947527)
          ·
            refine ⟨32282594304649214914421291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21521729536432809942947527 32282594304649214914421291)
            ·
              refine ⟨48423891456973822371631937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32282594304649214914421291 48423891456973822371631937)
              ·
                refine ⟨36317918592730366778723953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48423891456973822371631937 36317918592730366778723953)
                ·
                  refine ⟨27238438944547775084042965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36317918592730366778723953 27238438944547775084042965)
                  ·
                    refine ⟨638400912762838478532257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27238438944547775084042965 638400912762838478532257)
                    ·
                      rfl

theorem cell22_1864922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_1864922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864922 prefixEnd_1864922 := by exact prefixLift 1864922
  have htrace : WordTrace (prefixWord ++ tailWord_1864922) baseStart_1864922 baseEnd_1864922 := by
    simpa [prefixWord, tailWord_1864922, baseEnd_1864922] using wordTrace_append hprefix tailTrace_1864922
  have hstable : (prefixWord ++ tailWord_1864922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864922).length < 2 ^ (prefixWord ++ tailWord_1864922).sum := by decide
  have hdescent : baseEnd_1864922 < baseStart_1864922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864939 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 5, 3]
def baseStart_1864939 : Nat := 118140960795 + 1864939 * 2 ^ 59
def prefixEnd_1864939 : Nat := 4983230072969 + 3 ^ 40 * 1864939 * 2
def baseEnd_1864939 : Nat := 638406732210256100857205

theorem tailTrace_1864939 : CollatzResearch.WordTrace tailWord_1864939 prefixEnd_1864939 638406732210256100857205 := by
  unfold tailWord_1864939
  simp only [CollatzResearch.WordTrace]
  refine ⟨68019913390651984068733871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45346608927101322712489247 68019913390651984068733871)
  ·
    refine ⟨102029870085977976103100807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68019913390651984068733871 102029870085977976103100807)
    ·
      refine ⟨153044805128966964154651211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102029870085977976103100807 153044805128966964154651211)
      ·
        refine ⟨229567207693450446231976817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153044805128966964154651211 229567207693450446231976817)
        ·
          refine ⟨172175405770087834673982613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229567207693450446231976817 172175405770087834673982613)
          ·
            refine ⟨8070722145472867250342935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 172175405770087834673982613 8070722145472867250342935)
            ·
              refine ⟨12106083218209300875514403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8070722145472867250342935 12106083218209300875514403)
              ·
                refine ⟨18159124827313951313271605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12106083218209300875514403 18159124827313951313271605)
                ·
                  refine ⟨1702417952560682935619213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18159124827313951313271605 1702417952560682935619213)
                  ·
                    refine ⟨638406732210256100857205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1702417952560682935619213 638406732210256100857205)
                    ·
                      rfl

theorem cell22_1864939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 3].length) (baseStart_1864939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864939 prefixEnd_1864939 := by exact prefixLift 1864939
  have htrace : WordTrace (prefixWord ++ tailWord_1864939) baseStart_1864939 baseEnd_1864939 := by
    simpa [prefixWord, tailWord_1864939, baseEnd_1864939] using wordTrace_append hprefix tailTrace_1864939
  have hstable : (prefixWord ++ tailWord_1864939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864939).length < 2 ^ (prefixWord ++ tailWord_1864939).sum := by decide
  have hdescent : baseEnd_1864939 < baseStart_1864939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864941 : List Nat := [1, 5, 1, 2, 2, 2, 3, 6]
def baseStart_1864941 : Nat := 118140960795 + 1864941 * 2 ^ 59
def prefixEnd_1864941 : Nat := 4983230072969 + 3 ^ 40 * 1864941 * 2
def baseEnd_1864941 : Nat := 70934157427903195811911

theorem tailTrace_1864941 : CollatzResearch.WordTrace tailWord_1864941 prefixEnd_1864941 70934157427903195811911 := by
  unfold tailWord_1864941
  simp only [CollatzResearch.WordTrace]
  refine ⟨68019986336644738410306677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45346657557763158940204451 68019986336644738410306677)
  ·
    refine ⟨6376873719060444225966251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68019986336644738410306677 6376873719060444225966251)
    ·
      refine ⟨9565310578590666338949377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6376873719060444225966251 9565310578590666338949377)
      ·
        refine ⟨7173982933942999754212033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9565310578590666338949377 7173982933942999754212033)
        ·
          refine ⟨5380487200457249815659025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7173982933942999754212033 5380487200457249815659025)
          ·
            refine ⟨4035365400342937361744269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5380487200457249815659025 4035365400342937361744269)
            ·
              refine ⟨1513262025128601510654101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4035365400342937361744269 1513262025128601510654101)
              ·
                refine ⟨70934157427903195811911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1513262025128601510654101 70934157427903195811911)
                ·
                  rfl

theorem cell22_1864941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 6].length) (baseStart_1864941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864941 prefixEnd_1864941 := by exact prefixLift 1864941
  have htrace : WordTrace (prefixWord ++ tailWord_1864941) baseStart_1864941 baseEnd_1864941 := by
    simpa [prefixWord, tailWord_1864941, baseEnd_1864941] using wordTrace_append hprefix tailTrace_1864941
  have hstable : (prefixWord ++ tailWord_1864941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864941).length < 2 ^ (prefixWord ++ tailWord_1864941).sum := by decide
  have hdescent : baseEnd_1864941 < baseStart_1864941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864943 : List Nat := [1, 1, 2, 1, 8, 1, 1, 1, 2, 4]
def baseStart_1864943 : Nat := 118140960795 + 1864943 * 2 ^ 59
def prefixEnd_1864943 : Nat := 4983230072969 + 3 ^ 40 * 1864943 * 2
def baseEnd_1864943 : Nat := 638408101492001423757193

theorem tailTrace_1864943 : CollatzResearch.WordTrace tailWord_1864943 prefixEnd_1864943 638408101492001423757193 := by
  unfold tailWord_1864943
  simp only [CollatzResearch.WordTrace]
  refine ⟨68020059282637492751879483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45346706188424995167919655 68020059282637492751879483)
  ·
    refine ⟨102030088923956239127819225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68020059282637492751879483 102030088923956239127819225)
    ·
      refine ⟨76522566692967179345864419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102030088923956239127819225 76522566692967179345864419)
      ·
        refine ⟨114783850039450769018796629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76522566692967179345864419 114783850039450769018796629)
        ·
          refine ⟨1345123242649813699439023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 114783850039450769018796629 1345123242649813699439023)
          ·
            refine ⟨2017684863974720549158535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345123242649813699439023 2017684863974720549158535)
            ·
              refine ⟨3026527295962080823737803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2017684863974720549158535 3026527295962080823737803)
              ·
                refine ⟨4539790943943121235606705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3026527295962080823737803 4539790943943121235606705)
                ·
                  refine ⟨3404843207957340926705029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4539790943943121235606705 3404843207957340926705029)
                  ·
                    refine ⟨638408101492001423757193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3404843207957340926705029 638408101492001423757193)
                    ·
                      rfl

theorem cell22_1864943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 2, 4].length) (baseStart_1864943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864943 prefixEnd_1864943 := by exact prefixLift 1864943
  have htrace : WordTrace (prefixWord ++ tailWord_1864943) baseStart_1864943 baseEnd_1864943 := by
    simpa [prefixWord, tailWord_1864943, baseEnd_1864943] using wordTrace_append hprefix tailTrace_1864943
  have hstable : (prefixWord ++ tailWord_1864943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864943).length < 2 ^ (prefixWord ++ tailWord_1864943).sum := by decide
  have hdescent : baseEnd_1864943 < baseStart_1864943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864962 : List Nat := [3, 4, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_1864962 : Nat := 118140960795 + 1864962 * 2 ^ 59
def prefixEnd_1864962 : Nat := 4983230072969 + 3 ^ 40 * 1864962 * 2
def baseEnd_1864962 : Nat := 638414605580291707532135

theorem tailTrace_1864962 : CollatzResearch.WordTrace tailWord_1864962 prefixEnd_1864962 638414605580291707532135 := by
  unfold tailWord_1864962
  simp only [CollatzResearch.WordTrace]
  refine ⟨17005188067392164749205285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45347168179712439331214093 17005188067392164749205285)
  ·
    refine ⟨3188472762636030890475991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17005188067392164749205285 3188472762636030890475991)
    ·
      refine ⟨4782709143954046335713987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3188472762636030890475991 4782709143954046335713987)
      ·
        refine ⟨7174063715931069503570981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4782709143954046335713987 7174063715931069503570981)
        ·
          refine ⟨1345136946737075531919559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7174063715931069503570981 1345136946737075531919559)
          ·
            refine ⟨2017705420105613297879339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345136946737075531919559 2017705420105613297879339)
            ·
              refine ⟨3026558130158419946819009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2017705420105613297879339 3026558130158419946819009)
              ·
                refine ⟨2269918597618814960114257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3026558130158419946819009 2269918597618814960114257)
                ·
                  refine ⟨1702438948214111220085693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2269918597618814960114257 1702438948214111220085693)
                  ·
                    refine ⟨638414605580291707532135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1702438948214111220085693 638414605580291707532135)
                    ·
                      rfl

theorem cell22_1864962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_1864962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864962 prefixEnd_1864962 := by exact prefixLift 1864962
  have htrace : WordTrace (prefixWord ++ tailWord_1864962) baseStart_1864962 baseEnd_1864962 := by
    simpa [prefixWord, tailWord_1864962, baseEnd_1864962] using wordTrace_append hprefix tailTrace_1864962
  have hstable : (prefixWord ++ tailWord_1864962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864962).length < 2 ^ (prefixWord ++ tailWord_1864962).sum := by decide
  have hdescent : baseEnd_1864962 < baseStart_1864962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864984 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 2, 5]
def baseStart_1864984 : Nat := 118140960795 + 1864984 * 2 ^ 59
def prefixEnd_1864984 : Nat := 4983230072969 + 3 ^ 40 * 1864984 * 2
def baseEnd_1864984 : Nat := 638422136629890983482067

theorem tailTrace_1864984 : CollatzResearch.WordTrace tailWord_1864984 prefixEnd_1864984 638422136629890983482067 := by
  unfold tailWord_1864984
  simp only [CollatzResearch.WordTrace]
  refine ⟨34010777337744478377061003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45347703116992637836081337 34010777337744478377061003)
  ·
    refine ⟨51016166006616717565591505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34010777337744478377061003 51016166006616717565591505)
    ·
      refine ⟨38262124504962538174193629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51016166006616717565591505 38262124504962538174193629)
      ·
        refine ⟨14348296689360951815322611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38262124504962538174193629 14348296689360951815322611)
        ·
          refine ⟨21522445034041427722983917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14348296689360951815322611 21522445034041427722983917)
          ·
            refine ⟨8070916887765535396118969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21522445034041427722983917 8070916887765535396118969)
            ·
              refine ⟨6053187665824151547089227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8070916887765535396118969 6053187665824151547089227)
              ·
                refine ⟨9079781498736227320633841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6053187665824151547089227 9079781498736227320633841)
                ·
                  refine ⟨6809836124052170490475381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9079781498736227320633841 6809836124052170490475381)
                  ·
                    refine ⟨638422136629890983482067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6809836124052170490475381 638422136629890983482067)
                    ·
                      rfl

theorem cell22_1864984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_1864984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1864984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1864984 prefixEnd_1864984 := by exact prefixLift 1864984
  have htrace : WordTrace (prefixWord ++ tailWord_1864984) baseStart_1864984 baseEnd_1864984 := by
    simpa [prefixWord, tailWord_1864984, baseEnd_1864984] using wordTrace_append hprefix tailTrace_1864984
  have hstable : (prefixWord ++ tailWord_1864984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864984).length < 2 ^ (prefixWord ++ tailWord_1864984).sum := by decide
  have hdescent : baseEnd_1864984 < baseStart_1864984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865031 : List Nat := [1, 1, 4, 1, 2, 5, 1, 1, 6]
def baseStart_1865031 : Nat := 118140960795 + 1865031 * 2 ^ 59
def prefixEnd_1865031 : Nat := 4983230072969 + 3 ^ 40 * 1865031 * 2
def baseEnd_1865031 : Nat := 212812741896799509185641

theorem tailTrace_1865031 : CollatzResearch.WordTrace tailWord_1865031 prefixEnd_1865031 212812741896799509185641 := by
  unfold tailWord_1865031
  simp only [CollatzResearch.WordTrace]
  refine ⟨68023268906318683781082947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45348845937545789187388631 68023268906318683781082947)
  ·
    refine ⟨102034903359478025671624421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68023268906318683781082947 102034903359478025671624421)
    ·
      refine ⟨19131544379902129813429579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102034903359478025671624421 19131544379902129813429579)
      ·
        refine ⟨28697316569853194720144369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19131544379902129813429579 28697316569853194720144369)
        ·
          refine ⟨21522987427389896040108277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28697316569853194720144369 21522987427389896040108277)
          ·
            refine ⟨2017780071317802753760151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21522987427389896040108277 2017780071317802753760151)
            ·
              refine ⟨3026670106976704130640227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2017780071317802753760151 3026670106976704130640227)
              ·
                refine ⟨4540005160465056195960341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3026670106976704130640227 4540005160465056195960341)
                ·
                  refine ⟨212812741896799509185641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4540005160465056195960341 212812741896799509185641)
                  ·
                    rfl

theorem cell22_1865031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 6].length) (baseStart_1865031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865031 prefixEnd_1865031 := by exact prefixLift 1865031
  have htrace : WordTrace (prefixWord ++ tailWord_1865031) baseStart_1865031 baseEnd_1865031 := by
    simpa [prefixWord, tailWord_1865031, baseEnd_1865031] using wordTrace_append hprefix tailTrace_1865031
  have hstable : (prefixWord ++ tailWord_1865031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865031).length < 2 ^ (prefixWord ++ tailWord_1865031).sum := by decide
  have hdescent : baseEnd_1865031 < baseStart_1865031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865037 : List Nat := [1, 6, 1, 3, 1, 2, 2, 1, 5]
def baseStart_1865037 : Nat := 118140960795 + 1865037 * 2 ^ 59
def prefixEnd_1865037 : Nat := 4983230072969 + 3 ^ 40 * 1865037 * 2
def baseEnd_1865037 : Nat := 212813426537672170635635

theorem tailTrace_1865037 : CollatzResearch.WordTrace tailWord_1865037 prefixEnd_1865037 212813426537672170635635 := by
  unfold tailWord_1865037
  simp only [CollatzResearch.WordTrace]
  refine ⟨68023487744296946805801365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45348991829531297870534243 68023487744296946805801365)
  ·
    refine ⟨3188600988013919381521939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68023487744296946805801365 3188600988013919381521939)
    ·
      refine ⟨4782901482020879072282909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3188600988013919381521939 4782901482020879072282909)
      ·
        refine ⟨1793588055757829652106091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4782901482020879072282909 1793588055757829652106091)
        ·
          refine ⟨2690382083636744478159137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1793588055757829652106091 2690382083636744478159137)
          ·
            refine ⟨2017786562727558358619353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2690382083636744478159137 2017786562727558358619353)
            ·
              refine ⟨1513339922045668768964515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2017786562727558358619353 1513339922045668768964515)
              ·
                refine ⟨2270009883068503153446773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1513339922045668768964515 2270009883068503153446773)
                ·
                  refine ⟨212813426537672170635635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2270009883068503153446773 212813426537672170635635)
                  ·
                    rfl

theorem cell22_1865037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_1865037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865037 prefixEnd_1865037 := by exact prefixLift 1865037
  have htrace : WordTrace (prefixWord ++ tailWord_1865037) baseStart_1865037 baseEnd_1865037 := by
    simpa [prefixWord, tailWord_1865037, baseEnd_1865037] using wordTrace_append hprefix tailTrace_1865037
  have hstable : (prefixWord ++ tailWord_1865037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865037).length < 2 ^ (prefixWord ++ tailWord_1865037).sum := by decide
  have hdescent : baseEnd_1865037 < baseStart_1865037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865059 : List Nat := [1, 1, 1, 5, 2, 2, 2, 8]
def baseStart_1865059 : Nat := 118140960795 + 1865059 * 2 ^ 59
def prefixEnd_1865059 : Nat := 4983230072969 + 3 ^ 40 * 1865059 * 2
def baseEnd_1865059 : Nat := 70938645629179531984093

theorem tailTrace_1865059 : CollatzResearch.WordTrace tailWord_1865059 prefixEnd_1865059 70938645629179531984093 := by
  unfold tailWord_1865059
  simp only [CollatzResearch.WordTrace]
  refine ⟨68024290150217244563102231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45349526766811496375401487 68024290150217244563102231)
  ·
    refine ⟨102036435225325866844653347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68024290150217244563102231 102036435225325866844653347)
    ·
      refine ⟨153054652837988800266980021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102036435225325866844653347 153054652837988800266980021)
      ·
        refine ⟨14348873703561450025029377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153054652837988800266980021 14348873703561450025029377)
        ·
          refine ⟨10761655277671087518772033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14348873703561450025029377 10761655277671087518772033)
          ·
            refine ⟨8071241458253315639079025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10761655277671087518772033 8071241458253315639079025)
            ·
              refine ⟨6053431093689986729309269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8071241458253315639079025 6053431093689986729309269)
              ·
                refine ⟨70938645629179531984093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6053431093689986729309269 70938645629179531984093)
                ·
                  rfl

theorem cell22_1865059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 8].length) (baseStart_1865059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865059 prefixEnd_1865059 := by exact prefixLift 1865059
  have htrace : WordTrace (prefixWord ++ tailWord_1865059) baseStart_1865059 baseEnd_1865059 := by
    simpa [prefixWord, tailWord_1865059, baseEnd_1865059] using wordTrace_append hprefix tailTrace_1865059
  have hstable : (prefixWord ++ tailWord_1865059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865059).length < 2 ^ (prefixWord ++ tailWord_1865059).sum := by decide
  have hdescent : baseEnd_1865059 < baseStart_1865059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865061 : List Nat := [1, 3, 1, 3, 1, 2, 4, 1, 2, 4]
def baseStart_1865061 : Nat := 118140960795 + 1865061 * 2 ^ 59
def prefixEnd_1865061 : Nat := 4983230072969 + 3 ^ 40 * 1865061 * 2
def baseEnd_1865061 : Nat := 638448495303488449306831

theorem tailTrace_1865061 : CollatzResearch.WordTrace tailWord_1865061 prefixEnd_1865061 638448495303488449306831 := by
  unfold tailWord_1865061
  simp only [CollatzResearch.WordTrace]
  refine ⟨68024363096209998904675037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45349575397473332603116691 68024363096209998904675037)
  ·
    refine ⟨25509136161078749589253139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68024363096209998904675037 25509136161078749589253139)
    ·
      refine ⟨38263704241618124383879709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25509136161078749589253139 38263704241618124383879709)
      ·
        refine ⟨14348889090606796643954891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38263704241618124383879709 14348889090606796643954891)
        ·
          refine ⟨21523333635910194965932337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14348889090606796643954891 21523333635910194965932337)
          ·
            refine ⟨16142500226932646224449253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21523333635910194965932337 16142500226932646224449253)
            ·
              refine ⟨3026718792549871167084235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16142500226932646224449253 3026718792549871167084235)
              ·
                refine ⟨4540078188824806750626353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3026718792549871167084235 4540078188824806750626353)
                ·
                  refine ⟨3405058641618605062969765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4540078188824806750626353 3405058641618605062969765)
                  ·
                    refine ⟨638448495303488449306831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3405058641618605062969765 638448495303488449306831)
                    ·
                      rfl

theorem cell22_1865061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_1865061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865061 prefixEnd_1865061 := by exact prefixLift 1865061
  have htrace : WordTrace (prefixWord ++ tailWord_1865061) baseStart_1865061 baseEnd_1865061 := by
    simpa [prefixWord, tailWord_1865061, baseEnd_1865061] using wordTrace_append hprefix tailTrace_1865061
  have hstable : (prefixWord ++ tailWord_1865061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865061).length < 2 ^ (prefixWord ++ tailWord_1865061).sum := by decide
  have hdescent : baseEnd_1865061 < baseStart_1865061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865108 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_1865108 : Nat := 118140960795 + 1865108 * 2 ^ 59
def prefixEnd_1865108 : Nat := 4983230072969 + 3 ^ 40 * 1865108 * 2
def baseEnd_1865108 : Nat := 638464584363995993381687

theorem tailTrace_1865108 : CollatzResearch.WordTrace tailWord_1865108 prefixEnd_1865108 638464584363995993381687 := by
  unfold tailWord_1865108
  simp only [CollatzResearch.WordTrace]
  refine ⟨34013038663519862965817989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45350718218026483954423985 34013038663519862965817989)
  ·
    refine ⟨6377444749409974306090873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34013038663519862965817989 6377444749409974306090873)
    ·
      refine ⟨4783083562057480729568155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6377444749409974306090873 4783083562057480729568155)
      ·
        refine ⟨7174625343086221094352233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4783083562057480729568155 7174625343086221094352233)
        ·
          refine ⟨5380969007314665820764175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7174625343086221094352233 5380969007314665820764175)
          ·
            refine ⟨8071453510971998731146263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5380969007314665820764175 8071453510971998731146263)
            ·
              refine ⟨12107180266457998096719395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8071453510971998731146263 12107180266457998096719395)
              ·
                refine ⟨18160770399686997145079093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12107180266457998096719395 18160770399686997145079093)
                ·
                  refine ⟨1702572224970655982351165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18160770399686997145079093 1702572224970655982351165)
                  ·
                    refine ⟨638464584363995993381687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1702572224970655982351165 638464584363995993381687)
                    ·
                      rfl

theorem cell22_1865108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_1865108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865108 prefixEnd_1865108 := by exact prefixLift 1865108
  have htrace : WordTrace (prefixWord ++ tailWord_1865108) baseStart_1865108 baseEnd_1865108 := by
    simpa [prefixWord, tailWord_1865108, baseEnd_1865108] using wordTrace_append hprefix tailTrace_1865108
  have hstable : (prefixWord ++ tailWord_1865108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865108).length < 2 ^ (prefixWord ++ tailWord_1865108).sum := by decide
  have hdescent : baseEnd_1865108 < baseStart_1865108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865166 : List Nat := [4, 1, 1, 1, 2, 1, 4, 2, 6]
def baseStart_1865166 : Nat := 118140960795 + 1865166 * 2 ^ 59
def prefixEnd_1865166 : Nat := 4983230072969 + 3 ^ 40 * 1865166 * 2
def baseEnd_1865166 : Nat := 212828146316434391810503

theorem tailTrace_1865166 : CollatzResearch.WordTrace tailWord_1865166 prefixEnd_1865166 212828146316434391810503 := by
  unfold tailWord_1865166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8503524095103700229655919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45352128507219734558164901 8503524095103700229655919)
  ·
    refine ⟨12755286142655550344483879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8503524095103700229655919 12755286142655550344483879)
    ·
      refine ⟨19132929213983325516725819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12755286142655550344483879 19132929213983325516725819)
      ·
        refine ⟨28699393820974988275088729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19132929213983325516725819 28699393820974988275088729)
        ·
          refine ⟨21524545365731241206316547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28699393820974988275088729 21524545365731241206316547)
          ·
            refine ⟨32286818048596861809474821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21524545365731241206316547 32286818048596861809474821)
            ·
              refine ⟨6053778384111911589276529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32286818048596861809474821 6053778384111911589276529)
              ·
                refine ⟨4540333788083933691957397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6053778384111911589276529 4540333788083933691957397)
                ·
                  refine ⟨212828146316434391810503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4540333788083933691957397 212828146316434391810503)
                  ·
                    rfl

theorem cell22_1865166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_1865166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865166 prefixEnd_1865166 := by exact prefixLift 1865166
  have htrace : WordTrace (prefixWord ++ tailWord_1865166) baseStart_1865166 baseEnd_1865166 := by
    simpa [prefixWord, tailWord_1865166, baseEnd_1865166] using wordTrace_append hprefix tailTrace_1865166
  have hstable : (prefixWord ++ tailWord_1865166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865166).length < 2 ^ (prefixWord ++ tailWord_1865166).sum := by decide
  have hdescent : baseEnd_1865166 < baseStart_1865166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865198 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 4, 3]
def baseStart_1865198 : Nat := 118140960795 + 1865198 * 2 ^ 59
def prefixEnd_1865198 : Nat := 4983230072969 + 3 ^ 40 * 1865198 * 2
def baseEnd_1865198 : Nat := 638495393203265758631411

theorem tailTrace_1865198 : CollatzResearch.WordTrace tailWord_1865198 prefixEnd_1865198 638495393203265758631411 := by
  unfold tailWord_1865198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8503669987089208912801531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45352906597809114201608165 8503669987089208912801531)
  ·
    refine ⟨12755504980633813369202297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8503669987089208912801531 12755504980633813369202297)
    ·
      refine ⟨9566628735475360026901723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12755504980633813369202297 9566628735475360026901723)
      ·
        refine ⟨14349943103213040040352585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9566628735475360026901723 14349943103213040040352585)
        ·
          refine ⟨10762457327409780030264439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14349943103213040040352585 10762457327409780030264439)
          ·
            refine ⟨16143685991114670045396659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10762457327409780030264439 16143685991114670045396659)
            ·
              refine ⟨24215528986672005068094989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16143685991114670045396659 24215528986672005068094989)
              ·
                refine ⟨9080823370002001900535621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24215528986672005068094989 9080823370002001900535621)
                ·
                  refine ⟨1702654381875375356350429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9080823370002001900535621 1702654381875375356350429)
                  ·
                    refine ⟨638495393203265758631411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1702654381875375356350429 638495393203265758631411)
                    ·
                      rfl

theorem cell22_1865198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_1865198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865198 prefixEnd_1865198 := by exact prefixLift 1865198
  have htrace : WordTrace (prefixWord ++ tailWord_1865198) baseStart_1865198 baseEnd_1865198 := by
    simpa [prefixWord, tailWord_1865198, baseEnd_1865198] using wordTrace_append hprefix tailTrace_1865198
  have hstable : (prefixWord ++ tailWord_1865198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865198).length < 2 ^ (prefixWord ++ tailWord_1865198).sum := by decide
  have hdescent : baseEnd_1865198 < baseStart_1865198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865200 : List Nat := [2, 1, 1, 1, 3, 5, 3, 2, 4]
def baseStart_1865200 : Nat := 118140960795 + 1865200 * 2 ^ 59
def prefixEnd_1865200 : Nat := 4983230072969 + 3 ^ 40 * 1865200 * 2
def baseEnd_1865200 : Nat := 212832025948046140027135

theorem tailTrace_1865200 : CollatzResearch.WordTrace tailWord_1865200 prefixEnd_1865200 212832025948046140027135 := by
  unfold tailWord_1865200
  simp only [CollatzResearch.WordTrace]
  refine ⟨34014716421353212821992527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45352955228470950429323369 34014716421353212821992527)
  ·
    refine ⟨51022074632029819232988791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34014716421353212821992527 51022074632029819232988791)
    ·
      refine ⟨76533111948044728849483187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51022074632029819232988791 76533111948044728849483187)
      ·
        refine ⟨114799667922067093274224781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76533111948044728849483187 114799667922067093274224781)
        ·
          refine ⟨43049875470775159977834293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114799667922067093274224781 43049875470775159977834293)
          ·
            refine ⟨4035925825385171247921965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43049875470775159977834293 4035925825385171247921965)
            ·
              refine ⟨1513472184519439217970737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4035925825385171247921965 1513472184519439217970737)
              ·
                refine ⟨1135104138389579413478053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1513472184519439217970737 1135104138389579413478053)
                ·
                  refine ⟨212832025948046140027135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1135104138389579413478053 212832025948046140027135)
                  ·
                    rfl

theorem cell22_1865200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 4].length) (baseStart_1865200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865200 prefixEnd_1865200 := by exact prefixLift 1865200
  have htrace : WordTrace (prefixWord ++ tailWord_1865200) baseStart_1865200 baseEnd_1865200 := by
    simpa [prefixWord, tailWord_1865200, baseEnd_1865200] using wordTrace_append hprefix tailTrace_1865200
  have hstable : (prefixWord ++ tailWord_1865200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865200).length < 2 ^ (prefixWord ++ tailWord_1865200).sum := by decide
  have hdescent : baseEnd_1865200 < baseStart_1865200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865230 : List Nat := [4, 1, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_1865230 : Nat := 118140960795 + 1865230 * 2 ^ 59
def prefixEnd_1865230 : Nat := 4983230072969 + 3 ^ 40 * 1865230 * 2
def baseEnd_1865230 : Nat := 638506347457228341831313

theorem tailTrace_1865230 : CollatzResearch.WordTrace tailWord_1865230 prefixEnd_1865230 638506347457228341831313 := by
  unfold tailWord_1865230
  simp only [CollatzResearch.WordTrace]
  refine ⟨8503815879074717595947143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45353684688398493845051429 8503815879074717595947143)
  ·
    refine ⟨12755723818612076393920715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8503815879074717595947143 12755723818612076393920715)
    ·
      refine ⟨19133585727918114590881073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12755723818612076393920715 19133585727918114590881073)
      ·
        refine ⟨14350189295938585943160805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19133585727918114590881073 14350189295938585943160805)
        ·
          refine ⟨2690660492988484864342651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14350189295938585943160805 2690660492988484864342651)
          ·
            refine ⟨4035990739482727296513977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2690660492988484864342651 4035990739482727296513977)
            ·
              refine ⟨3026993054612045472385483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4035990739482727296513977 3026993054612045472385483)
              ·
                refine ⟨4540489581918068208578225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3026993054612045472385483 4540489581918068208578225)
                ·
                  refine ⟨3405367186438551156433669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4540489581918068208578225 3405367186438551156433669)
                  ·
                    refine ⟨638506347457228341831313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3405367186438551156433669 638506347457228341831313)
                    ·
                      rfl

theorem cell22_1865230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_1865230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865230 prefixEnd_1865230 := by exact prefixLift 1865230
  have htrace : WordTrace (prefixWord ++ tailWord_1865230) baseStart_1865230 baseEnd_1865230 := by
    simpa [prefixWord, tailWord_1865230, baseEnd_1865230] using wordTrace_append hprefix tailTrace_1865230
  have hstable : (prefixWord ++ tailWord_1865230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865230).length < 2 ^ (prefixWord ++ tailWord_1865230).sum := by decide
  have hdescent : baseEnd_1865230 < baseStart_1865230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865271 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 1, 7]
def baseStart_1865271 : Nat := 118140960795 + 1865271 * 2 ^ 59
def prefixEnd_1865271 : Nat := 4983230072969 + 3 ^ 40 * 1865271 * 2
def baseEnd_1865271 : Nat := 638520382595117901556187

theorem tailTrace_1865271 : CollatzResearch.WordTrace tailWord_1865271 prefixEnd_1865271 638520382595117901556187 := by
  unfold tailWord_1865271
  simp only [CollatzResearch.WordTrace]
  refine ⟨68032022425449204769819667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45354681616966136513213111 68032022425449204769819667)
  ·
    refine ⟨102048033638173807154729501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68032022425449204769819667 102048033638173807154729501)
    ·
      refine ⟨38268012614315177683023563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102048033638173807154729501 38268012614315177683023563)
      ·
        refine ⟨57402018921472766524535345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38268012614315177683023563 57402018921472766524535345)
        ·
          refine ⟨43051514191104574893401509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57402018921472766524535345 43051514191104574893401509)
          ·
            refine ⟨8072158910832107792512783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43051514191104574893401509 8072158910832107792512783)
            ·
              refine ⟨12108238366248161688769175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8072158910832107792512783 12108238366248161688769175)
              ·
                refine ⟨18162357549372242533153763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12108238366248161688769175 18162357549372242533153763)
                ·
                  refine ⟨27243536324058363799730645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18162357549372242533153763 27243536324058363799730645)
                  ·
                    refine ⟨638520382595117901556187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27243536324058363799730645 638520382595117901556187)
                    ·
                      rfl

theorem cell22_1865271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_1865271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865271 prefixEnd_1865271 := by exact prefixLift 1865271
  have htrace : WordTrace (prefixWord ++ tailWord_1865271) baseStart_1865271 baseEnd_1865271 := by
    simpa [prefixWord, tailWord_1865271, baseEnd_1865271] using wordTrace_append hprefix tailTrace_1865271
  have hstable : (prefixWord ++ tailWord_1865271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865271).length < 2 ^ (prefixWord ++ tailWord_1865271).sum := by decide
  have hdescent : baseEnd_1865271 < baseStart_1865271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865273 : List Nat := [1, 2, 1, 5, 1, 2, 2, 3, 5]
def baseStart_1865273 : Nat := 118140960795 + 1865273 * 2 ^ 59
def prefixEnd_1865273 : Nat := 4983230072969 + 3 ^ 40 * 1865273 * 2
def baseEnd_1865273 : Nat := 212840355745330187668727

theorem tailTrace_1865273 : CollatzResearch.WordTrace tailWord_1865273 prefixEnd_1865273 212840355745330187668727 := by
  unfold tailWord_1865273
  simp only [CollatzResearch.WordTrace]
  refine ⟨68032095371441959111392473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45354730247627972740928315 68032095371441959111392473)
  ·
    refine ⟨51024071528581469333544355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68032095371441959111392473 51024071528581469333544355)
    ·
      refine ⟨76536107292872204000316533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51024071528581469333544355 76536107292872204000316533)
      ·
        refine ⟨7175260058706769125029675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76536107292872204000316533 7175260058706769125029675)
        ·
          refine ⟨10762890088060153687544513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7175260058706769125029675 10762890088060153687544513)
          ·
            refine ⟨8072167566045115265658385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10762890088060153687544513 8072167566045115265658385)
            ·
              refine ⟨6054125674533836449243789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8072167566045115265658385 6054125674533836449243789)
              ·
                refine ⟨2270297127950188668466421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6054125674533836449243789 2270297127950188668466421)
                ·
                  refine ⟨212840355745330187668727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2270297127950188668466421 212840355745330187668727)
                  ·
                    rfl

theorem cell22_1865273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 5].length) (baseStart_1865273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865273 prefixEnd_1865273 := by exact prefixLift 1865273
  have htrace : WordTrace (prefixWord ++ tailWord_1865273) baseStart_1865273 baseEnd_1865273 := by
    simpa [prefixWord, tailWord_1865273, baseEnd_1865273] using wordTrace_append hprefix tailTrace_1865273
  have hstable : (prefixWord ++ tailWord_1865273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865273).length < 2 ^ (prefixWord ++ tailWord_1865273).sum := by decide
  have hdescent : baseEnd_1865273 < baseStart_1865273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865301 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 10]
def baseStart_1865301 : Nat := 118140960795 + 1865301 * 2 ^ 59
def prefixEnd_1865301 : Nat := 4983230072969 + 3 ^ 40 * 1865301 * 2
def baseEnd_1865301 : Nat := 212843550736069274435365

theorem tailTrace_1865301 : CollatzResearch.WordTrace tailWord_1865301 prefixEnd_1865301 212843550736069274435365 := by
  unfold tailWord_1865301
  simp only [CollatzResearch.WordTrace]
  refine ⟨68033116615340519893411757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45355411076893679928941171 68033116615340519893411757)
  ·
    refine ⟨25512418730752694960029409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68033116615340519893411757 25512418730752694960029409)
    ·
      refine ⟨19134314048064521220022057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25512418730752694960029409 19134314048064521220022057)
      ·
        refine ⟨14350735536048390915016543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19134314048064521220022057 14350735536048390915016543)
        ·
          refine ⟨21526103304072586372524815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14350735536048390915016543 21526103304072586372524815)
          ·
            refine ⟨32289154956108879558787223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21526103304072586372524815 32289154956108879558787223)
            ·
              refine ⟨48433732434163319338180835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32289154956108879558787223 48433732434163319338180835)
              ·
                refine ⟨72650598651244979007271253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48433732434163319338180835 72650598651244979007271253)
                ·
                  refine ⟨212843550736069274435365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 72650598651244979007271253 212843550736069274435365)
                  ·
                    rfl

theorem cell22_1865301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_1865301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865301 prefixEnd_1865301 := by exact prefixLift 1865301
  have htrace : WordTrace (prefixWord ++ tailWord_1865301) baseStart_1865301 baseEnd_1865301 := by
    simpa [prefixWord, tailWord_1865301, baseEnd_1865301] using wordTrace_append hprefix tailTrace_1865301
  have hstable : (prefixWord ++ tailWord_1865301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865301).length < 2 ^ (prefixWord ++ tailWord_1865301).sum := by decide
  have hdescent : baseEnd_1865301 < baseStart_1865301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865425 : List Nat := [1, 2, 2, 1, 2, 5, 2, 2, 5]
def baseStart_1865425 : Nat := 118140960795 + 1865425 * 2 ^ 59
def prefixEnd_1865425 : Nat := 4983230072969 + 3 ^ 40 * 1865425 * 2
def baseEnd_1865425 : Nat := 212857699980770944401905

theorem tailTrace_1865425 : CollatzResearch.WordTrace tailWord_1865425 prefixEnd_1865425 212857699980770944401905 := by
  unfold tailWord_1865425
  simp only [CollatzResearch.WordTrace]
  refine ⟨68037639266891289070925729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45358426177927526047283819 68037639266891289070925729)
  ·
    refine ⟨51028229450168466803194297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68037639266891289070925729 51028229450168466803194297)
    ·
      refine ⟨38271172087626350102395723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51028229450168466803194297 38271172087626350102395723)
      ·
        refine ⟨57406758131439525153593585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38271172087626350102395723 57406758131439525153593585)
        ·
          refine ⟨43055068598579643865195189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57406758131439525153593585 43055068598579643865195189)
          ·
            refine ⟨4036412681116841612362049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43055068598579643865195189 4036412681116841612362049)
            ·
              refine ⟨3027309510837631209271537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4036412681116841612362049 3027309510837631209271537)
              ·
                refine ⟨2270482133128223406953653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3027309510837631209271537 2270482133128223406953653)
                ·
                  refine ⟨212857699980770944401905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2270482133128223406953653 212857699980770944401905)
                  ·
                    rfl

theorem cell22_1865425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 5].length) (baseStart_1865425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865425 prefixEnd_1865425 := by exact prefixLift 1865425
  have htrace : WordTrace (prefixWord ++ tailWord_1865425) baseStart_1865425 baseEnd_1865425 := by
    simpa [prefixWord, tailWord_1865425, baseEnd_1865425] using wordTrace_append hprefix tailTrace_1865425
  have hstable : (prefixWord ++ tailWord_1865425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865425).length < 2 ^ (prefixWord ++ tailWord_1865425).sum := by decide
  have hdescent : baseEnd_1865425 < baseStart_1865425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865455 : List Nat := [1, 1, 2, 1, 5, 1, 2, 4, 1, 4]
def baseStart_1865455 : Nat := 118140960795 + 1865455 * 2 ^ 59
def prefixEnd_1865455 : Nat := 4983230072969 + 3 ^ 40 * 1865455 * 2
def baseEnd_1865455 : Nat := 638583369555402754955623

theorem tailTrace_1865455 : CollatzResearch.WordTrace tailWord_1865455 prefixEnd_1865455 638583369555402754955623 := by
  unfold tailWord_1865455
  simp only [CollatzResearch.WordTrace]
  refine ⟨68038733456782604194517819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45359155637855069463011879 68038733456782604194517819)
  ·
    refine ⟨102058100185173906291776729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68038733456782604194517819 102058100185173906291776729)
    ·
      refine ⟨76543575138880429718832547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102058100185173906291776729 76543575138880429718832547)
      ·
        refine ⟨114815362708320644578248821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76543575138880429718832547 114815362708320644578248821)
        ·
          refine ⟨10763940253905060429210827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114815362708320644578248821 10763940253905060429210827)
          ·
            refine ⟨16145910380857590643816241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10763940253905060429210827 16145910380857590643816241)
            ·
              refine ⟨12109432785643192982862181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16145910380857590643816241 12109432785643192982862181)
              ·
                refine ⟨2270518647308098684286659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12109432785643192982862181 2270518647308098684286659)
                ·
                  refine ⟨3405777970962148026429989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2270518647308098684286659 3405777970962148026429989)
                  ·
                    refine ⟨638583369555402754955623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3405777970962148026429989 638583369555402754955623)
                    ·
                      rfl

theorem cell22_1865455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 4].length) (baseStart_1865455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865455 prefixEnd_1865455 := by exact prefixLift 1865455
  have htrace : WordTrace (prefixWord ++ tailWord_1865455) baseStart_1865455 baseEnd_1865455 := by
    simpa [prefixWord, tailWord_1865455, baseEnd_1865455] using wordTrace_append hprefix tailTrace_1865455
  have hstable : (prefixWord ++ tailWord_1865455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865455).length < 2 ^ (prefixWord ++ tailWord_1865455).sum := by decide
  have hdescent : baseEnd_1865455 < baseStart_1865455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865598 : List Nat := [4, 2, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1865598 : Nat := 118140960795 + 1865598 * 2 ^ 59
def prefixEnd_1865598 : Nat := 4983230072969 + 3 ^ 40 * 1865598 * 2
def baseEnd_1865598 : Nat := 638632321377798048630185

theorem tailTrace_1865598 : CollatzResearch.WordTrace tailWord_1865598 prefixEnd_1865598 638632321377798048630185 := by
  unfold tailWord_1865598
  simp only [CollatzResearch.WordTrace]
  refine ⟨8505493636908067452121681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45362632730176359744648965 8505493636908067452121681)
  ·
    refine ⟨6379120227681050589091261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8505493636908067452121681 6379120227681050589091261)
    ·
      refine ⟨2392170085380393970909223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6379120227681050589091261 2392170085380393970909223)
      ·
        refine ⟨3588255128070590956363835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2392170085380393970909223 3588255128070590956363835)
        ·
          refine ⟨5382382692105886434545753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3588255128070590956363835 5382382692105886434545753)
          ·
            refine ⟨4036787019079414825909315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5382382692105886434545753 4036787019079414825909315)
            ·
              refine ⟨6055180528619122238863973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4036787019079414825909315 6055180528619122238863973)
              ·
                refine ⟨1135346349116085419786995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6055180528619122238863973 1135346349116085419786995)
                ·
                  refine ⟨1703019523674128129680493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1135346349116085419786995 1703019523674128129680493)
                  ·
                    refine ⟨638632321377798048630185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1703019523674128129680493 638632321377798048630185)
                    ·
                      rfl

theorem cell22_1865598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1865598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865598 prefixEnd_1865598 := by exact prefixLift 1865598
  have htrace : WordTrace (prefixWord ++ tailWord_1865598) baseStart_1865598 baseEnd_1865598 := by
    simpa [prefixWord, tailWord_1865598, baseEnd_1865598] using wordTrace_append hprefix tailTrace_1865598
  have hstable : (prefixWord ++ tailWord_1865598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865598).length < 2 ^ (prefixWord ++ tailWord_1865598).sum := by decide
  have hdescent : baseEnd_1865598 < baseStart_1865598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865605 : List Nat := [1, 3, 1, 1, 3, 2, 2, 3, 6]
def baseStart_1865605 : Nat := 118140960795 + 1865605 * 2 ^ 59
def prefixEnd_1865605 : Nat := 4983230072969 + 3 ^ 40 * 1865605 * 2
def baseEnd_1865605 : Nat := 212878239206950787901721

theorem tailTrace_1865605 : CollatzResearch.WordTrace tailWord_1865605 prefixEnd_1865605 212878239206950787901721 := by
  unfold tailWord_1865605
  simp only [CollatzResearch.WordTrace]
  refine ⟨68044204406239179812478269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45362802937492786541652179 68044204406239179812478269)
  ·
    refine ⟨25516576652339692429679351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68044204406239179812478269 25516576652339692429679351)
    ·
      refine ⟨38274864978509538644519027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25516576652339692429679351 38274864978509538644519027)
      ·
        refine ⟨57412297467764307966778541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38274864978509538644519027 57412297467764307966778541)
        ·
          refine ⟨21529611550411615487541953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57412297467764307966778541 21529611550411615487541953)
          ·
            refine ⟨16147208662808711615656465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21529611550411615487541953 16147208662808711615656465)
            ·
              refine ⟨12110406497106533711742349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16147208662808711615656465 12110406497106533711742349)
              ·
                refine ⟨4541402436414950141903381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12110406497106533711742349 4541402436414950141903381)
                ·
                  refine ⟨212878239206950787901721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4541402436414950141903381 212878239206950787901721)
                  ·
                    rfl

theorem cell22_1865605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_1865605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865605 prefixEnd_1865605 := by exact prefixLift 1865605
  have htrace : WordTrace (prefixWord ++ tailWord_1865605) baseStart_1865605 baseEnd_1865605 := by
    simpa [prefixWord, tailWord_1865605, baseEnd_1865605] using wordTrace_append hprefix tailTrace_1865605
  have hstable : (prefixWord ++ tailWord_1865605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865605).length < 2 ^ (prefixWord ++ tailWord_1865605).sum := by decide
  have hdescent : baseEnd_1865605 < baseStart_1865605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865639 : List Nat := [1, 1, 6, 1, 2, 1, 1, 5, 4]
def baseStart_1865639 : Nat := 118140960795 + 1865639 * 2 ^ 59
def prefixEnd_1865639 : Nat := 4983230072969 + 3 ^ 40 * 1865639 * 2
def baseEnd_1865639 : Nat := 212882118838562536118353

theorem tailTrace_1865639 : CollatzResearch.WordTrace tailWord_1865639 prefixEnd_1865639 212882118838562536118353 := by
  unfold tailWord_1865639
  simp only [CollatzResearch.WordTrace]
  refine ⟨68045444488116003619215971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45363629658744002412810647 68045444488116003619215971)
  ·
    refine ⟨102068166732174005428823957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68045444488116003619215971 102068166732174005428823957)
    ·
      refine ⟨4784445315570656504476123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102068166732174005428823957 4784445315570656504476123)
      ·
        refine ⟨7176667973355984756714185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4784445315570656504476123 7176667973355984756714185)
        ·
          refine ⟨5382500980016988567535639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7176667973355984756714185 5382500980016988567535639)
          ·
            refine ⟨8073751470025482851303459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5382500980016988567535639 8073751470025482851303459)
            ·
              refine ⟨12110627205038224276955189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8073751470025482851303459 12110627205038224276955189)
              ·
                refine ⟨1135371300472333525964549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12110627205038224276955189 1135371300472333525964549)
                ·
                  refine ⟨212882118838562536118353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1135371300472333525964549 212882118838562536118353)
                  ·
                    rfl

theorem cell22_1865639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 4].length) (baseStart_1865639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865639 prefixEnd_1865639 := by exact prefixLift 1865639
  have htrace : WordTrace (prefixWord ++ tailWord_1865639) baseStart_1865639 baseEnd_1865639 := by
    simpa [prefixWord, tailWord_1865639, baseEnd_1865639] using wordTrace_append hprefix tailTrace_1865639
  have hstable : (prefixWord ++ tailWord_1865639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865639).length < 2 ^ (prefixWord ++ tailWord_1865639).sum := by decide
  have hdescent : baseEnd_1865639 < baseStart_1865639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865680 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 2, 6]
def baseStart_1865680 : Nat := 118140960795 + 1865680 * 2 ^ 59
def prefixEnd_1865680 : Nat := 4983230072969 + 3 ^ 40 * 1865680 * 2
def baseEnd_1865680 : Nat := 638660391653577168079933

theorem tailTrace_1865680 : CollatzResearch.WordTrace tailWord_1865680 prefixEnd_1865680 638660391653577168079933 := by
  unfold tailWord_1865680
  simp only [CollatzResearch.WordTrace]
  refine ⟨34023469940483733810729247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45364626587311645080972329 34023469940483733810729247)
  ·
    refine ⟨51035204910725600716093871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34023469940483733810729247 51035204910725600716093871)
    ·
      refine ⟨76552807366088401074140807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51035204910725600716093871 76552807366088401074140807)
      ·
        refine ⟨114829211049132601611211211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76552807366088401074140807 114829211049132601611211211)
        ·
          refine ⟨172243816573698902416816817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114829211049132601611211211 172243816573698902416816817)
          ·
            refine ⟨129182862430274176812612613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172243816573698902416816817 129182862430274176812612613)
            ·
              refine ⟨24221786705676408152364865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129182862430274176812612613 24221786705676408152364865)
              ·
                refine ⟨18166340029257306114273649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24221786705676408152364865 18166340029257306114273649)
                ·
                  refine ⟨13624755021942979585705237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18166340029257306114273649 13624755021942979585705237)
                  ·
                    refine ⟨638660391653577168079933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13624755021942979585705237 638660391653577168079933)
                    ·
                      rfl

theorem cell22_1865680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_1865680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865680 prefixEnd_1865680 := by exact prefixLift 1865680
  have htrace : WordTrace (prefixWord ++ tailWord_1865680) baseStart_1865680 baseEnd_1865680 := by
    simpa [prefixWord, tailWord_1865680, baseEnd_1865680] using wordTrace_append hprefix tailTrace_1865680
  have hstable : (prefixWord ++ tailWord_1865680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865680).length < 2 ^ (prefixWord ++ tailWord_1865680).sum := by decide
  have hdescent : baseEnd_1865680 < baseStart_1865680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865767 : List Nat := [1, 1, 7, 1, 2, 2, 2, 2, 1, 3]
def baseStart_1865767 : Nat := 118140960795 + 1865767 * 2 ^ 59
def prefixEnd_1865767 : Nat := 4983230072969 + 3 ^ 40 * 1865767 * 2
def baseEnd_1865767 : Nat := 638690173531537941154667

theorem tailTrace_1865767 : CollatzResearch.WordTrace tailWord_1865767 prefixEnd_1865767 638690173531537941154667 := by
  unfold tailWord_1865767
  simp only [CollatzResearch.WordTrace]
  refine ⟨68050113031652281479875555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45366742021101520986583703 68050113031652281479875555)
  ·
    refine ⟨102075169547478422219813333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68050113031652281479875555 102075169547478422219813333)
    ·
      refine ⟨2392386786269025520776875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 102075169547478422219813333 2392386786269025520776875)
      ·
        refine ⟨3588580179403538281165313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2392386786269025520776875 3588580179403538281165313)
        ·
          refine ⟨2691435134552653710873985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3588580179403538281165313 2691435134552653710873985)
          ·
            refine ⟨2018576350914490283155489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2691435134552653710873985 2018576350914490283155489)
            ·
              refine ⟨1513932263185867712366617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2018576350914490283155489 1513932263185867712366617)
              ·
                refine ⟨1135449197389400784274963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1513932263185867712366617 1135449197389400784274963)
                ·
                  refine ⟨1703173796084101176412445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1135449197389400784274963 1703173796084101176412445)
                  ·
                    refine ⟨638690173531537941154667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1703173796084101176412445 638690173531537941154667)
                    ·
                      rfl

theorem cell22_1865767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_1865767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865767 prefixEnd_1865767 := by exact prefixLift 1865767
  have htrace : WordTrace (prefixWord ++ tailWord_1865767) baseStart_1865767 baseEnd_1865767 := by
    simpa [prefixWord, tailWord_1865767, baseEnd_1865767] using wordTrace_append hprefix tailTrace_1865767
  have hstable : (prefixWord ++ tailWord_1865767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865767).length < 2 ^ (prefixWord ++ tailWord_1865767).sum := by decide
  have hdescent : baseEnd_1865767 < baseStart_1865767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865789 : List Nat := [1, 4, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_1865789 : Nat := 118140960795 + 1865789 * 2 ^ 59
def prefixEnd_1865789 : Nat := 4983230072969 + 3 ^ 40 * 1865789 * 2
def baseEnd_1865789 : Nat := 638697704581137217104599

theorem tailTrace_1865789 : CollatzResearch.WordTrace tailWord_1865789 prefixEnd_1865789 638697704581137217104599 := by
  unfold tailWord_1865789
  simp only [CollatzResearch.WordTrace]
  refine ⟨68050915437572579237176421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45367276958381719491450947 68050915437572579237176421)
  ·
    refine ⟨12759546644544858606970579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68050915437572579237176421 12759546644544858606970579)
    ·
      refine ⟨19139319966817287910455869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12759546644544858606970579 19139319966817287910455869)
      ·
        refine ⟨7177244987556482966420951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19139319966817287910455869 7177244987556482966420951)
        ·
          refine ⟨10765867481334724449631427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7177244987556482966420951 10765867481334724449631427)
          ·
            refine ⟨16148801222002086674447141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10765867481334724449631427 16148801222002086674447141)
            ·
              refine ⟨3027900229125391251458839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16148801222002086674447141 3027900229125391251458839)
              ·
                refine ⟨4541850343688086877188259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3027900229125391251458839 4541850343688086877188259)
                ·
                  refine ⟨6812775515532130315782389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4541850343688086877188259 6812775515532130315782389)
                  ·
                    refine ⟨638697704581137217104599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6812775515532130315782389 638697704581137217104599)
                    ·
                      rfl

theorem cell22_1865789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_1865789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865789 prefixEnd_1865789 := by exact prefixLift 1865789
  have htrace : WordTrace (prefixWord ++ tailWord_1865789) baseStart_1865789 baseEnd_1865789 := by
    simpa [prefixWord, tailWord_1865789, baseEnd_1865789] using wordTrace_append hprefix tailTrace_1865789
  have hstable : (prefixWord ++ tailWord_1865789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865789).length < 2 ^ (prefixWord ++ tailWord_1865789).sum := by decide
  have hdescent : baseEnd_1865789 < baseStart_1865789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865804 : List Nat := [2, 2, 1, 3, 1, 1, 5, 1, 2, 4]
def baseStart_1865804 : Nat := 118140960795 + 1865804 * 2 ^ 59
def prefixEnd_1865804 : Nat := 4983230072969 + 3 ^ 40 * 1865804 * 2
def baseEnd_1865804 : Nat := 638702839387682177979553

theorem tailTrace_1865804 : CollatzResearch.WordTrace tailWord_1865804 prefixEnd_1865804 638702839387682177979553 := by
  unfold tailWord_1865804
  simp only [CollatzResearch.WordTrace]
  refine ⟨34025731266259118399486233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45367641688345491199314977 34025731266259118399486233)
  ·
    refine ⟨25519298449694338799614675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34025731266259118399486233 25519298449694338799614675)
    ·
      refine ⟨38278947674541508199422013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25519298449694338799614675 38278947674541508199422013)
      ·
        refine ⟨14354605377953065574783255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38278947674541508199422013 14354605377953065574783255)
        ·
          refine ⟨21531908066929598362174883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14354605377953065574783255 21531908066929598362174883)
          ·
            refine ⟨32297862100394397543262325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21531908066929598362174883 32297862100394397543262325)
            ·
              refine ⟨3027924571911974769680843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32297862100394397543262325 3027924571911974769680843)
              ·
                refine ⟨4541886857867962154521265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3027924571911974769680843 4541886857867962154521265)
                ·
                  refine ⟨3406415143400971615890949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4541886857867962154521265 3406415143400971615890949)
                  ·
                    refine ⟨638702839387682177979553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3406415143400971615890949 638702839387682177979553)
                    ·
                      rfl

theorem cell22_1865804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_1865804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865804 prefixEnd_1865804 := by exact prefixLift 1865804
  have htrace : WordTrace (prefixWord ++ tailWord_1865804) baseStart_1865804 baseEnd_1865804 := by
    simpa [prefixWord, tailWord_1865804, baseEnd_1865804] using wordTrace_append hprefix tailTrace_1865804
  have hstable : (prefixWord ++ tailWord_1865804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865804).length < 2 ^ (prefixWord ++ tailWord_1865804).sum := by decide
  have hdescent : baseEnd_1865804 < baseStart_1865804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865810 : List Nat := [3, 2, 2, 1, 5, 1, 2, 1, 1, 4]
def baseStart_1865810 : Nat := 118140960795 + 1865810 * 2 ^ 59
def prefixEnd_1865810 : Nat := 4983230072969 + 3 ^ 40 * 1865810 * 2
def baseEnd_1865810 : Nat := 638704893310300162329535

theorem tailTrace_1865810 : CollatzResearch.WordTrace tailWord_1865810 prefixEnd_1865810 638704893310300162329535 := by
  unfold tailWord_1865810
  simp only [CollatzResearch.WordTrace]
  refine ⟨17012920342624124955922721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45367787580330999882460589 17012920342624124955922721)
  ·
    refine ⟨12759690256968093716942041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17012920342624124955922721 12759690256968093716942041)
    ·
      refine ⟨9569767692726070287706531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12759690256968093716942041 9569767692726070287706531)
      ·
        refine ⟨14354651539089105431559797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9569767692726070287706531 14354651539089105431559797)
        ·
          refine ⟨1345748581789603634208731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14354651539089105431559797 1345748581789603634208731)
          ·
            refine ⟨2018622872684405451313097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345748581789603634208731 2018622872684405451313097)
            ·
              refine ⟨1513967154513304088484823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2018622872684405451313097 1513967154513304088484823)
              ·
                refine ⟨2270950731769956132727235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1513967154513304088484823 2270950731769956132727235)
                ·
                  refine ⟨3406426097654934199090853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2270950731769956132727235 3406426097654934199090853)
                  ·
                    refine ⟨638704893310300162329535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3406426097654934199090853 638704893310300162329535)
                    ·
                      rfl

theorem cell22_1865810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_1865810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865810 prefixEnd_1865810 := by exact prefixLift 1865810
  have htrace : WordTrace (prefixWord ++ tailWord_1865810) baseStart_1865810 baseEnd_1865810 := by
    simpa [prefixWord, tailWord_1865810, baseEnd_1865810] using wordTrace_append hprefix tailTrace_1865810
  have hstable : (prefixWord ++ tailWord_1865810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865810).length < 2 ^ (prefixWord ++ tailWord_1865810).sum := by decide
  have hdescent : baseEnd_1865810 < baseStart_1865810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865864 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 7]
def baseStart_1865864 : Nat := 118140960795 + 1865864 * 2 ^ 59
def prefixEnd_1865864 : Nat := 4983230072969 + 3 ^ 40 * 1865864 * 2
def baseEnd_1865864 : Nat := 212907792871287340493123

theorem tailTrace_1865864 : CollatzResearch.WordTrace tailWord_1865864 prefixEnd_1865864 212907792871287340493123 := by
  unfold tailWord_1865864
  simp only [CollatzResearch.WordTrace]
  refine ⟨34026825456150433523078323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45369100608200578030771097 34026825456150433523078323)
  ·
    refine ⟨51040238184225650284617485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34026825456150433523078323 51040238184225650284617485)
    ·
      refine ⟨19140089319084618856731557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51040238184225650284617485 19140089319084618856731557)
      ·
        refine ⟨3588766747328366035637167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19140089319084618856731557 3588766747328366035637167)
        ·
          refine ⟨5383150120992549053455751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3588766747328366035637167 5383150120992549053455751)
          ·
            refine ⟨8074725181488823580183627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5383150120992549053455751 8074725181488823580183627)
            ·
              refine ⟨12112087772233235370275441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8074725181488823580183627 12112087772233235370275441)
              ·
                refine ⟨9084065829174926527706581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12112087772233235370275441 9084065829174926527706581)
                ·
                  refine ⟨212907792871287340493123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9084065829174926527706581 212907792871287340493123)
                  ·
                    rfl

theorem cell22_1865864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 7].length) (baseStart_1865864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865864 prefixEnd_1865864 := by exact prefixLift 1865864
  have htrace : WordTrace (prefixWord ++ tailWord_1865864) baseStart_1865864 baseEnd_1865864 := by
    simpa [prefixWord, tailWord_1865864, baseEnd_1865864] using wordTrace_append hprefix tailTrace_1865864
  have hstable : (prefixWord ++ tailWord_1865864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865864).length < 2 ^ (prefixWord ++ tailWord_1865864).sum := by decide
  have hdescent : baseEnd_1865864 < baseStart_1865864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865885 : List Nat := [1, 4, 2, 1, 1, 4, 3, 2, 1, 3]
def baseStart_1865885 : Nat := 118140960795 + 1865885 * 2 ^ 59
def prefixEnd_1865885 : Nat := 4983230072969 + 3 ^ 40 * 1865885 * 2
def baseEnd_1865885 : Nat := 638730567343024966704305

theorem tailTrace_1865885 : CollatzResearch.WordTrace tailWord_1865885 prefixEnd_1865885 638730567343024966704305 := by
  unfold tailWord_1865885
  simp only [CollatzResearch.WordTrace]
  refine ⟨68054416845224787632671109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45369611230149858421780739 68054416845224787632671109)
  ·
    refine ⟨12760203158479647681125833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68054416845224787632671109 12760203158479647681125833)
    ·
      refine ⟨9570152368859735760844375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12760203158479647681125833 9570152368859735760844375)
      ·
        refine ⟨14355228553289603641266563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9570152368859735760844375 14355228553289603641266563)
        ·
          refine ⟨21532842829934405461899845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14355228553289603641266563 21532842829934405461899845)
          ·
            refine ⟨4037408030612701024106221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21532842829934405461899845 4037408030612701024106221)
            ·
              refine ⟨1514028011479762884039833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4037408030612701024106221 1514028011479762884039833)
              ·
                refine ⟨1135521008609822163029875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1514028011479762884039833 1135521008609822163029875)
                ·
                  refine ⟨1703281512914733244544813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1135521008609822163029875 1703281512914733244544813)
                  ·
                    refine ⟨638730567343024966704305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1703281512914733244544813 638730567343024966704305)
                    ·
                      rfl

theorem cell22_1865885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_1865885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865885 prefixEnd_1865885 := by exact prefixLift 1865885
  have htrace : WordTrace (prefixWord ++ tailWord_1865885) baseStart_1865885 baseEnd_1865885 := by
    simpa [prefixWord, tailWord_1865885, baseEnd_1865885] using wordTrace_append hprefix tailTrace_1865885
  have hstable : (prefixWord ++ tailWord_1865885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865885).length < 2 ^ (prefixWord ++ tailWord_1865885).sum := by decide
  have hdescent : baseEnd_1865885 < baseStart_1865885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865898 : List Nat := [3, 1, 5, 1, 2, 1, 1, 3, 5]
def baseStart_1865898 : Nat := 118140960795 + 1865898 * 2 ^ 59
def prefixEnd_1865898 : Nat := 4983230072969 + 3 ^ 40 * 1865898 * 2
def baseEnd_1865898 : Nat := 212911672502899088709755

theorem tailTrace_1865898 : CollatzResearch.WordTrace tailWord_1865898 prefixEnd_1865898 212911672502899088709755 := by
  unfold tailWord_1865898
  simp only [CollatzResearch.WordTrace]
  refine ⟨17013722748544422713223587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45369927329451793901929565 17013722748544422713223587)
  ·
    refine ⟨25520584122816634069835381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17013722748544422713223587 25520584122816634069835381)
    ·
      refine ⟨2392554761514059444047067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25520584122816634069835381 2392554761514059444047067)
      ·
        refine ⟨3588832142271089166070601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2392554761514059444047067 3588832142271089166070601)
        ·
          refine ⟨2691624106703316874552951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3588832142271089166070601 2691624106703316874552951)
          ·
            refine ⟨4037436160054975311829427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2691624106703316874552951 4037436160054975311829427)
            ·
              refine ⟨6056154240082462967744141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4037436160054975311829427 6056154240082462967744141)
              ·
                refine ⟨2271057840030923612904053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6056154240082462967744141 2271057840030923612904053)
                ·
                  refine ⟨212911672502899088709755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2271057840030923612904053 212911672502899088709755)
                  ·
                    rfl

theorem cell22_1865898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_1865898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865898 prefixEnd_1865898 := by exact prefixLift 1865898
  have htrace : WordTrace (prefixWord ++ tailWord_1865898) baseStart_1865898 baseEnd_1865898 := by
    simpa [prefixWord, tailWord_1865898, baseEnd_1865898] using wordTrace_append hprefix tailTrace_1865898
  have hstable : (prefixWord ++ tailWord_1865898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865898).length < 2 ^ (prefixWord ++ tailWord_1865898).sum := by decide
  have hdescent : baseEnd_1865898 < baseStart_1865898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865911 : List Nat := [1, 1, 3, 1, 4, 2, 3, 2, 1, 4]
def baseStart_1865911 : Nat := 118140960795 + 1865911 * 2 ^ 59
def prefixEnd_1865911 : Nat := 4983230072969 + 3 ^ 40 * 1865911 * 2
def baseEnd_1865911 : Nat := 638739467674369565554225

theorem tailTrace_1865911 : CollatzResearch.WordTrace tailWord_1865911 prefixEnd_1865911 638739467674369565554225 := by
  unfold tailWord_1865911
  simp only [CollatzResearch.WordTrace]
  refine ⟨68055365143130594073117587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45370243428753729382078391 68055365143130594073117587)
  ·
    refine ⟨102083047714695891109676381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68055365143130594073117587 102083047714695891109676381)
    ·
      refine ⟨38281142893010959166128643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102083047714695891109676381 38281142893010959166128643)
      ·
        refine ⟨57421714339516438749192965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38281142893010959166128643 57421714339516438749192965)
        ·
          refine ⟨10766571438659332265473681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57421714339516438749192965 10766571438659332265473681)
          ·
            refine ⟨8074928578994499199105261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10766571438659332265473681 8074928578994499199105261)
            ·
              refine ⟨3028098217122937199664473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8074928578994499199105261 3028098217122937199664473)
              ·
                refine ⟨2271073662842202899748355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3028098217122937199664473 2271073662842202899748355)
                ·
                  refine ⟨3406610494263304349622533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2271073662842202899748355 3406610494263304349622533)
                  ·
                    refine ⟨638739467674369565554225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3406610494263304349622533 638739467674369565554225)
                    ·
                      rfl

theorem cell22_1865911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_1865911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1865911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1865911 prefixEnd_1865911 := by exact prefixLift 1865911
  have htrace : WordTrace (prefixWord ++ tailWord_1865911) baseStart_1865911 baseEnd_1865911 := by
    simpa [prefixWord, tailWord_1865911, baseEnd_1865911] using wordTrace_append hprefix tailTrace_1865911
  have hstable : (prefixWord ++ tailWord_1865911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865911).length < 2 ^ (prefixWord ++ tailWord_1865911).sum := by decide
  have hdescent : baseEnd_1865911 < baseStart_1865911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866059 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 5, 5]
def baseStart_1866059 : Nat := 118140960795 + 1866059 * 2 ^ 59
def prefixEnd_1866059 : Nat := 4983230072969 + 3 ^ 40 * 1866059 * 2
def baseEnd_1866059 : Nat := 638790131098946512853771

theorem tailTrace_1866059 : CollatzResearch.WordTrace tailWord_1866059 prefixEnd_1866059 638790131098946512853771 := by
  unfold tailWord_1866059
  simp only [CollatzResearch.WordTrace]
  refine ⟨68060763146594415349505231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45373842097729610233003487 68060763146594415349505231)
  ·
    refine ⟨102091144719891623024257847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68060763146594415349505231 102091144719891623024257847)
    ·
      refine ⟨153136717079837434536386771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102091144719891623024257847 153136717079837434536386771)
      ·
        refine ⟨229705075619756151804580157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153136717079837434536386771 229705075619756151804580157)
        ·
          refine ⟨86139403357408556926717559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229705075619756151804580157 86139403357408556926717559)
          ·
            refine ⟨129209105036112835390076339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86139403357408556926717559 129209105036112835390076339)
            ·
              refine ⟨193813657554169253085114509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129209105036112835390076339 193813657554169253085114509)
              ·
                refine ⟨72680121582813469906917941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193813657554169253085114509 72680121582813469906917941)
                ·
                  refine ⟨6813761398388762803773557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72680121582813469906917941 6813761398388762803773557)
                  ·
                    refine ⟨638790131098946512853771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6813761398388762803773557 638790131098946512853771)
                    ·
                      rfl

theorem cell22_1866059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 5].length) (baseStart_1866059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866059 prefixEnd_1866059 := by exact prefixLift 1866059
  have htrace : WordTrace (prefixWord ++ tailWord_1866059) baseStart_1866059 baseEnd_1866059 := by
    simpa [prefixWord, tailWord_1866059, baseEnd_1866059] using wordTrace_append hprefix tailTrace_1866059
  have hstable : (prefixWord ++ tailWord_1866059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866059).length < 2 ^ (prefixWord ++ tailWord_1866059).sum := by decide
  have hdescent : baseEnd_1866059 < baseStart_1866059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866080 : List Nat := [2, 1, 1, 3, 5, 2, 1, 2, 1, 4]
def baseStart_1866080 : Nat := 118140960795 + 1866080 * 2 ^ 59
def prefixEnd_1866080 : Nat := 4983230072969 + 3 ^ 40 * 1866080 * 2
def baseEnd_1866080 : Nat := 638797319828109458078707

theorem tailTrace_1866080 : CollatzResearch.WordTrace tailWord_1866080 prefixEnd_1866080 638797319828109458078707 := by
  unfold tailWord_1866080
  simp only [CollatzResearch.WordTrace]
  refine ⟨34030764539759167968009847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45374352719678890624013129 34030764539759167968009847)
  ·
    refine ⟨51046146809638751952014771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34030764539759167968009847 51046146809638751952014771)
    ·
      refine ⟨76569220214458127928022157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51046146809638751952014771 76569220214458127928022157)
      ·
        refine ⟨28713457580421797973008309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76569220214458127928022157 28713457580421797973008309)
        ·
          refine ⟨2691886648164543559969529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28713457580421797973008309 2691886648164543559969529)
          ·
            refine ⟨2018914986123407669977147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2691886648164543559969529 2018914986123407669977147)
            ·
              refine ⟨3028372479185111504965721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2018914986123407669977147 3028372479185111504965721)
              ·
                refine ⟨2271279359388833628724291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3028372479185111504965721 2271279359388833628724291)
                ·
                  refine ⟨3406919039083250443086437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2271279359388833628724291 3406919039083250443086437)
                  ·
                    refine ⟨638797319828109458078707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3406919039083250443086437 638797319828109458078707)
                    ·
                      rfl

theorem cell22_1866080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 1, 4].length) (baseStart_1866080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866080 prefixEnd_1866080 := by exact prefixLift 1866080
  have htrace : WordTrace (prefixWord ++ tailWord_1866080) baseStart_1866080 baseEnd_1866080 := by
    simpa [prefixWord, tailWord_1866080, baseEnd_1866080] using wordTrace_append hprefix tailTrace_1866080
  have hstable : (prefixWord ++ tailWord_1866080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866080).length < 2 ^ (prefixWord ++ tailWord_1866080).sum := by decide
  have hdescent : baseEnd_1866080 < baseStart_1866080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866089 : List Nat := [1, 2, 1, 1, 1, 3, 3, 10]
def baseStart_1866089 : Nat := 118140960795 + 1866089 * 2 ^ 59
def prefixEnd_1866089 : Nat := 4983230072969 + 3 ^ 40 * 1866089 * 2
def baseEnd_1866089 : Nat := 70977822301337381622631

theorem tailTrace_1866089 : CollatzResearch.WordTrace tailWord_1866089 prefixEnd_1866089 70977822301337381622631 := by
  unfold tailWord_1866089
  simp only [CollatzResearch.WordTrace]
  refine ⟨68061857336485730473097321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45374571557657153648731547 68061857336485730473097321)
  ·
    refine ⟨51046393002364297854822991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68061857336485730473097321 51046393002364297854822991)
    ·
      refine ⟨76569589503546446782234487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51046393002364297854822991 76569589503546446782234487)
      ·
        refine ⟨114854384255319670173351731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76569589503546446782234487 114854384255319670173351731)
        ·
          refine ⟨172281576382979505260027597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114854384255319670173351731 172281576382979505260027597)
          ·
            refine ⟨64605591143617314472510349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172281576382979505260027597 64605591143617314472510349)
            ·
              refine ⟨24227096678856492927191381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64605591143617314472510349 24227096678856492927191381)
              ·
                refine ⟨70977822301337381622631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24227096678856492927191381 70977822301337381622631)
                ·
                  rfl

theorem cell22_1866089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 10].length) (baseStart_1866089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866089 prefixEnd_1866089 := by exact prefixLift 1866089
  have htrace : WordTrace (prefixWord ++ tailWord_1866089) baseStart_1866089 baseEnd_1866089 := by
    simpa [prefixWord, tailWord_1866089, baseEnd_1866089] using wordTrace_append hprefix tailTrace_1866089
  have hstable : (prefixWord ++ tailWord_1866089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866089).length < 2 ^ (prefixWord ++ tailWord_1866089).sum := by decide
  have hdescent : baseEnd_1866089 < baseStart_1866089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866138 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 5, 3]
def baseStart_1866138 : Nat := 118140960795 + 1866138 * 2 ^ 59
def prefixEnd_1866138 : Nat := 4983230072969 + 3 ^ 40 * 1866138 * 2
def baseEnd_1866138 : Nat := 638817174413416640128529

theorem tailTrace_1866138 : CollatzResearch.WordTrace tailWord_1866138 prefixEnd_1866138 638817174413416640128529 := by
  unfold tailWord_1866138
  simp only [CollatzResearch.WordTrace]
  refine ⟨17015911128327052960407767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45375763008872141227754045 17015911128327052960407767)
  ·
    refine ⟨25523866692490579440611651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17015911128327052960407767 25523866692490579440611651)
    ·
      refine ⟨38285800038735869160917477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25523866692490579440611651 38285800038735869160917477)
      ·
        refine ⟨7178587507262975467672027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38285800038735869160917477 7178587507262975467672027)
        ·
          refine ⟨10767881260894463201508041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7178587507262975467672027 10767881260894463201508041)
          ·
            refine ⟨8075910945670847401131031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10767881260894463201508041 8075910945670847401131031)
            ·
              refine ⟨12113866418506271101696547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8075910945670847401131031 12113866418506271101696547)
              ·
                refine ⟨18170799627759406652544821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12113866418506271101696547 18170799627759406652544821)
                ·
                  refine ⟨1703512465102444373676077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18170799627759406652544821 1703512465102444373676077)
                  ·
                    refine ⟨638817174413416640128529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1703512465102444373676077 638817174413416640128529)
                    ·
                      rfl

theorem cell22_1866138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_1866138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866138 prefixEnd_1866138 := by exact prefixLift 1866138
  have htrace : WordTrace (prefixWord ++ tailWord_1866138) baseStart_1866138 baseEnd_1866138 := by
    simpa [prefixWord, tailWord_1866138, baseEnd_1866138] using wordTrace_append hprefix tailTrace_1866138
  have hstable : (prefixWord ++ tailWord_1866138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866138).length < 2 ^ (prefixWord ++ tailWord_1866138).sum := by decide
  have hdescent : baseEnd_1866138 < baseStart_1866138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866142 : List Nat := [4, 3, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_1866142 : Nat := 118140960795 + 1866142 * 2 ^ 59
def prefixEnd_1866142 : Nat := 4983230072969 + 3 ^ 40 * 1866142 * 2
def baseEnd_1866142 : Nat := 638818543695161963028517

theorem tailTrace_1866142 : CollatzResearch.WordTrace tailWord_1866142 prefixEnd_1866142 638818543695161963028517 := by
  unfold tailWord_1866142
  simp only [CollatzResearch.WordTrace]
  refine ⟨8507973800661715065597085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45375860270195813683184453 8507973800661715065597085)
  ·
    refine ⟨3190490175248143149598907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8507973800661715065597085 3190490175248143149598907)
    ·
      refine ⟨4785735262872214724398361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3190490175248143149598907 4785735262872214724398361)
      ·
        refine ⟨3589301447154161043298771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4785735262872214724398361 3589301447154161043298771)
        ·
          refine ⟨5383952170731241564948157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3589301447154161043298771 5383952170731241564948157)
          ·
            refine ⟨2018982064024215586855559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5383952170731241564948157 2018982064024215586855559)
            ·
              refine ⟨3028473096036323380283339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2018982064024215586855559 3028473096036323380283339)
              ·
                refine ⟨4542709644054485070425009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3028473096036323380283339 4542709644054485070425009)
                ·
                  refine ⟨3407032233040863802818757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4542709644054485070425009 3407032233040863802818757)
                  ·
                    refine ⟨638818543695161963028517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3407032233040863802818757 638818543695161963028517)
                    ·
                      rfl

theorem cell22_1866142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_1866142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866142 prefixEnd_1866142 := by exact prefixLift 1866142
  have htrace : WordTrace (prefixWord ++ tailWord_1866142) baseStart_1866142 baseEnd_1866142 := by
    simpa [prefixWord, tailWord_1866142, baseEnd_1866142] using wordTrace_append hprefix tailTrace_1866142
  have hstable : (prefixWord ++ tailWord_1866142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866142).length < 2 ^ (prefixWord ++ tailWord_1866142).sum := by decide
  have hdescent : baseEnd_1866142 < baseStart_1866142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866172 : List Nat := [2, 2, 2, 4, 1, 1, 2, 4, 1, 3]
def baseStart_1866172 : Nat := 118140960795 + 1866172 * 2 ^ 59
def prefixEnd_1866172 : Nat := 4983230072969 + 3 ^ 40 * 1866172 * 2
def baseEnd_1866172 : Nat := 638828813308251884778425

theorem tailTrace_1866172 : CollatzResearch.WordTrace tailWord_1866172 prefixEnd_1866172 638828813308251884778425 := by
  unfold tailWord_1866172
  simp only [CollatzResearch.WordTrace]
  refine ⟨34032442297592517824184385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45376589730123357098912513 34032442297592517824184385)
  ·
    refine ⟨25524331723194388368138289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34032442297592517824184385 25524331723194388368138289)
    ·
      refine ⟨19143248792395791276103717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25524331723194388368138289 19143248792395791276103717)
      ·
        refine ⟨3589359148574210864269447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19143248792395791276103717 3589359148574210864269447)
        ·
          refine ⟨5384038722861316296404171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3589359148574210864269447 5384038722861316296404171)
          ·
            refine ⟨8076058084291974444606257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5384038722861316296404171 8076058084291974444606257)
            ·
              refine ⟨6057043563218980833454693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8076058084291974444606257 6057043563218980833454693)
              ·
                refine ⟨1135695668103558906272755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6057043563218980833454693 1135695668103558906272755)
                ·
                  refine ⟨1703543502155338359409133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1135695668103558906272755 1703543502155338359409133)
                  ·
                    refine ⟨638828813308251884778425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1703543502155338359409133 638828813308251884778425)
                    ·
                      rfl

theorem cell22_1866172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_1866172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866172 prefixEnd_1866172 := by exact prefixLift 1866172
  have htrace : WordTrace (prefixWord ++ tailWord_1866172) baseStart_1866172 baseEnd_1866172 := by
    simpa [prefixWord, tailWord_1866172, baseEnd_1866172] using wordTrace_append hprefix tailTrace_1866172
  have hstable : (prefixWord ++ tailWord_1866172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866172).length < 2 ^ (prefixWord ++ tailWord_1866172).sum := by decide
  have hdescent : baseEnd_1866172 < baseStart_1866172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866303 : List Nat := [1, 1, 2, 2, 3, 2, 1, 5, 5]
def baseStart_1866303 : Nat := 118140960795 + 1866303 * 2 ^ 59
def prefixEnd_1866303 : Nat := 4983230072969 + 3 ^ 40 * 1866303 * 2
def baseEnd_1866303 : Nat := 212957885761803736584341

theorem tailTrace_1866303 : CollatzResearch.WordTrace tailWord_1866303 prefixEnd_1866303 212957885761803736584341 := by
  unfold tailWord_1866303
  simp only [CollatzResearch.WordTrace]
  refine ⟨68069662557710445021387563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45379775038473630014258375 68069662557710445021387563)
  ·
    refine ⟨102104493836565667532081345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68069662557710445021387563 102104493836565667532081345)
    ·
      refine ⟨76578370377424250649061009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102104493836565667532081345 76578370377424250649061009)
      ·
        refine ⟨57433777783068187986795757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76578370377424250649061009 57433777783068187986795757)
        ·
          refine ⟨21537666668650570495048409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57433777783068187986795757 21537666668650570495048409)
          ·
            refine ⟨16153250001487927871286307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21537666668650570495048409 16153250001487927871286307)
            ·
              refine ⟨24229875002231891806929461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16153250001487927871286307 24229875002231891806929461)
              ·
                refine ⟨2271550781459239856899637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24229875002231891806929461 2271550781459239856899637)
                ·
                  refine ⟨212957885761803736584341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2271550781459239856899637 212957885761803736584341)
                  ·
                    rfl

theorem cell22_1866303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 5].length) (baseStart_1866303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866303 prefixEnd_1866303 := by exact prefixLift 1866303
  have htrace : WordTrace (prefixWord ++ tailWord_1866303) baseStart_1866303 baseEnd_1866303 := by
    simpa [prefixWord, tailWord_1866303, baseEnd_1866303] using wordTrace_append hprefix tailTrace_1866303
  have hstable : (prefixWord ++ tailWord_1866303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866303).length < 2 ^ (prefixWord ++ tailWord_1866303).sum := by decide
  have hdescent : baseEnd_1866303 < baseStart_1866303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866324 : List Nat := [2, 4, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_1866324 : Nat := 118140960795 + 1866324 * 2 ^ 59
def prefixEnd_1866324 : Nat := 4983230072969 + 3 ^ 40 * 1866324 * 2
def baseEnd_1866324 : Nat := 638880846014574154977959

theorem tailTrace_1866324 : CollatzResearch.WordTrace tailWord_1866324 prefixEnd_1866324 638880846014574154977959 := by
  unfold tailWord_1866324
  simp only [CollatzResearch.WordTrace]
  refine ⟨34035214245317182803951013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45380285660422910405268017 34035214245317182803951013)
  ·
    refine ⟨6381602670996971775740815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34035214245317182803951013 6381602670996971775740815)
    ·
      refine ⟨9572404006495457663611223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6381602670996971775740815 9572404006495457663611223)
      ·
        refine ⟨14358606009743186495416835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9572404006495457663611223 14358606009743186495416835)
        ·
          refine ⟨21537909014614779743125253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14358606009743186495416835 21537909014614779743125253)
          ·
            refine ⟨4038357940240271201835985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21537909014614779743125253 4038357940240271201835985)
            ·
              refine ⟨3028768455180203401376989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4038357940240271201835985 3028768455180203401376989)
              ·
                refine ⟨1135788170692576275516371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3028768455180203401376989 1135788170692576275516371)
                ·
                  refine ⟨1703682256038864413274557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1135788170692576275516371 1703682256038864413274557)
                  ·
                    refine ⟨638880846014574154977959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1703682256038864413274557 638880846014574154977959)
                    ·
                      rfl

theorem cell22_1866324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_1866324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866324 prefixEnd_1866324 := by exact prefixLift 1866324
  have htrace : WordTrace (prefixWord ++ tailWord_1866324) baseStart_1866324 baseEnd_1866324 := by
    simpa [prefixWord, tailWord_1866324, baseEnd_1866324] using wordTrace_append hprefix tailTrace_1866324
  have hstable : (prefixWord ++ tailWord_1866324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866324).length < 2 ^ (prefixWord ++ tailWord_1866324).sum := by decide
  have hdescent : baseEnd_1866324 < baseStart_1866324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866348 : List Nat := [2, 2, 1, 1, 3, 1, 3, 3, 6]
def baseStart_1866348 : Nat := 118140960795 + 1866348 * 2 ^ 59
def prefixEnd_1866348 : Nat := 4983230072969 + 3 ^ 40 * 1866348 * 2
def baseEnd_1866348 : Nat := 212963020568348697459295

theorem tailTrace_1866348 : CollatzResearch.WordTrace tailWord_1866348 prefixEnd_1866348 212963020568348697459295 := by
  unfold tailWord_1866348
  simp only [CollatzResearch.WordTrace]
  refine ⟨34035651921273708853387849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45380869228364945137850465 34035651921273708853387849)
  ·
    refine ⟨25526738940955281640040887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34035651921273708853387849 25526738940955281640040887)
    ·
      refine ⟨38290108411432922460061331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25526738940955281640040887 38290108411432922460061331)
      ·
        refine ⟨57435162617149383690091997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38290108411432922460061331 57435162617149383690091997)
        ·
          refine ⟨21538185981431018883784499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57435162617149383690091997 21538185981431018883784499)
          ·
            refine ⟨32307278972146528325676749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21538185981431018883784499 32307278972146528325676749)
            ·
              refine ⟨12115229614554948122128781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32307278972146528325676749 12115229614554948122128781)
              ·
                refine ⟨4543211105458105545798293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12115229614554948122128781 4543211105458105545798293)
                ·
                  refine ⟨212963020568348697459295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4543211105458105545798293 212963020568348697459295)
                  ·
                    rfl

theorem cell22_1866348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_1866348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866348 prefixEnd_1866348 := by exact prefixLift 1866348
  have htrace : WordTrace (prefixWord ++ tailWord_1866348) baseStart_1866348 baseEnd_1866348 := by
    simpa [prefixWord, tailWord_1866348, baseEnd_1866348] using wordTrace_append hprefix tailTrace_1866348
  have hstable : (prefixWord ++ tailWord_1866348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866348).length < 2 ^ (prefixWord ++ tailWord_1866348).sum := by decide
  have hdescent : baseEnd_1866348 < baseStart_1866348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866363 : List Nat := [1, 1, 1, 1, 1, 4, 2, 5, 1, 5]
def baseStart_1866363 : Nat := 118140960795 + 1866363 * 2 ^ 59
def prefixEnd_1866363 : Nat := 4983230072969 + 3 ^ 40 * 1866363 * 2
def baseEnd_1866363 : Nat := 638894196511591053252839

theorem tailTrace_1866363 : CollatzResearch.WordTrace tailWord_1866363 prefixEnd_1866363 638894196511591053252839 := by
  unfold tailWord_1866363
  simp only [CollatzResearch.WordTrace]
  refine ⟨68071850937493075268571743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45381233958328716845714495 68071850937493075268571743)
  ·
    refine ⟨102107776406239612902857615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68071850937493075268571743 102107776406239612902857615)
    ·
      refine ⟨153161664609359419354286423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102107776406239612902857615 153161664609359419354286423)
      ·
        refine ⟨229742496914039129031429635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153161664609359419354286423 229742496914039129031429635)
        ·
          refine ⟨344613745371058693547144453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229742496914039129031429635 344613745371058693547144453)
          ·
            refine ⟨64615077257073505040089585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 344613745371058693547144453 64615077257073505040089585)
            ·
              refine ⟨48461307942805128780067189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64615077257073505040089585 48461307942805128780067189)
              ·
                refine ⟨4543247619637980823131299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48461307942805128780067189 4543247619637980823131299)
                ·
                  refine ⟨6814871429456971234696949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4543247619637980823131299 6814871429456971234696949)
                  ·
                    refine ⟨638894196511591053252839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6814871429456971234696949 638894196511591053252839)
                    ·
                      rfl

theorem cell22_1866363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 5].length) (baseStart_1866363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866363 prefixEnd_1866363 := by exact prefixLift 1866363
  have htrace : WordTrace (prefixWord ++ tailWord_1866363) baseStart_1866363 baseEnd_1866363 := by
    simpa [prefixWord, tailWord_1866363, baseEnd_1866363] using wordTrace_append hprefix tailTrace_1866363
  have hstable : (prefixWord ++ tailWord_1866363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866363).length < 2 ^ (prefixWord ++ tailWord_1866363).sum := by decide
  have hdescent : baseEnd_1866363 < baseStart_1866363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866425 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 5, 3]
def baseStart_1866425 : Nat := 118140960795 + 1866425 * 2 ^ 59
def prefixEnd_1866425 : Nat := 4983230072969 + 3 ^ 40 * 1866425 * 2
def baseEnd_1866425 : Nat := 638915420378643558202649

theorem tailTrace_1866425 : CollatzResearch.WordTrace tailWord_1866425 prefixEnd_1866425 638915420378643558202649 := by
  unfold tailWord_1866425
  simp only [CollatzResearch.WordTrace]
  refine ⟨68074112263268459857328729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45382741508845639904885819 68074112263268459857328729)
  ·
    refine ⟨51055584197451344892996547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68074112263268459857328729 51055584197451344892996547)
    ·
      refine ⟨76583376296177017339494821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51055584197451344892996547 76583376296177017339494821)
      ·
        refine ⟨14359383055533190751155279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76583376296177017339494821 14359383055533190751155279)
        ·
          refine ⟨21539074583299786126732919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14359383055533190751155279 21539074583299786126732919)
          ·
            refine ⟨32308611874949679190099379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21539074583299786126732919 32308611874949679190099379)
            ·
              refine ⟨48462917812424518785149069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32308611874949679190099379 48462917812424518785149069)
              ·
                refine ⟨18173594179659194544430901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48462917812424518785149069 18173594179659194544430901)
                ·
                  refine ⟨1703774454343049488540397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18173594179659194544430901 1703774454343049488540397)
                  ·
                    refine ⟨638915420378643558202649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1703774454343049488540397 638915420378643558202649)
                    ·
                      rfl

theorem cell22_1866425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 3].length) (baseStart_1866425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866425 prefixEnd_1866425 := by exact prefixLift 1866425
  have htrace : WordTrace (prefixWord ++ tailWord_1866425) baseStart_1866425 baseEnd_1866425 := by
    simpa [prefixWord, tailWord_1866425, baseEnd_1866425] using wordTrace_append hprefix tailTrace_1866425
  have hstable : (prefixWord ++ tailWord_1866425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866425).length < 2 ^ (prefixWord ++ tailWord_1866425).sum := by decide
  have hdescent : baseEnd_1866425 < baseStart_1866425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866455 : List Nat := [1, 1, 3, 2, 1, 4, 1, 4, 5]
def baseStart_1866455 : Nat := 118140960795 + 1866455 * 2 ^ 59
def prefixEnd_1866455 : Nat := 4983230072969 + 3 ^ 40 * 1866455 * 2
def baseEnd_1866455 : Nat := 212975229997244493317519

theorem tailTrace_1866455 : CollatzResearch.WordTrace tailWord_1866455 prefixEnd_1866455 212975229997244493317519 := by
  unfold tailWord_1866455
  simp only [CollatzResearch.WordTrace]
  refine ⟨68075206453159774980920819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45383470968773183320613879 68075206453159774980920819)
  ·
    refine ⟨102112809679739662471381229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68075206453159774980920819 102112809679739662471381229)
    ·
      refine ⟨38292303629902373426767961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102112809679739662471381229 38292303629902373426767961)
      ·
        refine ⟨28719227722426780070075971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38292303629902373426767961 28719227722426780070075971)
        ·
          refine ⟨43078841583640170105113957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28719227722426780070075971 43078841583640170105113957)
          ·
            refine ⟨8077282796932531894708867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43078841583640170105113957 8077282796932531894708867)
            ·
              refine ⟨12115924195398797842063301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8077282796932531894708867 12115924195398797842063301)
              ·
                refine ⟨2271735786637274595386869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12115924195398797842063301 2271735786637274595386869)
                ·
                  refine ⟨212975229997244493317519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2271735786637274595386869 212975229997244493317519)
                  ·
                    rfl

theorem cell22_1866455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 5].length) (baseStart_1866455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866455 prefixEnd_1866455 := by exact prefixLift 1866455
  have htrace : WordTrace (prefixWord ++ tailWord_1866455) baseStart_1866455 baseEnd_1866455 := by
    simpa [prefixWord, tailWord_1866455, baseEnd_1866455] using wordTrace_append hprefix tailTrace_1866455
  have hstable : (prefixWord ++ tailWord_1866455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866455).length < 2 ^ (prefixWord ++ tailWord_1866455).sum := by decide
  have hdescent : baseEnd_1866455 < baseStart_1866455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866500 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 8]
def baseStart_1866500 : Nat := 118140960795 + 1866500 * 2 ^ 59
def prefixEnd_1866500 : Nat := 4983230072969 + 3 ^ 40 * 1866500 * 2
def baseEnd_1866500 : Nat := 212980364803789454192473

theorem tailTrace_1866500 : CollatzResearch.WordTrace tailWord_1866500 prefixEnd_1866500 212980364803789454192473 := by
  unfold tailWord_1866500
  simp only [CollatzResearch.WordTrace]
  refine ⟨34038423868998373833154477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45384565158664498444205969 34038423868998373833154477)
  ·
    refine ⟨12764408950874390187432929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34038423868998373833154477 12764408950874390187432929)
    ·
      refine ⟨9573306713155792640574697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12764408950874390187432929 9573306713155792640574697)
      ·
        refine ⟨7179980034866844480431023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9573306713155792640574697 7179980034866844480431023)
        ·
          refine ⟨10769970052300266720646535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7179980034866844480431023 10769970052300266720646535)
          ·
            refine ⟨16154955078450400080969803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10769970052300266720646535 16154955078450400080969803)
            ·
              refine ⟨24232432617675600121454705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16154955078450400080969803 24232432617675600121454705)
              ·
                refine ⟨18174324463256700091091029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24232432617675600121454705 18174324463256700091091029)
                ·
                  refine ⟨212980364803789454192473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18174324463256700091091029 212980364803789454192473)
                  ·
                    rfl

theorem cell22_1866500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_1866500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866500 prefixEnd_1866500 := by exact prefixLift 1866500
  have htrace : WordTrace (prefixWord ++ tailWord_1866500) baseStart_1866500 baseEnd_1866500 := by
    simpa [prefixWord, tailWord_1866500, baseEnd_1866500] using wordTrace_append hprefix tailTrace_1866500
  have hstable : (prefixWord ++ tailWord_1866500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866500).length < 2 ^ (prefixWord ++ tailWord_1866500).sum := by decide
  have hdescent : baseEnd_1866500 < baseStart_1866500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866517 : List Nat := [1, 3, 2, 1, 2, 2, 1, 6, 4]
def baseStart_1866517 : Nat := 118140960795 + 1866517 * 2 ^ 59
def prefixEnd_1866517 : Nat := 4983230072969 + 3 ^ 40 * 1866517 * 2
def baseEnd_1866517 : Nat := 212982304619595328300789

theorem tailTrace_1866517 : CollatzResearch.WordTrace tailWord_1866517 prefixEnd_1866517 212982304619595328300789 := by
  unfold tailWord_1866517
  simp only [CollatzResearch.WordTrace]
  refine ⟨68077467778935159569677805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45384978519290106379785203 68077467778935159569677805)
  ·
    refine ⟨25529050417100684838629177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68077467778935159569677805 25529050417100684838629177)
    ·
      refine ⟨19146787812825513628971883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25529050417100684838629177 19146787812825513628971883)
      ·
        refine ⟨28720181719238270443457825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19146787812825513628971883 28720181719238270443457825)
        ·
          refine ⟨21540136289428702832593369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28720181719238270443457825 21540136289428702832593369)
          ·
            refine ⟨16155102217071527124445027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21540136289428702832593369 16155102217071527124445027)
            ·
              refine ⟨24232653325607290686667541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16155102217071527124445027 24232653325607290686667541)
              ·
                refine ⟨1135905624637841750937541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24232653325607290686667541 1135905624637841750937541)
                ·
                  refine ⟨212982304619595328300789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1135905624637841750937541 212982304619595328300789)
                  ·
                    rfl

theorem cell22_1866517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_1866517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866517 prefixEnd_1866517 := by exact prefixLift 1866517
  have htrace : WordTrace (prefixWord ++ tailWord_1866517) baseStart_1866517 baseEnd_1866517 := by
    simpa [prefixWord, tailWord_1866517, baseEnd_1866517] using wordTrace_append hprefix tailTrace_1866517
  have hstable : (prefixWord ++ tailWord_1866517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866517).length < 2 ^ (prefixWord ++ tailWord_1866517).sum := by decide
  have hdescent : baseEnd_1866517 < baseStart_1866517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866545 : List Nat := [1, 2, 2, 3, 2, 1, 3, 8]
def baseStart_1866545 : Nat := 118140960795 + 1866545 * 2 ^ 59
def prefixEnd_1866545 : Nat := 4983230072969 + 3 ^ 40 * 1866545 * 2
def baseEnd_1866545 : Nat := 70995166536778138355809

theorem tailTrace_1866545 : CollatzResearch.WordTrace tailWord_1866545 prefixEnd_1866545 70995166536778138355809 := by
  unfold tailWord_1866545
  simp only [CollatzResearch.WordTrace]
  refine ⟨68078489022833720351697089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45385659348555813567798059 68078489022833720351697089)
  ·
    refine ⟨51058866767125290263772817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68078489022833720351697089 51058866767125290263772817)
    ·
      refine ⟨38294150075343967697829613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51058866767125290263772817 38294150075343967697829613)
      ·
        refine ⟨14360306278253987886686105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38294150075343967697829613 14360306278253987886686105)
        ·
          refine ⟨10770229708690490915014579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14360306278253987886686105 10770229708690490915014579)
          ·
            refine ⟨16155344563035736372521869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10770229708690490915014579 16155344563035736372521869)
            ·
              refine ⟨6058254211138401139695701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16155344563035736372521869 6058254211138401139695701)
              ·
                refine ⟨70995166536778138355809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6058254211138401139695701 70995166536778138355809)
                ·
                  rfl

theorem cell22_1866545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 8].length) (baseStart_1866545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866545 prefixEnd_1866545 := by exact prefixLift 1866545
  have htrace : WordTrace (prefixWord ++ tailWord_1866545) baseStart_1866545 baseEnd_1866545 := by
    simpa [prefixWord, tailWord_1866545, baseEnd_1866545] using wordTrace_append hprefix tailTrace_1866545
  have hstable : (prefixWord ++ tailWord_1866545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866545).length < 2 ^ (prefixWord ++ tailWord_1866545).sum := by decide
  have hdescent : baseEnd_1866545 < baseStart_1866545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866667 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 6, 3]
def baseStart_1866667 : Nat := 118140960795 + 1866667 * 2 ^ 59
def prefixEnd_1866667 : Nat := 4983230072969 + 3 ^ 40 * 1866667 * 2
def baseEnd_1866667 : Nat := 638998261924235593651907

theorem tailTrace_1866667 : CollatzResearch.WordTrace tailWord_1866667 prefixEnd_1866667 638998261924235593651907 := by
  unfold tailWord_1866667
  simp only [CollatzResearch.WordTrace]
  refine ⟨68082938728391735187638255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45388625818927823458425503 68082938728391735187638255)
  ·
    refine ⟨102124408092587602781457383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68082938728391735187638255 102124408092587602781457383)
    ·
      refine ⟨153186612138881404172186075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102124408092587602781457383 153186612138881404172186075)
      ·
        refine ⟨229779918208322106258279113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153186612138881404172186075 229779918208322106258279113)
        ·
          refine ⟨172334938656241579693709335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229779918208322106258279113 172334938656241579693709335)
          ·
            refine ⟨258502407984362369540564003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172334938656241579693709335 258502407984362369540564003)
            ·
              refine ⟨387753611976543554310846005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258502407984362369540564003 387753611976543554310846005)
              ·
                refine ⟨36351901122800958216641813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 387753611976543554310846005 36351901122800958216641813)
                ·
                  refine ⟨1703995365131294916405085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36351901122800958216641813 1703995365131294916405085)
                  ·
                    refine ⟨638998261924235593651907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1703995365131294916405085 638998261924235593651907)
                    ·
                      rfl

theorem cell22_1866667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 3].length) (baseStart_1866667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866667 prefixEnd_1866667 := by exact prefixLift 1866667
  have htrace : WordTrace (prefixWord ++ tailWord_1866667) baseStart_1866667 baseEnd_1866667 := by
    simpa [prefixWord, tailWord_1866667, baseEnd_1866667] using wordTrace_append hprefix tailTrace_1866667
  have hstable : (prefixWord ++ tailWord_1866667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866667).length < 2 ^ (prefixWord ++ tailWord_1866667).sum := by decide
  have hdescent : baseEnd_1866667 < baseStart_1866667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866682 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 4, 4]
def baseStart_1866682 : Nat := 118140960795 + 1866682 * 2 ^ 59
def prefixEnd_1866682 : Nat := 4983230072969 + 3 ^ 40 * 1866682 * 2
def baseEnd_1866682 : Nat := 639003396730780554526861

theorem tailTrace_1866682 : CollatzResearch.WordTrace tailWord_1866682 prefixEnd_1866682 639003396730780554526861 := by
  unfold tailWord_1866682
  simp only [CollatzResearch.WordTrace]
  refine ⟨17020871455834348187358575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45388990548891595166289533 17020871455834348187358575)
  ·
    refine ⟨25531307183751522281037863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17020871455834348187358575 25531307183751522281037863)
    ·
      refine ⟨38296960775627283421556795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25531307183751522281037863 38296960775627283421556795)
      ·
        refine ⟨57445441163440925132335193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38296960775627283421556795 57445441163440925132335193)
        ·
          refine ⟨43084080872580693849251395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57445441163440925132335193 43084080872580693849251395)
          ·
            refine ⟨64626121308871040773877093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43084080872580693849251395 64626121308871040773877093)
            ·
              refine ⟨12117397745413320145101955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64626121308871040773877093 12117397745413320145101955)
              ·
                refine ⟨18176096618119980217652933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12117397745413320145101955 18176096618119980217652933)
                ·
                  refine ⟨3408018115897496290809925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18176096618119980217652933 3408018115897496290809925)
                  ·
                    refine ⟨639003396730780554526861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3408018115897496290809925 639003396730780554526861)
                    ·
                      rfl

theorem cell22_1866682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_1866682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866682 prefixEnd_1866682 := by exact prefixLift 1866682
  have htrace : WordTrace (prefixWord ++ tailWord_1866682) baseStart_1866682 baseEnd_1866682 := by
    simpa [prefixWord, tailWord_1866682, baseEnd_1866682] using wordTrace_append hprefix tailTrace_1866682
  have hstable : (prefixWord ++ tailWord_1866682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866682).length < 2 ^ (prefixWord ++ tailWord_1866682).sum := by decide
  have hdescent : baseEnd_1866682 < baseStart_1866682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866714 : List Nat := [3, 1, 1, 2, 4, 1, 4, 6]
def baseStart_1866714 : Nat := 118140960795 + 1866714 * 2 ^ 59
def prefixEnd_1866714 : Nat := 4983230072969 + 3 ^ 40 * 1866714 * 2
def baseEnd_1866714 : Nat := 71001594553860348636307

theorem tailTrace_1866714 : CollatzResearch.WordTrace tailWord_1866714 prefixEnd_1866714 71001594553860348636307 := by
  unfold tailWord_1866714
  simp only [CollatzResearch.WordTrace]
  refine ⟨17021163239805365553649799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45389768639480974809732797 17021163239805365553649799)
  ·
    refine ⟨25531744859708048330474699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17021163239805365553649799 25531744859708048330474699)
    ·
      refine ⟨38297617289562072495712049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25531744859708048330474699 38297617289562072495712049)
      ·
        refine ⟨28723212967171554371784037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38297617289562072495712049 28723212967171554371784037)
        ·
          refine ⟨5385602431344666444709507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28723212967171554371784037 5385602431344666444709507)
          ·
            refine ⟨8078403647016999667064261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5385602431344666444709507 8078403647016999667064261)
            ·
              refine ⟨1514700683815687437574549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8078403647016999667064261 1514700683815687437574549)
              ·
                refine ⟨71001594553860348636307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1514700683815687437574549 71001594553860348636307)
                ·
                  rfl

theorem cell22_1866714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 6].length) (baseStart_1866714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866714 prefixEnd_1866714 := by exact prefixLift 1866714
  have htrace : WordTrace (prefixWord ++ tailWord_1866714) baseStart_1866714 baseEnd_1866714 := by
    simpa [prefixWord, tailWord_1866714, baseEnd_1866714] using wordTrace_append hprefix tailTrace_1866714
  have hstable : (prefixWord ++ tailWord_1866714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866714).length < 2 ^ (prefixWord ++ tailWord_1866714).sum := by decide
  have hdescent : baseEnd_1866714 < baseStart_1866714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866746 : List Nat := [3, 1, 1, 1, 1, 2, 1, 8, 1, 3]
def baseStart_1866746 : Nat := 118140960795 + 1866746 * 2 ^ 59
def prefixEnd_1866746 : Nat := 4983230072969 + 3 ^ 40 * 1866746 * 2
def baseEnd_1866746 : Nat := 639025305238705720926665

theorem tailTrace_1866746 : CollatzResearch.WordTrace tailWord_1866746 prefixEnd_1866746 639025305238705720926665 := by
  unfold tailWord_1866746
  simp only [CollatzResearch.WordTrace]
  refine ⟨17021455023776382919941023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45390546730070354453176061 17021455023776382919941023)
  ·
    refine ⟨25532182535664574379911535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17021455023776382919941023 25532182535664574379911535)
    ·
      refine ⟨38298273803496861569867303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25532182535664574379911535 38298273803496861569867303)
      ·
        refine ⟨57447410705245292354800955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38298273803496861569867303 57447410705245292354800955)
        ·
          refine ⟨86171116057867938532201433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57447410705245292354800955 86171116057867938532201433)
          ·
            refine ⟨64628337043400953899151075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86171116057867938532201433 64628337043400953899151075)
            ·
              refine ⟨96942505565101430848726613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64628337043400953899151075 96942505565101430848726613)
              ·
                refine ⟨1136044987091032392758515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 96942505565101430848726613 1136044987091032392758515)
                ·
                  refine ⟨1704067480636548589137773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1136044987091032392758515 1704067480636548589137773)
                  ·
                    refine ⟨639025305238705720926665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1704067480636548589137773 639025305238705720926665)
                    ·
                      rfl

theorem cell22_1866746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 1, 3].length) (baseStart_1866746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866746 prefixEnd_1866746 := by exact prefixLift 1866746
  have htrace : WordTrace (prefixWord ++ tailWord_1866746) baseStart_1866746 baseEnd_1866746 := by
    simpa [prefixWord, tailWord_1866746, baseEnd_1866746] using wordTrace_append hprefix tailTrace_1866746
  have hstable : (prefixWord ++ tailWord_1866746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866746).length < 2 ^ (prefixWord ++ tailWord_1866746).sum := by decide
  have hdescent : baseEnd_1866746 < baseStart_1866746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866757 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 1, 7]
def baseStart_1866757 : Nat := 118140960795 + 1866757 * 2 ^ 59
def prefixEnd_1866757 : Nat := 4983230072969 + 3 ^ 40 * 1866757 * 2
def baseEnd_1866757 : Nat := 639029070763505358901631

theorem tailTrace_1866757 : CollatzResearch.WordTrace tailWord_1866757 prefixEnd_1866757 639029070763505358901631 := by
  unfold tailWord_1866757
  simp only [CollatzResearch.WordTrace]
  refine ⟨68086221298065680558414525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45390814198710453705609683 68086221298065680558414525)
  ·
    refine ⟨25532332986774630209405447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68086221298065680558414525 25532332986774630209405447)
    ·
      refine ⟨38298499480161945314108171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25532332986774630209405447 38298499480161945314108171)
      ·
        refine ⟨57447749220242917971162257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38298499480161945314108171 57447749220242917971162257)
        ·
          refine ⟨43085811915182188478371693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57447749220242917971162257 43085811915182188478371693)
          ·
            refine ⟨16157179468193320679389385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43085811915182188478371693 16157179468193320679389385)
            ·
              refine ⟨12117884601144990509542039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16157179468193320679389385 12117884601144990509542039)
              ·
                refine ⟨18176826901717485764313059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12117884601144990509542039 18176826901717485764313059)
                ·
                  refine ⟨27265240352576228646469589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18176826901717485764313059 27265240352576228646469589)
                  ·
                    refine ⟨639029070763505358901631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27265240352576228646469589 639029070763505358901631)
                    ·
                      rfl

theorem cell22_1866757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_1866757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866757 prefixEnd_1866757 := by exact prefixLift 1866757
  have htrace : WordTrace (prefixWord ++ tailWord_1866757) baseStart_1866757 baseEnd_1866757 := by
    simpa [prefixWord, tailWord_1866757, baseEnd_1866757] using wordTrace_append hprefix tailTrace_1866757
  have hstable : (prefixWord ++ tailWord_1866757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866757).length < 2 ^ (prefixWord ++ tailWord_1866757).sum := by decide
  have hdescent : baseEnd_1866757 < baseStart_1866757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866759 : List Nat := [1, 1, 4, 3, 1, 1, 3, 3, 5]
def baseStart_1866759 : Nat := 118140960795 + 1866759 * 2 ^ 59
def prefixEnd_1866759 : Nat := 4983230072969 + 3 ^ 40 * 1866759 * 2
def baseEnd_1866759 : Nat := 213009918468126006783875

theorem tailTrace_1866759 : CollatzResearch.WordTrace tailWord_1866759 prefixEnd_1866759 213009918468126006783875 := by
  unfold tailWord_1866759
  simp only [CollatzResearch.WordTrace]
  refine ⟨68086294244058434899987331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45390862829372289933324887 68086294244058434899987331)
  ·
    refine ⟨102129441366087652349980997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68086294244058434899987331 102129441366087652349980997)
    ·
      refine ⟨19149270256141434815621437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102129441366087652349980997 19149270256141434815621437)
      ·
        refine ⟨7180976346053038055858039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19149270256141434815621437 7180976346053038055858039)
        ·
          refine ⟨10771464519079557083787059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7180976346053038055858039 10771464519079557083787059)
          ·
            refine ⟨16157196778619335625680589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10771464519079557083787059 16157196778619335625680589)
            ·
              refine ⟨6058948791982250859630221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16157196778619335625680589 6058948791982250859630221)
              ·
                refine ⟨2272105796993344072361333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6058948791982250859630221 2272105796993344072361333)
                ·
                  refine ⟨213009918468126006783875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2272105796993344072361333 213009918468126006783875)
                  ·
                    rfl

theorem cell22_1866759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 5].length) (baseStart_1866759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866759 prefixEnd_1866759 := by exact prefixLift 1866759
  have htrace : WordTrace (prefixWord ++ tailWord_1866759) baseStart_1866759 baseEnd_1866759 := by
    simpa [prefixWord, tailWord_1866759, baseEnd_1866759] using wordTrace_append hprefix tailTrace_1866759
  have hstable : (prefixWord ++ tailWord_1866759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866759).length < 2 ^ (prefixWord ++ tailWord_1866759).sum := by decide
  have hdescent : baseEnd_1866759 < baseStart_1866759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866806 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_1866806 : Nat := 118140960795 + 1866806 * 2 ^ 59
def prefixEnd_1866806 : Nat := 4983230072969 + 3 ^ 40 * 1866806 * 2
def baseEnd_1866806 : Nat := 639045844464885564426481

theorem tailTrace_1866806 : CollatzResearch.WordTrace tailWord_1866806 prefixEnd_1866806 639045844464885564426481 := by
  unfold tailWord_1866806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4255500529680510120434267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45392005649925441284632181 4255500529680510120434267)
  ·
    refine ⟨6383250794520765180651401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4255500529680510120434267 6383250794520765180651401)
    ·
      refine ⟨4787438095890573885488551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6383250794520765180651401 4787438095890573885488551)
      ·
        refine ⟨7181157143835860828232827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4787438095890573885488551 7181157143835860828232827)
        ·
          refine ⟨10771735715753791242349241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7181157143835860828232827 10771735715753791242349241)
          ·
            refine ⟨8078801786815343431761931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10771735715753791242349241 8078801786815343431761931)
            ·
              refine ⟨12118202680223015147642897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8078801786815343431761931 12118202680223015147642897)
              ·
                refine ⟨9088652010167261360732173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12118202680223015147642897 9088652010167261360732173)
                ·
                  refine ⟨3408244503812723010274565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9088652010167261360732173 3408244503812723010274565)
                  ·
                    refine ⟨639045844464885564426481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3408244503812723010274565 639045844464885564426481)
                    ·
                      rfl

theorem cell22_1866806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_1866806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866806 prefixEnd_1866806 := by exact prefixLift 1866806
  have htrace : WordTrace (prefixWord ++ tailWord_1866806) baseStart_1866806 baseEnd_1866806 := by
    simpa [prefixWord, tailWord_1866806, baseEnd_1866806] using wordTrace_append hprefix tailTrace_1866806
  have hstable : (prefixWord ++ tailWord_1866806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866806).length < 2 ^ (prefixWord ++ tailWord_1866806).sum := by decide
  have hdescent : baseEnd_1866806 < baseStart_1866806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866819 : List Nat := [1, 1, 1, 3, 1, 2, 6, 1, 1, 5]
def baseStart_1866819 : Nat := 118140960795 + 1866819 * 2 ^ 59
def prefixEnd_1866819 : Nat := 4983230072969 + 3 ^ 40 * 1866819 * 2
def baseEnd_1866819 : Nat := 639050294630557863851441

theorem tailTrace_1866819 : CollatzResearch.WordTrace tailWord_1866819 prefixEnd_1866819 639050294630557863851441 := by
  unfold tailWord_1866819
  simp only [CollatzResearch.WordTrace]
  refine ⟨68088482623841065147171511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45392321749227376764781007 68088482623841065147171511)
  ·
    refine ⟨102132723935761597720757267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68088482623841065147171511 102132723935761597720757267)
    ·
      refine ⟨153199085903642396581135901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102132723935761597720757267 153199085903642396581135901)
      ·
        refine ⟨57449657213865898717925963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153199085903642396581135901 57449657213865898717925963)
        ·
          refine ⟨86174485820798848076888945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57449657213865898717925963 86174485820798848076888945)
          ·
            refine ⟨64630864365599136057666709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86174485820798848076888945 64630864365599136057666709)
            ·
              refine ⟨3029571767137459502703127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64630864365599136057666709 3029571767137459502703127)
              ·
                refine ⟨4544357650706189254054691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3029571767137459502703127 4544357650706189254054691)
                ·
                  refine ⟨6816536476059283881082037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4544357650706189254054691 6816536476059283881082037)
                  ·
                    refine ⟨639050294630557863851441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6816536476059283881082037 639050294630557863851441)
                    ·
                      rfl

theorem cell22_1866819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 5].length) (baseStart_1866819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866819 prefixEnd_1866819 := by exact prefixLift 1866819
  have htrace : WordTrace (prefixWord ++ tailWord_1866819) baseStart_1866819 baseEnd_1866819 := by
    simpa [prefixWord, tailWord_1866819, baseEnd_1866819] using wordTrace_append hprefix tailTrace_1866819
  have hstable : (prefixWord ++ tailWord_1866819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866819).length < 2 ^ (prefixWord ++ tailWord_1866819).sum := by decide
  have hdescent : baseEnd_1866819 < baseStart_1866819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866832 : List Nat := [2, 1, 1, 1, 1, 3, 1, 12]
def baseStart_1866832 : Nat := 118140960795 + 1866832 * 2 ^ 59
def prefixEnd_1866832 : Nat := 4983230072969 + 3 ^ 40 * 1866832 * 2
def baseEnd_1866832 : Nat := 71006082755136684808489

theorem tailTrace_1866832 : CollatzResearch.WordTrace tailWord_1866832 prefixEnd_1866832 71006082755136684808489 := by
  unfold tailWord_1866832
  simp only [CollatzResearch.WordTrace]
  refine ⟨34044478386396984183697375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45392637848529312244929833 34044478386396984183697375)
  ·
    refine ⟨51066717579595476275546063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34044478386396984183697375 51066717579595476275546063)
    ·
      refine ⟨76600076369393214413319095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51066717579595476275546063 76600076369393214413319095)
      ·
        refine ⟨114900114554089821619978643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76600076369393214413319095 114900114554089821619978643)
        ·
          refine ⟨172350171831134732429967965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114900114554089821619978643 172350171831134732429967965)
          ·
            refine ⟨64631314436675524661237987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172350171831134732429967965 64631314436675524661237987)
            ·
              refine ⟨96946971655013286991856981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64631314436675524661237987 96946971655013286991856981)
              ·
                refine ⟨71006082755136684808489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 96946971655013286991856981 71006082755136684808489)
                ·
                  rfl

theorem cell22_1866832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 12].length) (baseStart_1866832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866832 prefixEnd_1866832 := by exact prefixLift 1866832
  have htrace : WordTrace (prefixWord ++ tailWord_1866832) baseStart_1866832 baseEnd_1866832 := by
    simpa [prefixWord, tailWord_1866832, baseEnd_1866832] using wordTrace_append hprefix tailTrace_1866832
  have hstable : (prefixWord ++ tailWord_1866832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866832).length < 2 ^ (prefixWord ++ tailWord_1866832).sum := by decide
  have hdescent : baseEnd_1866832 < baseStart_1866832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866870 : List Nat := [5, 1, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_1866870 : Nat := 118140960795 + 1866870 * 2 ^ 59
def prefixEnd_1866870 : Nat := 4983230072969 + 3 ^ 40 * 1866870 * 2
def baseEnd_1866870 : Nat := 639067752972810730826285

theorem tailTrace_1866870 : CollatzResearch.WordTrace tailWord_1866870 prefixEnd_1866870 639067752972810730826285 := by
  unfold tailWord_1866870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4255646421666018803579879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45393561831104200571518709 4255646421666018803579879)
  ·
    refine ⟨6383469632499028205369819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4255646421666018803579879 6383469632499028205369819)
    ·
      refine ⟨9575204448748542308054729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6383469632499028205369819 9575204448748542308054729)
      ·
        refine ⟨7181403336561406731041047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9575204448748542308054729 7181403336561406731041047)
        ·
          refine ⟨10772105004842110096561571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7181403336561406731041047 10772105004842110096561571)
          ·
            refine ⟨16158157507263165144842357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10772105004842110096561571 16158157507263165144842357)
            ·
              refine ⟨1514827266305921732328971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16158157507263165144842357 1514827266305921732328971)
              ·
                refine ⟨2272240899458882598493457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1514827266305921732328971 2272240899458882598493457)
                ·
                  refine ⟨1704180674594161948870093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2272240899458882598493457 1704180674594161948870093)
                  ·
                    refine ⟨639067752972810730826285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1704180674594161948870093 639067752972810730826285)
                    ·
                      rfl

theorem cell22_1866870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_1866870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866870 prefixEnd_1866870 := by exact prefixLift 1866870
  have htrace : WordTrace (prefixWord ++ tailWord_1866870) baseStart_1866870 baseEnd_1866870 := by
    simpa [prefixWord, tailWord_1866870, baseEnd_1866870] using wordTrace_append hprefix tailTrace_1866870
  have hstable : (prefixWord ++ tailWord_1866870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866870).length < 2 ^ (prefixWord ++ tailWord_1866870).sum := by decide
  have hdescent : baseEnd_1866870 < baseStart_1866870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866966 : List Nat := [5, 2, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_1866966 : Nat := 118140960795 + 1866966 * 2 ^ 59
def prefixEnd_1866966 : Nat := 4983230072969 + 3 ^ 40 * 1866966 * 2
def baseEnd_1866966 : Nat := 639100615734698480425991

theorem tailTrace_1866966 : CollatzResearch.WordTrace tailWord_1866966 prefixEnd_1866966 639100615734698480425991 := by
  unfold tailWord_1866966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4255865259644281828298297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45395896102872339501848501 4255865259644281828298297)
  ·
    refine ⟨3191898944733211371223723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4255865259644281828298297 3191898944733211371223723)
    ·
      refine ⟨4787848417099817056835585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3191898944733211371223723 4787848417099817056835585)
      ·
        refine ⟨3590886312824862792626689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4787848417099817056835585 3590886312824862792626689)
        ·
          refine ⟨2693164734618647094470017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3590886312824862792626689 2693164734618647094470017)
          ·
            refine ⟨2019873550963985320852513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2693164734618647094470017 2019873550963985320852513)
            ·
              refine ⟨1514905163222988990639385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2019873550963985320852513 1514905163222988990639385)
              ·
                refine ⟨1136178872417241742979539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1514905163222988990639385 1136178872417241742979539)
                ·
                  refine ⟨1704268308625862614469309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1136178872417241742979539 1704268308625862614469309)
                  ·
                    refine ⟨639100615734698480425991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1704268308625862614469309 639100615734698480425991)
                    ·
                      rfl

theorem cell22_1866966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_1866966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866966 prefixEnd_1866966 := by exact prefixLift 1866966
  have htrace : WordTrace (prefixWord ++ tailWord_1866966) baseStart_1866966 baseEnd_1866966 := by
    simpa [prefixWord, tailWord_1866966, baseEnd_1866966] using wordTrace_append hprefix tailTrace_1866966
  have hstable : (prefixWord ++ tailWord_1866966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866966).length < 2 ^ (prefixWord ++ tailWord_1866966).sum := by decide
  have hdescent : baseEnd_1866966 < baseStart_1866966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866969 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 3, 6]
def baseStart_1866969 : Nat := 118140960795 + 1866969 * 2 ^ 59
def prefixEnd_1866969 : Nat := 4983230072969 + 3 ^ 40 * 1866969 * 2
def baseEnd_1866969 : Nat := 639101642696007472600981

theorem tailTrace_1866969 : CollatzResearch.WordTrace tailWord_1866969 prefixEnd_1866969 639101642696007472600981 := by
  unfold tailWord_1866969
  simp only [CollatzResearch.WordTrace]
  refine ⟨68093953573297640765131961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45395969048865093843421307 68093953573297640765131961)
  ·
    refine ⟨51070465179973230573848971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68093953573297640765131961 51070465179973230573848971)
    ·
      refine ⟨76605697769959845860773457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51070465179973230573848971 76605697769959845860773457)
      ·
        refine ⟨57454273327469884395580093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76605697769959845860773457 57454273327469884395580093)
        ·
          refine ⟨21545352497801206648342535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57454273327469884395580093 21545352497801206648342535)
          ·
            refine ⟨32318028746701809972513803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21545352497801206648342535 32318028746701809972513803)
            ·
              refine ⟨48477043120052714958770705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32318028746701809972513803 48477043120052714958770705)
              ·
                refine ⟨36357782340039536219078029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48477043120052714958770705 36357782340039536219078029)
                ·
                  refine ⟨13634168377514826082154261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36357782340039536219078029 13634168377514826082154261)
                  ·
                    refine ⟨639101642696007472600981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13634168377514826082154261 639101642696007472600981)
                    ·
                      rfl

theorem cell22_1866969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_1866969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866969 prefixEnd_1866969 := by exact prefixLift 1866969
  have htrace : WordTrace (prefixWord ++ tailWord_1866969) baseStart_1866969 baseEnd_1866969 := by
    simpa [prefixWord, tailWord_1866969, baseEnd_1866969] using wordTrace_append hprefix tailTrace_1866969
  have hstable : (prefixWord ++ tailWord_1866969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866969).length < 2 ^ (prefixWord ++ tailWord_1866969).sum := by decide
  have hdescent : baseEnd_1866969 < baseStart_1866969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866988 : List Nat := [2, 2, 1, 1, 2, 4, 2, 3, 2, 3]
def baseStart_1866988 : Nat := 118140960795 + 1866988 * 2 ^ 59
def prefixEnd_1866988 : Nat := 4983230072969 + 3 ^ 40 * 1866988 * 2
def baseEnd_1866988 : Nat := 639108146784297756375923

theorem tailTrace_1866988 : CollatzResearch.WordTrace tailWord_1866988 prefixEnd_1866988 639108146784297756375923 := by
  unfold tailWord_1866988
  simp only [CollatzResearch.WordTrace]
  refine ⟨34047323280114403505036809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45396431040152538006715745 34047323280114403505036809)
  ·
    refine ⟨25535492460085802628777607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34047323280114403505036809 25535492460085802628777607)
    ·
      refine ⟨38303238690128703943166411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25535492460085802628777607 38303238690128703943166411)
      ·
        refine ⟨57454858035193055914749617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38303238690128703943166411 57454858035193055914749617)
        ·
          refine ⟨43091143526394791936062213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57454858035193055914749617 43091143526394791936062213)
          ·
            refine ⟨8079589411199023488011665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43091143526394791936062213 8079589411199023488011665)
            ·
              refine ⟨6059692058399267616008749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8079589411199023488011665 6059692058399267616008749)
              ·
                refine ⟨2272384521899725356003281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6059692058399267616008749 2272384521899725356003281)
                ·
                  refine ⟨1704288391424794017002461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2272384521899725356003281 1704288391424794017002461)
                  ·
                    refine ⟨639108146784297756375923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1704288391424794017002461 639108146784297756375923)
                    ·
                      rfl

theorem cell22_1866988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_1866988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866988 prefixEnd_1866988 := by exact prefixLift 1866988
  have htrace : WordTrace (prefixWord ++ tailWord_1866988) baseStart_1866988 baseEnd_1866988 := by
    simpa [prefixWord, tailWord_1866988, baseEnd_1866988] using wordTrace_append hprefix tailTrace_1866988
  have hstable : (prefixWord ++ tailWord_1866988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866988).length < 2 ^ (prefixWord ++ tailWord_1866988).sum := by decide
  have hdescent : baseEnd_1866988 < baseStart_1866988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866999 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 2, 7]
def baseStart_1866999 : Nat := 118140960795 + 1866999 * 2 ^ 59
def prefixEnd_1866999 : Nat := 4983230072969 + 3 ^ 40 * 1866999 * 2
def baseEnd_1866999 : Nat := 639111912309097394350889

theorem tailTrace_1866999 : CollatzResearch.WordTrace tailWord_1866999 prefixEnd_1866999 639111912309097394350889 := by
  unfold tailWord_1866999
  simp only [CollatzResearch.WordTrace]
  refine ⟨68095047763188955888724051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45396698508792637259149367 68095047763188955888724051)
  ·
    refine ⟨102142571644783433833086077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68095047763188955888724051 102142571644783433833086077)
    ·
      refine ⟨38303464366793787687407279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102142571644783433833086077 38303464366793787687407279)
      ·
        refine ⟨57455196550190681531110919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38303464366793787687407279 57455196550190681531110919)
        ·
          refine ⟨86182794825286022296666379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57455196550190681531110919 86182794825286022296666379)
          ·
            refine ⟨129274192237929033444999569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86182794825286022296666379 129274192237929033444999569)
            ·
              refine ⟨96955644178446775083749677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129274192237929033444999569 96955644178446775083749677)
              ·
                refine ⟨36358366566917540656406129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96955644178446775083749677 36358366566917540656406129)
                ·
                  refine ⟨27268774925188155492304597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36358366566917540656406129 27268774925188155492304597)
                  ·
                    refine ⟨639111912309097394350889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27268774925188155492304597 639111912309097394350889)
                    ·
                      rfl

theorem cell22_1866999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_1866999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1866999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1866999 prefixEnd_1866999 := by exact prefixLift 1866999
  have htrace : WordTrace (prefixWord ++ tailWord_1866999) baseStart_1866999 baseEnd_1866999 := by
    simpa [prefixWord, tailWord_1866999, baseEnd_1866999] using wordTrace_append hprefix tailTrace_1866999
  have hstable : (prefixWord ++ tailWord_1866999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866999).length < 2 ^ (prefixWord ++ tailWord_1866999).sum := by decide
  have hdescent : baseEnd_1866999 < baseStart_1866999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867001 : List Nat := [1, 2, 1, 3, 1, 1, 7, 6]
def baseStart_1867001 : Nat := 118140960795 + 1867001 * 2 ^ 59
def prefixEnd_1867001 : Nat := 4983230072969 + 3 ^ 40 * 1867001 * 2
def baseEnd_1867001 : Nat := 71012510772218895088987

theorem tailTrace_1867001 : CollatzResearch.WordTrace tailWord_1867001 prefixEnd_1867001 71012510772218895088987 := by
  unfold tailWord_1867001
  simp only [CollatzResearch.WordTrace]
  refine ⟨68095120709181710230296857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45396747139454473486864571 68095120709181710230296857)
  ·
    refine ⟨51071340531886282672722643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68095120709181710230296857 51071340531886282672722643)
    ·
      refine ⟨76607010797829424009083965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51071340531886282672722643 76607010797829424009083965)
      ·
        refine ⟨28727629049186034003406487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76607010797829424009083965 28727629049186034003406487)
        ·
          refine ⟨43091443573779051005109731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28727629049186034003406487 43091443573779051005109731)
          ·
            refine ⟨64637165360668576507664597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43091443573779051005109731 64637165360668576507664597)
            ·
              refine ⟨1514933563140669761898389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 64637165360668576507664597 1514933563140669761898389)
              ·
                refine ⟨71012510772218895088987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1514933563140669761898389 71012510772218895088987)
                ·
                  rfl

theorem cell22_1867001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 6].length) (baseStart_1867001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867001 prefixEnd_1867001 := by exact prefixLift 1867001
  have htrace : WordTrace (prefixWord ++ tailWord_1867001) baseStart_1867001 baseEnd_1867001 := by
    simpa [prefixWord, tailWord_1867001, baseEnd_1867001] using wordTrace_append hprefix tailTrace_1867001
  have hstable : (prefixWord ++ tailWord_1867001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867001).length < 2 ^ (prefixWord ++ tailWord_1867001).sum := by decide
  have hdescent : baseEnd_1867001 < baseStart_1867001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867050 : List Nat := [3, 1, 4, 2, 1, 1, 2, 2, 3, 3]
def baseStart_1867050 : Nat := 118140960795 + 1867050 * 2 ^ 59
def prefixEnd_1867050 : Nat := 4983230072969 + 3 ^ 40 * 1867050 * 2
def baseEnd_1867050 : Nat := 639129370651350261325733

theorem tailTrace_1867050 : CollatzResearch.WordTrace tailWord_1867050 prefixEnd_1867050 639129370651350261325733 := by
  unfold tailWord_1867050
  simp only [CollatzResearch.WordTrace]
  refine ⟨17024226971501047899707651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45397938590669461065887069 17024226971501047899707651)
  ·
    refine ⟨25536340457251571849561477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17024226971501047899707651 25536340457251571849561477)
    ·
      refine ⟨4788063835734669721792777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25536340457251571849561477 4788063835734669721792777)
      ·
        refine ⟨3591047876801002291344583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4788063835734669721792777 3591047876801002291344583)
        ·
          refine ⟨5386571815201503437016875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3591047876801002291344583 5386571815201503437016875)
          ·
            refine ⟨8079857722802255155525313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5386571815201503437016875 8079857722802255155525313)
            ·
              refine ⟨6059893292101691366643985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8079857722802255155525313 6059893292101691366643985)
              ·
                refine ⟨4544919969076268524982989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6059893292101691366643985 4544919969076268524982989)
                ·
                  refine ⟨1704344988403600696868621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4544919969076268524982989 1704344988403600696868621)
                  ·
                    refine ⟨639129370651350261325733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1704344988403600696868621 639129370651350261325733)
                    ·
                      rfl

theorem cell22_1867050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_1867050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867050 prefixEnd_1867050 := by exact prefixLift 1867050
  have htrace : WordTrace (prefixWord ++ tailWord_1867050) baseStart_1867050 baseEnd_1867050 := by
    simpa [prefixWord, tailWord_1867050, baseEnd_1867050] using wordTrace_append hprefix tailTrace_1867050
  have hstable : (prefixWord ++ tailWord_1867050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867050).length < 2 ^ (prefixWord ++ tailWord_1867050).sum := by decide
  have hdescent : baseEnd_1867050 < baseStart_1867050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867121 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 1, 6]
def baseStart_1867121 : Nat := 118140960795 + 1867121 * 2 ^ 59
def prefixEnd_1867121 : Nat := 4983230072969 + 3 ^ 40 * 1867121 * 2
def baseEnd_1867121 : Nat := 639153675402329742800515

theorem tailTrace_1867121 : CollatzResearch.WordTrace tailWord_1867121 prefixEnd_1867121 639153675402329742800515 := by
  unfold tailWord_1867121
  simp only [CollatzResearch.WordTrace]
  refine ⟨68099497468746970724665217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45399664979164647149776811 68099497468746970724665217)
  ·
    refine ⟨51074623101560228043498913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68099497468746970724665217 51074623101560228043498913)
    ·
      refine ⟨38305967326170171032624185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51074623101560228043498913 38305967326170171032624185)
      ·
        refine ⟨28729475494627628274468139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38305967326170171032624185 28729475494627628274468139)
        ·
          refine ⟨43094213241941442411702209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28729475494627628274468139 43094213241941442411702209)
          ·
            refine ⟨32320659931456081808776657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43094213241941442411702209 32320659931456081808776657)
            ·
              refine ⟨24240494948592061356582493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32320659931456081808776657 24240494948592061356582493)
              ·
                refine ⟨9090185605722023008718435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24240494948592061356582493 9090185605722023008718435)
                ·
                  refine ⟨13635278408583034513077653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9090185605722023008718435 13635278408583034513077653)
                  ·
                    refine ⟨639153675402329742800515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13635278408583034513077653 639153675402329742800515)
                    ·
                      rfl

theorem cell22_1867121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_1867121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867121 prefixEnd_1867121 := by exact prefixLift 1867121
  have htrace : WordTrace (prefixWord ++ tailWord_1867121) baseStart_1867121 baseEnd_1867121 := by
    simpa [prefixWord, tailWord_1867121, baseEnd_1867121] using wordTrace_append hprefix tailTrace_1867121
  have hstable : (prefixWord ++ tailWord_1867121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867121).length < 2 ^ (prefixWord ++ tailWord_1867121).sum := by decide
  have hdescent : baseEnd_1867121 < baseStart_1867121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867140 : List Nat := [2, 3, 2, 1, 1, 3, 1, 4, 2, 3]
def baseStart_1867140 : Nat := 118140960795 + 1867140 * 2 ^ 59
def prefixEnd_1867140 : Nat := 4983230072969 + 3 ^ 40 * 1867140 * 2
def baseEnd_1867140 : Nat := 639160179490620026575457

theorem tailTrace_1867140 : CollatzResearch.WordTrace tailWord_1867140 prefixEnd_1867140 639160179490620026575457 := by
  unfold tailWord_1867140
  simp only [CollatzResearch.WordTrace]
  refine ⟨34050095227839068484803437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45400126970452091313071249 34050095227839068484803437)
  ·
    refine ⟨12768785710439650681801289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34050095227839068484803437 12768785710439650681801289)
    ·
      refine ⟨9576589282829738011350967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12768785710439650681801289 9576589282829738011350967)
      ·
        refine ⟨14364883924244607017026451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9576589282829738011350967 14364883924244607017026451)
        ·
          refine ⟨21547325886366910525539677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14364883924244607017026451 21547325886366910525539677)
          ·
            refine ⟨8080247207387591447077379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21547325886366910525539677 8080247207387591447077379)
            ·
              refine ⟨12120370811081387170616069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8080247207387591447077379 12120370811081387170616069)
              ·
                refine ⟨2272569527077760094490513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12120370811081387170616069 2272569527077760094490513)
                ·
                  refine ⟨1704427145308320070867885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2272569527077760094490513 1704427145308320070867885)
                  ·
                    refine ⟨639160179490620026575457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1704427145308320070867885 639160179490620026575457)
                    ·
                      rfl

theorem cell22_1867140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_1867140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867140 prefixEnd_1867140 := by exact prefixLift 1867140
  have htrace : WordTrace (prefixWord ++ tailWord_1867140) baseStart_1867140 baseEnd_1867140 := by
    simpa [prefixWord, tailWord_1867140, baseEnd_1867140] using wordTrace_append hprefix tailTrace_1867140
  have hstable : (prefixWord ++ tailWord_1867140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867140).length < 2 ^ (prefixWord ++ tailWord_1867140).sum := by decide
  have hdescent : baseEnd_1867140 < baseStart_1867140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867170 : List Nat := [3, 3, 1, 2, 1, 3, 3, 6]
def baseStart_1867170 : Nat := 118140960795 + 1867170 * 2 ^ 59
def prefixEnd_1867170 : Nat := 4983230072969 + 3 ^ 40 * 1867170 * 2
def baseEnd_1867170 : Nat := 71018938789301105369485

theorem tailTrace_1867170 : CollatzResearch.WordTrace tailWord_1867170 prefixEnd_1867170 71018938789301105369485 := by
  unfold tailWord_1867170
  simp only [CollatzResearch.WordTrace]
  refine ⟨17025321161392363023299741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45400856430379634728799309 17025321161392363023299741)
  ·
    refine ⟨6384495435522136133737403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17025321161392363023299741 6384495435522136133737403)
    ·
      refine ⟨9576743153283204200606105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6384495435522136133737403 9576743153283204200606105)
      ·
        refine ⟨7182557364962403150454579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9576743153283204200606105 7182557364962403150454579)
        ·
          refine ⟨10773836047443604725681869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7182557364962403150454579 10773836047443604725681869)
          ·
            refine ⟨4040188517791351772130701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10773836047443604725681869 4040188517791351772130701)
            ·
              refine ⟨1515070694171756914549013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4040188517791351772130701 1515070694171756914549013)
              ·
                refine ⟨71018938789301105369485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1515070694171756914549013 71018938789301105369485)
                ·
                  rfl

theorem cell22_1867170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 6].length) (baseStart_1867170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867170 prefixEnd_1867170 := by exact prefixLift 1867170
  have htrace : WordTrace (prefixWord ++ tailWord_1867170) baseStart_1867170 baseEnd_1867170 := by
    simpa [prefixWord, tailWord_1867170, baseEnd_1867170] using wordTrace_append hprefix tailTrace_1867170
  have hstable : (prefixWord ++ tailWord_1867170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867170).length < 2 ^ (prefixWord ++ tailWord_1867170).sum := by decide
  have hdescent : baseEnd_1867170 < baseStart_1867170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867260 : List Nat := [2, 2, 2, 1, 2, 1, 2, 6, 4]
def baseStart_1867260 : Nat := 118140960795 + 1867260 * 2 ^ 59
def prefixEnd_1867260 : Nat := 4983230072969 + 3 ^ 40 * 1867260 * 2
def baseEnd_1867260 : Nat := 213067085980993237858363

theorem tailTrace_1867260 : CollatzResearch.WordTrace tailWord_1867260 prefixEnd_1867260 213067085980993237858363 := by
  unfold tailWord_1867260
  simp only [CollatzResearch.WordTrace]
  refine ⟨34052283607621698731987617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45403044810162264975983489 34052283607621698731987617)
  ·
    refine ⟨25539212705716274048990713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34052283607621698731987617 25539212705716274048990713)
    ·
      refine ⟨19154409529287205536743035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25539212705716274048990713 19154409529287205536743035)
      ·
        refine ⟨28731614293930808305114553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19154409529287205536743035 28731614293930808305114553)
        ·
          refine ⟨21548710720448106228835915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28731614293930808305114553 21548710720448106228835915)
          ·
            refine ⟨32323066080672159343253873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21548710720448106228835915 32323066080672159343253873)
            ·
              refine ⟨24242299560504119507440405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32323066080672159343253873 24242299560504119507440405)
              ·
                refine ⟨1136357791898630601911269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24242299560504119507440405 1136357791898630601911269)
                ·
                  refine ⟨213067085980993237858363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1136357791898630601911269 213067085980993237858363)
                  ·
                    rfl

theorem cell22_1867260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_1867260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867260 prefixEnd_1867260 := by exact prefixLift 1867260
  have htrace : WordTrace (prefixWord ++ tailWord_1867260) baseStart_1867260 baseEnd_1867260 := by
    simpa [prefixWord, tailWord_1867260, baseEnd_1867260] using wordTrace_append hprefix tailTrace_1867260
  have hstable : (prefixWord ++ tailWord_1867260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867260).length < 2 ^ (prefixWord ++ tailWord_1867260).sum := by decide
  have hdescent : baseEnd_1867260 < baseStart_1867260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867273 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 4, 4]
def baseStart_1867273 : Nat := 118140960795 + 1867273 * 2 ^ 59
def prefixEnd_1867273 : Nat := 4983230072969 + 3 ^ 40 * 1867273 * 2
def baseEnd_1867273 : Nat := 639205708108652013000049

theorem tailTrace_1867273 : CollatzResearch.WordTrace tailWord_1867273 prefixEnd_1867273 639205708108652013000049 := by
  unfold tailWord_1867273
  simp only [CollatzResearch.WordTrace]
  refine ⟨68105041364196300684198473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45403360909464200456132315 68105041364196300684198473)
  ·
    refine ⟨51078781023147225513148855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68105041364196300684198473 51078781023147225513148855)
    ·
      refine ⟨76618171534720838269723283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51078781023147225513148855 76618171534720838269723283)
      ·
        refine ⟨114927257302081257404584925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76618171534720838269723283 114927257302081257404584925)
        ·
          refine ⟨43097721488280471526719347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114927257302081257404584925 43097721488280471526719347)
          ·
            refine ⟨64646582232420707290079021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43097721488280471526719347 64646582232420707290079021)
            ·
              refine ⟨24242468337157765233779633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64646582232420707290079021 24242468337157765233779633)
              ·
                refine ⟨18181851252868323925334725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24242468337157765233779633 18181851252868323925334725)
                ·
                  refine ⟨3409097109912810736000261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18181851252868323925334725 3409097109912810736000261)
                  ·
                    refine ⟨639205708108652013000049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3409097109912810736000261 639205708108652013000049)
                    ·
                      rfl

theorem cell22_1867273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_1867273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867273 prefixEnd_1867273 := by exact prefixLift 1867273
  have htrace : WordTrace (prefixWord ++ tailWord_1867273) baseStart_1867273 baseEnd_1867273 := by
    simpa [prefixWord, tailWord_1867273, baseEnd_1867273] using wordTrace_append hprefix tailTrace_1867273
  have hstable : (prefixWord ++ tailWord_1867273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867273).length < 2 ^ (prefixWord ++ tailWord_1867273).sum := by decide
  have hdescent : baseEnd_1867273 < baseStart_1867273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867341 : List Nat := [1, 6, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_1867341 : Nat := 118140960795 + 1867341 * 2 ^ 59
def prefixEnd_1867341 : Nat := 4983230072969 + 3 ^ 40 * 1867341 * 2
def baseEnd_1867341 : Nat := 639228985898322502299841

theorem tailTrace_1867341 : CollatzResearch.WordTrace tailWord_1867341 prefixEnd_1867341 639228985898322502299841 := by
  unfold tailWord_1867341
  simp only [CollatzResearch.WordTrace]
  refine ⟨68107521527949948297673877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45405014351966632198449251 68107521527949948297673877)
  ·
    refine ⟨3192540071622653826453463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68107521527949948297673877 3192540071622653826453463)
    ·
      refine ⟨4788810107433980739680195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3192540071622653826453463 4788810107433980739680195)
      ·
        refine ⟨7183215161150971109520293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4788810107433980739680195 7183215161150971109520293)
        ·
          refine ⟨1346852842715807083035055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7183215161150971109520293 1346852842715807083035055)
          ·
            refine ⟨2020279264073710624552583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346852842715807083035055 2020279264073710624552583)
            ·
              refine ⟨3030418896110565936828875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2020279264073710624552583 3030418896110565936828875)
              ·
                refine ⟨4545628344165848905243313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3030418896110565936828875 4545628344165848905243313)
                ·
                  refine ⟨3409221258124386678932485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4545628344165848905243313 3409221258124386678932485)
                  ·
                    refine ⟨639228985898322502299841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3409221258124386678932485 639228985898322502299841)
                    ·
                      rfl

theorem cell22_1867341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_1867341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867341 prefixEnd_1867341 := by exact prefixLift 1867341
  have htrace : WordTrace (prefixWord ++ tailWord_1867341) baseStart_1867341 baseEnd_1867341 := by
    simpa [prefixWord, tailWord_1867341, baseEnd_1867341] using wordTrace_append hprefix tailTrace_1867341
  have hstable : (prefixWord ++ tailWord_1867341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867341).length < 2 ^ (prefixWord ++ tailWord_1867341).sum := by decide
  have hdescent : baseEnd_1867341 < baseStart_1867341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867365 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 2, 5]
def baseStart_1867365 : Nat := 118140960795 + 1867365 * 2 ^ 59
def prefixEnd_1867365 : Nat := 4983230072969 + 3 ^ 40 * 1867365 * 2
def baseEnd_1867365 : Nat := 639237201588794439699767

theorem tailTrace_1867365 : CollatzResearch.WordTrace tailWord_1867365 prefixEnd_1867365 639237201588794439699767 := by
  unfold tailWord_1867365
  simp only [CollatzResearch.WordTrace]
  refine ⟨68108396879863000396547549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45405597919908666931031699 68108396879863000396547549)
  ·
    refine ⟨25540648829948625148705331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68108396879863000396547549 25540648829948625148705331)
    ·
      refine ⟨38310973244922937723057997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25540648829948625148705331 38310973244922937723057997)
      ·
        refine ⟨14366614966846101646146749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38310973244922937723057997 14366614966846101646146749)
        ·
          refine ⟨5387480612567288117305031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14366614966846101646146749 5387480612567288117305031)
          ·
            refine ⟨8081220918850932175957547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5387480612567288117305031 8081220918850932175957547)
            ·
              refine ⟨12121831378276398263936321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8081220918850932175957547 12121831378276398263936321)
              ·
                refine ⟨9091373533707298697952241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12121831378276398263936321 9091373533707298697952241)
                ·
                  refine ⟨6818530150280474023464181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9091373533707298697952241 6818530150280474023464181)
                  ·
                    refine ⟨639237201588794439699767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6818530150280474023464181 639237201588794439699767)
                    ·
                      rfl

theorem cell22_1867365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_1867365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867365 prefixEnd_1867365 := by exact prefixLift 1867365
  have htrace : WordTrace (prefixWord ++ tailWord_1867365) baseStart_1867365 baseEnd_1867365 := by
    simpa [prefixWord, tailWord_1867365, baseEnd_1867365] using wordTrace_append hprefix tailTrace_1867365
  have hstable : (prefixWord ++ tailWord_1867365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867365).length < 2 ^ (prefixWord ++ tailWord_1867365).sum := by decide
  have hdescent : baseEnd_1867365 < baseStart_1867365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867382 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_1867382 : Nat := 118140960795 + 1867382 * 2 ^ 59
def prefixEnd_1867382 : Nat := 4983230072969 + 3 ^ 40 * 1867382 * 2
def baseEnd_1867382 : Nat := 639243021036212062024715

theorem tailTrace_1867382 : CollatzResearch.WordTrace tailWord_1867382 prefixEnd_1867382 639243021036212062024715 := by
  unfold tailWord_1867382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4256813557550088268744775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45406011280534274866610933 4256813557550088268744775)
  ·
    refine ⟨6385220336325132403117163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4256813557550088268744775 6385220336325132403117163)
    ·
      refine ⟨9577830504487698604675745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6385220336325132403117163 9577830504487698604675745)
      ·
        refine ⟨7183372878365773953506809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9577830504487698604675745 7183372878365773953506809)
        ·
          refine ⟨5387529658774330465130107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7183372878365773953506809 5387529658774330465130107)
          ·
            refine ⟨8081294488161495697695161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5387529658774330465130107 8081294488161495697695161)
            ·
              refine ⟨6060970866121121773271371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8081294488161495697695161 6060970866121121773271371)
              ·
                refine ⟨9091456299181682659907057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6060970866121121773271371 9091456299181682659907057)
                ·
                  refine ⟨6818592224386261994930293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9091456299181682659907057 6818592224386261994930293)
                  ·
                    refine ⟨639243021036212062024715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6818592224386261994930293 639243021036212062024715)
                    ·
                      rfl

theorem cell22_1867382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_1867382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867382 prefixEnd_1867382 := by exact prefixLift 1867382
  have htrace : WordTrace (prefixWord ++ tailWord_1867382) baseStart_1867382 baseEnd_1867382 := by
    simpa [prefixWord, tailWord_1867382, baseEnd_1867382] using wordTrace_append hprefix tailTrace_1867382
  have hstable : (prefixWord ++ tailWord_1867382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867382).length < 2 ^ (prefixWord ++ tailWord_1867382).sum := by decide
  have hdescent : baseEnd_1867382 < baseStart_1867382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867397 : List Nat := [1, 3, 1, 1, 4, 1, 4, 2, 1, 4]
def baseStart_1867397 : Nat := 118140960795 + 1867397 * 2 ^ 59
def prefixEnd_1867397 : Nat := 4983230072969 + 3 ^ 40 * 1867397 * 2
def baseEnd_1867397 : Nat := 639248155842757022899669

theorem tailTrace_1867397 : CollatzResearch.WordTrace tailWord_1867397 prefixEnd_1867397 639248155842757022899669 := by
  unfold tailWord_1867397
  simp only [CollatzResearch.WordTrace]
  refine ⟨68109564015747069861712445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45406376010498046574474963 68109564015747069861712445)
  ·
    refine ⟨25541086505905151198142167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68109564015747069861712445 25541086505905151198142167)
    ·
      refine ⟨38311629758857726797213251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25541086505905151198142167 38311629758857726797213251)
      ·
        refine ⟨57467444638286590195819877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38311629758857726797213251 57467444638286590195819877)
        ·
          refine ⟨10775145869678735661716227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57467444638286590195819877 10775145869678735661716227)
          ·
            refine ⟨16162718804518103492574341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10775145869678735661716227 16162718804518103492574341)
            ·
              refine ⟨3030509775847144404857689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16162718804518103492574341 3030509775847144404857689)
              ·
                refine ⟨2272882331885358303643267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3030509775847144404857689 2272882331885358303643267)
                ·
                  refine ⟨3409323497828037455464901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2272882331885358303643267 3409323497828037455464901)
                  ·
                    refine ⟨639248155842757022899669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3409323497828037455464901 639248155842757022899669)
                    ·
                      rfl

theorem cell22_1867397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_1867397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867397 prefixEnd_1867397 := by exact prefixLift 1867397
  have htrace : WordTrace (prefixWord ++ tailWord_1867397) baseStart_1867397 baseEnd_1867397 := by
    simpa [prefixWord, tailWord_1867397, baseEnd_1867397] using wordTrace_append hprefix tailTrace_1867397
  have hstable : (prefixWord ++ tailWord_1867397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867397).length < 2 ^ (prefixWord ++ tailWord_1867397).sum := by decide
  have hdescent : baseEnd_1867397 < baseStart_1867397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867427 : List Nat := [1, 1, 1, 4, 1, 1, 4, 4, 2, 3]
def baseStart_1867427 : Nat := 118140960795 + 1867427 * 2 ^ 59
def prefixEnd_1867427 : Nat := 4983230072969 + 3 ^ 40 * 1867427 * 2
def baseEnd_1867427 : Nat := 639258425455846944649577

theorem tailTrace_1867427 : CollatzResearch.WordTrace tailWord_1867427 prefixEnd_1867427 639258425455846944649577 := by
  unfold tailWord_1867427
  simp only [CollatzResearch.WordTrace]
  refine ⟨68110658205638384985304535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45407105470425589990203023 68110658205638384985304535)
  ·
    refine ⟨102165987308457577477956803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68110658205638384985304535 102165987308457577477956803)
    ·
      refine ⟨153248980962686366216935205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102165987308457577477956803 153248980962686366216935205)
      ·
        refine ⟨28734183930503693665675351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153248980962686366216935205 28734183930503693665675351)
        ·
          refine ⟨43101275895755540498513027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28734183930503693665675351 43101275895755540498513027)
          ·
            refine ⟨64651913843633310747769541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43101275895755540498513027 64651913843633310747769541)
            ·
              refine ⟨12122233845681245765206789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64651913843633310747769541 12122233845681245765206789)
              ·
                refine ⟨2272918846065233580976273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12122233845681245765206789 2272918846065233580976273)
                ·
                  refine ⟨1704689134548925185732205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2272918846065233580976273 1704689134548925185732205)
                  ·
                    refine ⟨639258425455846944649577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1704689134548925185732205 639258425455846944649577)
                    ·
                      rfl

theorem cell22_1867427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 3].length) (baseStart_1867427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867427 prefixEnd_1867427 := by exact prefixLift 1867427
  have htrace : WordTrace (prefixWord ++ tailWord_1867427) baseStart_1867427 baseEnd_1867427 := by
    simpa [prefixWord, tailWord_1867427, baseEnd_1867427] using wordTrace_append hprefix tailTrace_1867427
  have hstable : (prefixWord ++ tailWord_1867427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867427).length < 2 ^ (prefixWord ++ tailWord_1867427).sum := by decide
  have hdescent : baseEnd_1867427 < baseStart_1867427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867500 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 1, 7]
def baseStart_1867500 : Nat := 118140960795 + 1867500 * 2 ^ 59
def prefixEnd_1867500 : Nat := 4983230072969 + 3 ^ 40 * 1867500 * 2
def baseEnd_1867500 : Nat := 639283414847699087574353

theorem tailTrace_1867500 : CollatzResearch.WordTrace tailWord_1867500 prefixEnd_1867500 639283414847699087574353 := by
  unfold tailWord_1867500
  simp only [CollatzResearch.WordTrace]
  refine ⟨34056660367186959226355977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45408880489582612301807969 34056660367186959226355977)
  ·
    refine ⟨25542495275390219419766983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34056660367186959226355977 25542495275390219419766983)
    ·
      refine ⟨38313742913085329129650475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25542495275390219419766983 38313742913085329129650475)
      ·
        refine ⟨57470614369627993694475713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38313742913085329129650475 57470614369627993694475713)
        ·
          refine ⟨43102960777220995270856785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57470614369627993694475713 43102960777220995270856785)
          ·
            refine ⟨32327220582915746453142589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43102960777220995270856785 32327220582915746453142589)
            ·
              refine ⟨12122707718593404919928471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32327220582915746453142589 12122707718593404919928471)
              ·
                refine ⟨18184061577890107379892707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12122707718593404919928471 18184061577890107379892707)
                ·
                  refine ⟨27276092366835161069839061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18184061577890107379892707 27276092366835161069839061)
                  ·
                    refine ⟨639283414847699087574353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27276092366835161069839061 639283414847699087574353)
                    ·
                      rfl

theorem cell22_1867500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_1867500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867500 prefixEnd_1867500 := by exact prefixLift 1867500
  have htrace : WordTrace (prefixWord ++ tailWord_1867500) baseStart_1867500 baseEnd_1867500 := by
    simpa [prefixWord, tailWord_1867500, baseEnd_1867500] using wordTrace_append hprefix tailTrace_1867500
  have hstable : (prefixWord ++ tailWord_1867500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867500).length < 2 ^ (prefixWord ++ tailWord_1867500).sum := by decide
  have hdescent : baseEnd_1867500 < baseStart_1867500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867502 : List Nat := [4, 1, 2, 1, 1, 2, 1, 5, 5]
def baseStart_1867502 : Nat := 118140960795 + 1867502 * 2 ^ 59
def prefixEnd_1867502 : Nat := 4983230072969 + 3 ^ 40 * 1867502 * 2
def baseEnd_1867502 : Nat := 213094699829523916341449

theorem tailTrace_1867502 : CollatzResearch.WordTrace tailWord_1867502 prefixEnd_1867502 213094699829523916341449 := by
  unfold tailWord_1867502
  simp only [CollatzResearch.WordTrace]
  refine ⟨8514174210045834099285595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45408929120244448529523173 8514174210045834099285595)
  ·
    refine ⟨12771261315068751148928393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8514174210045834099285595 12771261315068751148928393)
    ·
      refine ⟨9578445986301563361696295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12771261315068751148928393 9578445986301563361696295)
      ·
        refine ⟨14367668979452345042544443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9578445986301563361696295 14367668979452345042544443)
        ·
          refine ⟨21551503469178517563816665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14367668979452345042544443 21551503469178517563816665)
          ·
            refine ⟨16163627601883888172862499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21551503469178517563816665 16163627601883888172862499)
            ·
              refine ⟨24245441402825832259293749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16163627601883888172862499 24245441402825832259293749)
              ·
                refine ⟨2273010131514921774308789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24245441402825832259293749 2273010131514921774308789)
                ·
                  refine ⟨213094699829523916341449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2273010131514921774308789 213094699829523916341449)
                  ·
                    rfl

theorem cell22_1867502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_1867502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867502 prefixEnd_1867502 := by exact prefixLift 1867502
  have htrace : WordTrace (prefixWord ++ tailWord_1867502) baseStart_1867502 baseEnd_1867502 := by
    simpa [prefixWord, tailWord_1867502, baseEnd_1867502] using wordTrace_append hprefix tailTrace_1867502
  have hstable : (prefixWord ++ tailWord_1867502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867502).length < 2 ^ (prefixWord ++ tailWord_1867502).sum := by decide
  have hdescent : baseEnd_1867502 < baseStart_1867502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867540 : List Nat := [2, 4, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_1867540 : Nat := 118140960795 + 1867540 * 2 ^ 59
def prefixEnd_1867540 : Nat := 4983230072969 + 3 ^ 40 * 1867540 * 2
def baseEnd_1867540 : Nat := 639297107665152316574231

theorem tailTrace_1867540 : CollatzResearch.WordTrace tailWord_1867540 prefixEnd_1867540 639297107665152316574231 := by
  unfold tailWord_1867540
  simp only [CollatzResearch.WordTrace]
  refine ⟨34057389827114502642084037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45409853102819336856112049 34057389827114502642084037)
  ·
    refine ⟨6385760592583969245390757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34057389827114502642084037 6385760592583969245390757)
    ·
      refine ⟨1197330111109494233510767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6385760592583969245390757 1197330111109494233510767)
      ·
        refine ⟨1795995166664241350266151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1197330111109494233510767 1795995166664241350266151)
        ·
          refine ⟨2693992749996362025399227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1795995166664241350266151 2693992749996362025399227)
          ·
            refine ⟨4040989124994543038098841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2693992749996362025399227 4040989124994543038098841)
            ·
              refine ⟨3030741843745907278574131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4040989124994543038098841 3030741843745907278574131)
              ·
                refine ⟨4546112765618860917861197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3030741843745907278574131 4546112765618860917861197)
                ·
                  refine ⟨1704792287107072844197949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4546112765618860917861197 1704792287107072844197949)
                  ·
                    refine ⟨639297107665152316574231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1704792287107072844197949 639297107665152316574231)
                    ·
                      rfl

theorem cell22_1867540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_1867540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867540 prefixEnd_1867540 := by exact prefixLift 1867540
  have htrace : WordTrace (prefixWord ++ tailWord_1867540) baseStart_1867540 baseEnd_1867540 := by
    simpa [prefixWord, tailWord_1867540, baseEnd_1867540] using wordTrace_append hprefix tailTrace_1867540
  have hstable : (prefixWord ++ tailWord_1867540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867540).length < 2 ^ (prefixWord ++ tailWord_1867540).sum := by decide
  have hdescent : baseEnd_1867540 < baseStart_1867540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867581 : List Nat := [1, 4, 1, 4, 1, 1, 3, 3, 4]
def baseStart_1867581 : Nat := 118140960795 + 1867581 * 2 ^ 59
def prefixEnd_1867581 : Nat := 4983230072969 + 3 ^ 40 * 1867581 * 2
def baseEnd_1867581 : Nat := 213103714267680625433035

theorem tailTrace_1867581 : CollatzResearch.WordTrace tailWord_1867581 prefixEnd_1867581 213103714267680625433035 := by
  unfold tailWord_1867581
  simp only [CollatzResearch.WordTrace]
  refine ⟨68116275047080469286410597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45410850031386979524273731 68116275047080469286410597)
  ·
    refine ⟨12771801571327587991201987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68116275047080469286410597 12771801571327587991201987)
    ·
      refine ⟨19157702356991381986802981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12771801571327587991201987 19157702356991381986802981)
      ·
        refine ⟨3592069191935884122525559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19157702356991381986802981 3592069191935884122525559)
        ·
          refine ⟨5388103787903826183788339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3592069191935884122525559 5388103787903826183788339)
          ·
            refine ⟨8082155681855739275682509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5388103787903826183788339 8082155681855739275682509)
            ·
              refine ⟨3030808380695902228380941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8082155681855739275682509 3030808380695902228380941)
              ·
                refine ⟨1136553142760963335642853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3030808380695902228380941 1136553142760963335642853)
                ·
                  refine ⟨213103714267680625433035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1136553142760963335642853 213103714267680625433035)
                  ·
                    rfl

theorem cell22_1867581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_1867581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867581 prefixEnd_1867581 := by exact prefixLift 1867581
  have htrace : WordTrace (prefixWord ++ tailWord_1867581) baseStart_1867581 baseEnd_1867581 := by
    simpa [prefixWord, tailWord_1867581, baseEnd_1867581] using wordTrace_append hprefix tailTrace_1867581
  have hstable : (prefixWord ++ tailWord_1867581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867581).length < 2 ^ (prefixWord ++ tailWord_1867581).sum := by decide
  have hdescent : baseEnd_1867581 < baseStart_1867581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867592 : List Nat := [2, 1, 3, 1, 1, 6, 8]
def baseStart_1867592 : Nat := 118140960795 + 1867592 * 2 ^ 59
def prefixEnd_1867592 : Nat := 4983230072969 + 3 ^ 40 * 1867592 * 2
def baseEnd_1867592 : Nat := 23678329938068204232373

theorem tailTrace_1867592 : CollatzResearch.WordTrace tailWord_1867592 prefixEnd_1867592 23678329938068204232373 := by
  unfold tailWord_1867592
  simp only [CollatzResearch.WordTrace]
  refine ⟨34058338125020309082530515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45411117500027078776707353 34058338125020309082530515)
  ·
    refine ⟨51087507187530463623795773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34058338125020309082530515 51087507187530463623795773)
    ·
      refine ⟨19157815195323923858923415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51087507187530463623795773 19157815195323923858923415)
      ·
        refine ⟨28736722792985885788385123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19157815195323923858923415 28736722792985885788385123)
        ·
          refine ⟨43105084189478828682577685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28736722792985885788385123 43105084189478828682577685)
          ·
            refine ⟨2020550821381820094495829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43105084189478828682577685 2020550821381820094495829)
            ·
              refine ⟨23678329938068204232373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2020550821381820094495829 23678329938068204232373)
              ·
                rfl

theorem cell22_1867592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 8].length) (baseStart_1867592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867592 prefixEnd_1867592 := by exact prefixLift 1867592
  have htrace : WordTrace (prefixWord ++ tailWord_1867592) baseStart_1867592 baseEnd_1867592 := by
    simpa [prefixWord, tailWord_1867592, baseEnd_1867592] using wordTrace_append hprefix tailTrace_1867592
  have hstable : (prefixWord ++ tailWord_1867592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867592).length < 2 ^ (prefixWord ++ tailWord_1867592).sum := by decide
  have hdescent : baseEnd_1867592 < baseStart_1867592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867624 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 5, 3]
def baseStart_1867624 : Nat := 118140960795 + 1867624 * 2 ^ 59
def prefixEnd_1867624 : Nat := 4983230072969 + 3 ^ 40 * 1867624 * 2
def baseEnd_1867624 : Nat := 639325862581804097473973

theorem tailTrace_1867624 : CollatzResearch.WordTrace tailWord_1867624 prefixEnd_1867624 639325862581804097473973 := by
  unfold tailWord_1867624
  simp only [CollatzResearch.WordTrace]
  refine ⟨34058921692962343815112963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45411895590616458420150617 34058921692962343815112963)
  ·
    refine ⟨51088382539443515722669445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34058921692962343815112963 51088382539443515722669445)
    ·
      refine ⟨9579071726145659198000521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51088382539443515722669445 9579071726145659198000521)
      ·
        refine ⟨7184303794609244398500391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9579071726145659198000521 7184303794609244398500391)
        ·
          refine ⟨10776455691913866597750587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7184303794609244398500391 10776455691913866597750587)
          ·
            refine ⟨16164683537870799896625881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10776455691913866597750587 16164683537870799896625881)
            ·
              refine ⟨12123512653403099922469411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16164683537870799896625881 12123512653403099922469411)
              ·
                refine ⟨18185268980104649883704117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12123512653403099922469411 18185268980104649883704117)
                ·
                  refine ⟨1704868966884810926597261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18185268980104649883704117 1704868966884810926597261)
                  ·
                    refine ⟨639325862581804097473973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1704868966884810926597261 639325862581804097473973)
                    ·
                      rfl

theorem cell22_1867624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_1867624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867624 prefixEnd_1867624 := by exact prefixLift 1867624
  have htrace : WordTrace (prefixWord ++ tailWord_1867624) baseStart_1867624 baseEnd_1867624 := by
    simpa [prefixWord, tailWord_1867624, baseEnd_1867624] using wordTrace_append hprefix tailTrace_1867624
  have hstable : (prefixWord ++ tailWord_1867624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867624).length < 2 ^ (prefixWord ++ tailWord_1867624).sum := by decide
  have hdescent : baseEnd_1867624 < baseStart_1867624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867641 : List Nat := [1, 2, 1, 3, 2, 2, 2, 5, 1, 3]
def baseStart_1867641 : Nat := 118140960795 + 1867641 * 2 ^ 59
def prefixEnd_1867641 : Nat := 4983230072969 + 3 ^ 40 * 1867641 * 2
def baseEnd_1867641 : Nat := 639331682029221719798921

theorem tailTrace_1867641 : CollatzResearch.WordTrace tailWord_1867641 prefixEnd_1867641 639331682029221719798921 := by
  unfold tailWord_1867641
  simp only [CollatzResearch.WordTrace]
  refine ⟨68118463426863099533594777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45412308951242066355729851 68118463426863099533594777)
  ·
    refine ⟨51088847570147324650196083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68118463426863099533594777 51088847570147324650196083)
    ·
      refine ⟨76633271355220986975294125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51088847570147324650196083 76633271355220986975294125)
      ·
        refine ⟨28737476758207870115735297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76633271355220986975294125 28737476758207870115735297)
        ·
          refine ⟨21553107568655902586801473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28737476758207870115735297 21553107568655902586801473)
          ·
            refine ⟨16164830676491926940101105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21553107568655902586801473 16164830676491926940101105)
            ·
              refine ⟨12123623007368945205075829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16164830676491926940101105 12123623007368945205075829)
              ·
                refine ⟨1136589656940838612975859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12123623007368945205075829 1136589656940838612975859)
                ·
                  refine ⟨1704884485411257919463789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1136589656940838612975859 1704884485411257919463789)
                  ·
                    refine ⟨639331682029221719798921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1704884485411257919463789 639331682029221719798921)
                    ·
                      rfl

theorem cell22_1867641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 1, 3].length) (baseStart_1867641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867641 prefixEnd_1867641 := by exact prefixLift 1867641
  have htrace : WordTrace (prefixWord ++ tailWord_1867641) baseStart_1867641 baseEnd_1867641 := by
    simpa [prefixWord, tailWord_1867641, baseEnd_1867641] using wordTrace_append hprefix tailTrace_1867641
  have hstable : (prefixWord ++ tailWord_1867641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867641).length < 2 ^ (prefixWord ++ tailWord_1867641).sum := by decide
  have hdescent : baseEnd_1867641 < baseStart_1867641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867684 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_1867684 : Nat := 118140960795 + 1867684 * 2 ^ 59
def prefixEnd_1867684 : Nat := 4983230072969 + 3 ^ 40 * 1867684 * 2
def baseEnd_1867684 : Nat := 639346401807983940973789

theorem tailTrace_1867684 : CollatzResearch.WordTrace tailWord_1867684 prefixEnd_1867684 639346401807983940973789 := by
  unfold tailWord_1867684
  simp only [CollatzResearch.WordTrace]
  refine ⟨34060015882853658938705053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45413354510471545251606737 34060015882853658938705053)
  ·
    refine ⟨12772505956070122102014395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34060015882853658938705053 12772505956070122102014395)
    ·
      refine ⟨19158758934105183153021593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12772505956070122102014395 19158758934105183153021593)
      ·
        refine ⟨14369069200578887364766195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19158758934105183153021593 14369069200578887364766195)
        ·
          refine ⟨21553603800868331047149293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14369069200578887364766195 21553603800868331047149293)
          ·
            refine ⟨8082601425325624142680985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21553603800868331047149293 8082601425325624142680985)
            ·
              refine ⟨6061951068994218107010739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8082601425325624142680985 6061951068994218107010739)
              ·
                refine ⟨9092926603491327160516109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6061951068994218107010739 9092926603491327160516109)
                ·
                  refine ⟨3409847476309247685193541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9092926603491327160516109 3409847476309247685193541)
                  ·
                    refine ⟨639346401807983940973789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3409847476309247685193541 639346401807983940973789)
                    ·
                      rfl

theorem cell22_1867684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_1867684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867684 prefixEnd_1867684 := by exact prefixLift 1867684
  have htrace : WordTrace (prefixWord ++ tailWord_1867684) baseStart_1867684 baseEnd_1867684 := by
    simpa [prefixWord, tailWord_1867684, baseEnd_1867684] using wordTrace_append hprefix tailTrace_1867684
  have hstable : (prefixWord ++ tailWord_1867684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867684).length < 2 ^ (prefixWord ++ tailWord_1867684).sum := by decide
  have hdescent : baseEnd_1867684 < baseStart_1867684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867701 : List Nat := [1, 3, 3, 2, 1, 3, 1, 3, 1, 4]
def baseStart_1867701 : Nat := 118140960795 + 1867701 * 2 ^ 59
def prefixEnd_1867701 : Nat := 4983230072969 + 3 ^ 40 * 1867701 * 2
def baseEnd_1867701 : Nat := 639352221255401563298737

theorem tailTrace_1867701 : CollatzResearch.WordTrace tailWord_1867701 prefixEnd_1867701 639352221255401563298737 := by
  unfold tailWord_1867701
  simp only [CollatzResearch.WordTrace]
  refine ⟨68120651806645729780778957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45413767871097153187185971 68120651806645729780778957)
  ·
    refine ⟨25545244427492148667792109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68120651806645729780778957 25545244427492148667792109)
    ·
      refine ⟨9579466660309555750422041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25545244427492148667792109 9579466660309555750422041)
      ·
        refine ⟨7184599995232166812816531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9579466660309555750422041 7184599995232166812816531)
        ·
          refine ⟨10776899992848250219224797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7184599995232166812816531 10776899992848250219224797)
          ·
            refine ⟨4041337497318093832209299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10776899992848250219224797 4041337497318093832209299)
            ·
              refine ⟨6062006245977140748313949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4041337497318093832209299 6062006245977140748313949)
              ·
                refine ⟨2273252342241427780617731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6062006245977140748313949 2273252342241427780617731)
                ·
                  refine ⟨3409878513362141670926597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2273252342241427780617731 3409878513362141670926597)
                  ·
                    refine ⟨639352221255401563298737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3409878513362141670926597 639352221255401563298737)
                    ·
                      rfl

theorem cell22_1867701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_1867701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867701 prefixEnd_1867701 := by exact prefixLift 1867701
  have htrace : WordTrace (prefixWord ++ tailWord_1867701) baseStart_1867701 baseEnd_1867701 := by
    simpa [prefixWord, tailWord_1867701, baseEnd_1867701] using wordTrace_append hprefix tailTrace_1867701
  have hstable : (prefixWord ++ tailWord_1867701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867701).length < 2 ^ (prefixWord ++ tailWord_1867701).sum := by decide
  have hdescent : baseEnd_1867701 < baseStart_1867701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867727 : List Nat := [1, 1, 2, 1, 1, 5, 2, 9]
def baseStart_1867727 : Nat := 118140960795 + 1867727 * 2 ^ 59
def prefixEnd_1867727 : Nat := 4983230072969 + 3 ^ 40 * 1867727 * 2
def baseEnd_1867727 : Nat := 71040124620749573572073

theorem tailTrace_1867727 : CollatzResearch.WordTrace tailWord_1867727 prefixEnd_1867727 71040124620749573572073 := by
  unfold tailWord_1867727
  simp only [CollatzResearch.WordTrace]
  refine ⟨68121600104551536221225435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45414400069701024147483623 68121600104551536221225435)
  ·
    refine ⟨102182400156827304331838153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68121600104551536221225435 102182400156827304331838153)
    ·
      refine ⟨76636800117620478248878615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102182400156827304331838153 76636800117620478248878615)
      ·
        refine ⟨114955200176430717373317923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76636800117620478248878615 114955200176430717373317923)
        ·
          refine ⟨172432800264646076059976885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114955200176430717373317923 172432800264646076059976885)
          ·
            refine ⟨16165575024810569630622833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172432800264646076059976885 16165575024810569630622833)
            ·
              refine ⟨12124181268607927222967125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16165575024810569630622833 12124181268607927222967125)
              ·
                refine ⟨71040124620749573572073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12124181268607927222967125 71040124620749573572073)
                ·
                  rfl

theorem cell22_1867727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 9].length) (baseStart_1867727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867727 prefixEnd_1867727 := by exact prefixLift 1867727
  have htrace : WordTrace (prefixWord ++ tailWord_1867727) baseStart_1867727 baseEnd_1867727 := by
    simpa [prefixWord, tailWord_1867727, baseEnd_1867727] using wordTrace_append hprefix tailTrace_1867727
  have hstable : (prefixWord ++ tailWord_1867727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867727).length < 2 ^ (prefixWord ++ tailWord_1867727).sum := by decide
  have hdescent : baseEnd_1867727 < baseStart_1867727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867761 : List Nat := [1, 2, 2, 2, 6, 1, 8]
def baseStart_1867761 : Nat := 118140960795 + 1867761 * 2 ^ 59
def prefixEnd_1867761 : Nat := 4983230072969 + 3 ^ 40 * 1867761 * 2
def baseEnd_1867761 : Nat := 23680472610428940992539

theorem tailTrace_1867761 : CollatzResearch.WordTrace tailWord_1867761 prefixEnd_1867761 23680472610428940992539 := by
  unfold tailWord_1867761
  simp only [CollatzResearch.WordTrace]
  refine ⟨68122840186428360027963137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45415226790952240018642091 68122840186428360027963137)
  ·
    refine ⟨51092130139821270020972353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68122840186428360027963137 51092130139821270020972353)
    ·
      refine ⟨38319097604865952515729265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51092130139821270020972353 38319097604865952515729265)
      ·
        refine ⟨28739323203649464386796949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38319097604865952515729265 28739323203649464386796949)
        ·
          refine ⟨1347155775171068643131107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28739323203649464386796949 1347155775171068643131107)
          ·
            refine ⟨2020733662756602964696661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347155775171068643131107 2020733662756602964696661)
            ·
              refine ⟨23680472610428940992539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2020733662756602964696661 23680472610428940992539)
              ·
                rfl

theorem cell22_1867761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 8].length) (baseStart_1867761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867761 prefixEnd_1867761 := by exact prefixLift 1867761
  have htrace : WordTrace (prefixWord ++ tailWord_1867761) baseStart_1867761 baseEnd_1867761 := by
    simpa [prefixWord, tailWord_1867761, baseEnd_1867761] using wordTrace_append hprefix tailTrace_1867761
  have hstable : (prefixWord ++ tailWord_1867761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867761).length < 2 ^ (prefixWord ++ tailWord_1867761).sum := by decide
  have hdescent : baseEnd_1867761 < baseStart_1867761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867834 : List Nat := [3, 1, 1, 1, 3, 1, 1, 5, 6]
def baseStart_1867834 : Nat := 118140960795 + 1867834 * 2 ^ 59
def prefixEnd_1867834 : Nat := 4983230072969 + 3 ^ 40 * 1867834 * 2
def baseEnd_1867834 : Nat := 213132583291144516574443

theorem tailTrace_1867834 : CollatzResearch.WordTrace tailWord_1867834 prefixEnd_1867834 213132583291144516574443 := by
  unfold tailWord_1867834
  simp only [CollatzResearch.WordTrace]
  refine ⟨17031375678790973373842639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45417001810109262330247037 17031375678790973373842639)
  ·
    refine ⟨25547063518186460060763959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17031375678790973373842639 25547063518186460060763959)
    ·
      refine ⟨38320595277279690091145939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25547063518186460060763959 38320595277279690091145939)
      ·
        refine ⟨57480892915919535136718909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38320595277279690091145939 57480892915919535136718909)
        ·
          refine ⟨21555334843469825676269591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57480892915919535136718909 21555334843469825676269591)
          ·
            refine ⟨32333002265204738514404387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21555334843469825676269591 32333002265204738514404387)
            ·
              refine ⟨48499503397807107771606581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32333002265204738514404387 48499503397807107771606581)
              ·
                refine ⟨4546828443544416353588117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48499503397807107771606581 4546828443544416353588117)
                ·
                  refine ⟨213132583291144516574443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4546828443544416353588117 213132583291144516574443)
                  ·
                    rfl

theorem cell22_1867834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_1867834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867834 prefixEnd_1867834 := by exact prefixLift 1867834
  have htrace : WordTrace (prefixWord ++ tailWord_1867834) baseStart_1867834 baseEnd_1867834 := by
    simpa [prefixWord, tailWord_1867834, baseEnd_1867834] using wordTrace_append hprefix tailTrace_1867834
  have hstable : (prefixWord ++ tailWord_1867834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867834).length < 2 ^ (prefixWord ++ tailWord_1867834).sum := by decide
  have hdescent : baseEnd_1867834 < baseStart_1867834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867838 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_1867838 : Nat := 118140960795 + 1867838 * 2 ^ 59
def prefixEnd_1867838 : Nat := 4983230072969 + 3 ^ 40 * 1867838 * 2
def baseEnd_1867838 : Nat := 639399119155178872623317

theorem tailTrace_1867838 : CollatzResearch.WordTrace tailWord_1867838 prefixEnd_1867838 639399119155178872623317 := by
  unfold tailWord_1867838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8515706075893675272314521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45417099071432934785677445 8515706075893675272314521)
  ·
    refine ⟨6386779556920256454235891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8515706075893675272314521 6386779556920256454235891)
    ·
      refine ⟨9580169335380384681353837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6386779556920256454235891 9580169335380384681353837)
      ·
        refine ⟨3592563500767644255507689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9580169335380384681353837 3592563500767644255507689)
        ·
          refine ⟨2694422625575733191630767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3592563500767644255507689 2694422625575733191630767)
          ·
            refine ⟨4041633938363599787446151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2694422625575733191630767 4041633938363599787446151)
            ·
              refine ⟨6062450907545399681169227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4041633938363599787446151 6062450907545399681169227)
              ·
                refine ⟨9093676361318099521753841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6062450907545399681169227 9093676361318099521753841)
                ·
                  refine ⟨6820257270988574641315381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9093676361318099521753841 6820257270988574641315381)
                  ·
                    refine ⟨639399119155178872623317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6820257270988574641315381 639399119155178872623317)
                    ·
                      rfl

theorem cell22_1867838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_1867838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867838 prefixEnd_1867838 := by exact prefixLift 1867838
  have htrace : WordTrace (prefixWord ++ tailWord_1867838) baseStart_1867838 baseEnd_1867838 := by
    simpa [prefixWord, tailWord_1867838, baseEnd_1867838] using wordTrace_append hprefix tailTrace_1867838
  have hstable : (prefixWord ++ tailWord_1867838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867838).length < 2 ^ (prefixWord ++ tailWord_1867838).sum := by decide
  have hdescent : baseEnd_1867838 < baseStart_1867838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867853 : List Nat := [1, 6, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_1867853 : Nat := 118140960795 + 1867853 * 2 ^ 59
def prefixEnd_1867853 : Nat := 4983230072969 + 3 ^ 40 * 1867853 * 2
def baseEnd_1867853 : Nat := 639404253961723833498271

theorem tailTrace_1867853 : CollatzResearch.WordTrace tailWord_1867853 prefixEnd_1867853 639404253961723833498271 := by
  unfold tailWord_1867853
  simp only [CollatzResearch.WordTrace]
  refine ⟨68126195702095059740312213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45417463801396706493541475 68126195702095059740312213)
  ·
    refine ⟨3193415423535705925327135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68126195702095059740312213 3193415423535705925327135)
    ·
      refine ⟨4790123135303558887990703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3193415423535705925327135 4790123135303558887990703)
      ·
        refine ⟨7185184702955338331986055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4790123135303558887990703 7185184702955338331986055)
        ·
          refine ⟨10777777054433007497979083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7185184702955338331986055 10777777054433007497979083)
          ·
            refine ⟨16166665581649511246968625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10777777054433007497979083 16166665581649511246968625)
            ·
              refine ⟨12124999186237133435226469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16166665581649511246968625 12124999186237133435226469)
              ·
                refine ⟨2273437347419462519104963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12124999186237133435226469 2273437347419462519104963)
                ·
                  refine ⟨3410156021129193778657445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2273437347419462519104963 3410156021129193778657445)
                  ·
                    refine ⟨639404253961723833498271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3410156021129193778657445 639404253961723833498271)
                    ·
                      rfl

theorem cell22_1867853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_1867853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867853 prefixEnd_1867853 := by exact prefixLift 1867853
  have htrace : WordTrace (prefixWord ++ tailWord_1867853) baseStart_1867853 baseEnd_1867853 := by
    simpa [prefixWord, tailWord_1867853, baseEnd_1867853] using wordTrace_append hprefix tailTrace_1867853
  have hstable : (prefixWord ++ tailWord_1867853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867853).length < 2 ^ (prefixWord ++ tailWord_1867853).sum := by decide
  have hdescent : baseEnd_1867853 < baseStart_1867853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867866 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 4, 3]
def baseStart_1867866 : Nat := 118140960795 + 1867866 * 2 ^ 59
def prefixEnd_1867866 : Nat := 4983230072969 + 3 ^ 40 * 1867866 * 2
def baseEnd_1867866 : Nat := 639408704127396132923231

theorem tailTrace_1867866 : CollatzResearch.WordTrace tailWord_1867866 prefixEnd_1867866 639408704127396132923231 := by
  unfold tailWord_1867866
  simp only [CollatzResearch.WordTrace]
  refine ⟨17031667462761990740133863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45417779900698641973690301 17031667462761990740133863)
  ·
    refine ⟨25547501194142986110200795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17031667462761990740133863 25547501194142986110200795)
    ·
      refine ⟨38321251791214479165301193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25547501194142986110200795 38321251791214479165301193)
      ·
        refine ⟨28740938843410859373975895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38321251791214479165301193 28740938843410859373975895)
        ·
          refine ⟨43111408265116289060963843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28740938843410859373975895 43111408265116289060963843)
          ·
            refine ⟨64667112397674433591445765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43111408265116289060963843 64667112397674433591445765)
            ·
              refine ⟨12125083574563956298396081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64667112397674433591445765 12125083574563956298396081)
              ·
                refine ⟨9093812680922967223797061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12125083574563956298396081 9093812680922967223797061)
                ·
                  refine ⟨1705089877673056354461949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9093812680922967223797061 1705089877673056354461949)
                  ·
                    refine ⟨639408704127396132923231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1705089877673056354461949 639408704127396132923231)
                    ·
                      rfl

theorem cell22_1867866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_1867866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867866 prefixEnd_1867866 := by exact prefixLift 1867866
  have htrace : WordTrace (prefixWord ++ tailWord_1867866) baseStart_1867866 baseEnd_1867866 := by
    simpa [prefixWord, tailWord_1867866, baseEnd_1867866] using wordTrace_append hprefix tailTrace_1867866
  have hstable : (prefixWord ++ tailWord_1867866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867866).length < 2 ^ (prefixWord ++ tailWord_1867866).sum := by decide
  have hdescent : baseEnd_1867866 < baseStart_1867866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867868 : List Nat := [2, 2, 4, 1, 1, 2, 1, 5, 4]
def baseStart_1867868 : Nat := 118140960795 + 1867868 * 2 ^ 59
def prefixEnd_1867868 : Nat := 4983230072969 + 3 ^ 40 * 1867868 * 2
def baseEnd_1867868 : Nat := 213136462922756264791075

theorem tailTrace_1867868 : CollatzResearch.WordTrace tailWord_1867868 prefixEnd_1867868 213136462922756264791075 := by
  unfold tailWord_1867868
  simp only [CollatzResearch.WordTrace]
  refine ⟨34063371398520358651054129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45417828531360478201405505 34063371398520358651054129)
  ·
    refine ⟨25547528548890268988290597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34063371398520358651054129 25547528548890268988290597)
    ·
      refine ⟨4790161602916925435304487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25547528548890268988290597 4790161602916925435304487)
      ·
        refine ⟨7185242404375388152956731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4790161602916925435304487 7185242404375388152956731)
        ·
          refine ⟨10777863606563082229435097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7185242404375388152956731 10777863606563082229435097)
          ·
            refine ⟨8083397704922311672076323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10777863606563082229435097 8083397704922311672076323)
            ·
              refine ⟨12125096557383467508114485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8083397704922311672076323 12125096557383467508114485)
              ·
                refine ⟨1136727802254700078885733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12125096557383467508114485 1136727802254700078885733)
                ·
                  refine ⟨213136462922756264791075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1136727802254700078885733 213136462922756264791075)
                  ·
                    rfl

theorem cell22_1867868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_1867868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867868 prefixEnd_1867868 := by exact prefixLift 1867868
  have htrace : WordTrace (prefixWord ++ tailWord_1867868) baseStart_1867868 baseEnd_1867868 := by
    simpa [prefixWord, tailWord_1867868, baseEnd_1867868] using wordTrace_append hprefix tailTrace_1867868
  have hstable : (prefixWord ++ tailWord_1867868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867868).length < 2 ^ (prefixWord ++ tailWord_1867868).sum := by decide
  have hdescent : baseEnd_1867868 < baseStart_1867868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867879 : List Nat := [1, 1, 5, 1, 1, 2, 11]
def baseStart_1867879 : Nat := 118140960795 + 1867879 * 2 ^ 59
def prefixEnd_1867879 : Nat := 4983230072969 + 3 ^ 40 * 1867879 * 2
def baseEnd_1867879 : Nat := 23681968677521053049933

theorem tailTrace_1867879 : CollatzResearch.WordTrace tailWord_1867879 prefixEnd_1867879 23681968677521053049933 := by
  unfold tailWord_1867879
  simp only [CollatzResearch.WordTrace]
  refine ⟨68127144000000866180758691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45418096000000577453839127 68127144000000866180758691)
  ·
    refine ⟨102190716000001299271138037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68127144000000866180758691 102190716000001299271138037)
    ·
      refine ⟨9580379625000121806669191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102190716000001299271138037 9580379625000121806669191)
      ·
        refine ⟨14370569437500182710003787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9580379625000121806669191 14370569437500182710003787)
        ·
          refine ⟨21555854156250274065005681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14370569437500182710003787 21555854156250274065005681)
          ·
            refine ⟨16166890617187705548754261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21555854156250274065005681 16166890617187705548754261)
            ·
              refine ⟨23681968677521053049933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16166890617187705548754261 23681968677521053049933)
              ·
                rfl

theorem cell22_1867879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 11].length) (baseStart_1867879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867879 prefixEnd_1867879 := by exact prefixLift 1867879
  have htrace : WordTrace (prefixWord ++ tailWord_1867879) baseStart_1867879 baseEnd_1867879 := by
    simpa [prefixWord, tailWord_1867879, baseEnd_1867879] using wordTrace_append hprefix tailTrace_1867879
  have hstable : (prefixWord ++ tailWord_1867879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867879).length < 2 ^ (prefixWord ++ tailWord_1867879).sum := by decide
  have hdescent : baseEnd_1867879 < baseStart_1867879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867900 : List Nat := [2, 2, 2, 1, 1, 5, 3, 1, 2, 3]
def baseStart_1867900 : Nat := 118140960795 + 1867900 * 2 ^ 59
def prefixEnd_1867900 : Nat := 4983230072969 + 3 ^ 40 * 1867900 * 2
def baseEnd_1867900 : Nat := 639420343022231377573127

theorem tailTrace_1867900 : CollatzResearch.WordTrace tailWord_1867900 prefixEnd_1867900 639420343022231377573127 := by
  unfold tailWord_1867900
  simp only [CollatzResearch.WordTrace]
  refine ⟨34063954966462393383636577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45418606621949857844848769 34063954966462393383636577)
  ·
    refine ⟨25547966224846795037727433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34063954966462393383636577 25547966224846795037727433)
    ·
      refine ⟨19160974668635096278295575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25547966224846795037727433 19160974668635096278295575)
      ·
        refine ⟨28741462002952644417443363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19160974668635096278295575 28741462002952644417443363)
        ·
          refine ⟨43112193004428966626165045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28741462002952644417443363 43112193004428966626165045)
          ·
            refine ⟨4041768094165215621202973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43112193004428966626165045 4041768094165215621202973)
            ·
              refine ⟨1515663035311955857951115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4041768094165215621202973 1515663035311955857951115)
              ·
                refine ⟨2273494552967933786926673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1515663035311955857951115 2273494552967933786926673)
                ·
                  refine ⟨1705120914725950340195005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2273494552967933786926673 1705120914725950340195005)
                  ·
                    refine ⟨639420343022231377573127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1705120914725950340195005 639420343022231377573127)
                    ·
                      rfl

theorem cell22_1867900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_1867900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867900 prefixEnd_1867900 := by exact prefixLift 1867900
  have htrace : WordTrace (prefixWord ++ tailWord_1867900) baseStart_1867900 baseEnd_1867900 := by
    simpa [prefixWord, tailWord_1867900, baseEnd_1867900] using wordTrace_append hprefix tailTrace_1867900
  have hstable : (prefixWord ++ tailWord_1867900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867900).length < 2 ^ (prefixWord ++ tailWord_1867900).sum := by decide
  have hdescent : baseEnd_1867900 < baseStart_1867900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867941 : List Nat := [1, 3, 1, 2, 1, 3, 2, 4, 5]
def baseStart_1867941 : Nat := 118140960795 + 1867941 * 2 ^ 59
def prefixEnd_1867941 : Nat := 4983230072969 + 3 ^ 40 * 1867941 * 2
def baseEnd_1867941 : Nat := 213144792720040312432667

theorem tailTrace_1867941 : CollatzResearch.WordTrace tailWord_1867941 prefixEnd_1867941 213144792720040312432667 := by
  unfold tailWord_1867941
  simp only [CollatzResearch.WordTrace]
  refine ⟨68129405325776250769515677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45419603550517500513010451 68129405325776250769515677)
  ·
    refine ⟨25548526997166094038568379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68129405325776250769515677 25548526997166094038568379)
    ·
      refine ⟨38322790495749141057852569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25548526997166094038568379 38322790495749141057852569)
      ·
        refine ⟨28742092871811855793389427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38322790495749141057852569 28742092871811855793389427)
        ·
          refine ⟨43113139307717783690084141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28742092871811855793389427 43113139307717783690084141)
          ·
            refine ⟨16167427240394168883781553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43113139307717783690084141 16167427240394168883781553)
            ·
              refine ⟨12125570430295626662836165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16167427240394168883781553 12125570430295626662836165)
              ·
                refine ⟨2273544455680429999281781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12125570430295626662836165 2273544455680429999281781)
                ·
                  refine ⟨213144792720040312432667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2273544455680429999281781 213144792720040312432667)
                  ·
                    rfl

theorem cell22_1867941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_1867941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1867941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1867941 prefixEnd_1867941 := by exact prefixLift 1867941
  have htrace : WordTrace (prefixWord ++ tailWord_1867941) baseStart_1867941 baseEnd_1867941 := by
    simpa [prefixWord, tailWord_1867941, baseEnd_1867941] using wordTrace_append hprefix tailTrace_1867941
  have hstable : (prefixWord ++ tailWord_1867941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867941).length < 2 ^ (prefixWord ++ tailWord_1867941).sum := by decide
  have hdescent : baseEnd_1867941 < baseStart_1867941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868001 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 3, 5]
def baseStart_1868001 : Nat := 118140960795 + 1868001 * 2 ^ 59
def prefixEnd_1868001 : Nat := 4983230072969 + 3 ^ 40 * 1868001 * 2
def baseEnd_1868001 : Nat := 639454917386300780797817

theorem tailTrace_1868001 : CollatzResearch.WordTrace tailWord_1868001 prefixEnd_1868001 639454917386300780797817 := by
  unfold tailWord_1868001
  simp only [CollatzResearch.WordTrace]
  refine ⟨68131593705558881016699857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45421062470372587344466571 68131593705558881016699857)
  ·
    refine ⟨51098695279169160762524893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68131593705558881016699857 51098695279169160762524893)
    ·
      refine ⟨19162010729688435285946835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51098695279169160762524893 19162010729688435285946835)
      ·
        refine ⟨28743016094532652928920253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19162010729688435285946835 28743016094532652928920253)
        ·
          refine ⟨10778631035449744848345095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28743016094532652928920253 10778631035449744848345095)
          ·
            refine ⟨16167946553174617272517643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10778631035449744848345095 16167946553174617272517643)
            ·
              refine ⟨24251919829761925908776465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16167946553174617272517643 24251919829761925908776465)
              ·
                refine ⟨18188939872321444431582349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24251919829761925908776465 18188939872321444431582349)
                ·
                  refine ⟨6820852452120541661843381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18188939872321444431582349 6820852452120541661843381)
                  ·
                    refine ⟨639454917386300780797817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6820852452120541661843381 639454917386300780797817)
                    ·
                      rfl

theorem cell22_1868001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_1868001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868001 prefixEnd_1868001 := by exact prefixLift 1868001
  have htrace : WordTrace (prefixWord ++ tailWord_1868001) baseStart_1868001 baseEnd_1868001 := by
    simpa [prefixWord, tailWord_1868001, baseEnd_1868001] using wordTrace_append hprefix tailTrace_1868001
  have hstable : (prefixWord ++ tailWord_1868001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868001).length < 2 ^ (prefixWord ++ tailWord_1868001).sum := by decide
  have hdescent : baseEnd_1868001 < baseStart_1868001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868016 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 4, 4]
def baseStart_1868016 : Nat := 118140960795 + 1868016 * 2 ^ 59
def prefixEnd_1868016 : Nat := 4983230072969 + 3 ^ 40 * 1868016 * 2
def baseEnd_1868016 : Nat := 639460052192845741672771

theorem tailTrace_1868016 : CollatzResearch.WordTrace tailWord_1868016 prefixEnd_1868016 639460052192845741672771 := by
  unfold tailWord_1868016
  simp only [CollatzResearch.WordTrace]
  refine ⟨34066070400252269289247951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45421427200336359052330601 34066070400252269289247951)
  ·
    refine ⟨51099105600378403933871927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34066070400252269289247951 51099105600378403933871927)
    ·
      refine ⟨76648658400567605900807891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51099105600378403933871927 76648658400567605900807891)
      ·
        refine ⟨114972987600851408851211837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76648658400567605900807891 114972987600851408851211837)
        ·
          refine ⟨43114870350319278319204439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114972987600851408851211837 43114870350319278319204439)
          ·
            refine ⟨64672305525478917478806659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43114870350319278319204439 64672305525478917478806659)
            ·
              refine ⟨97008458288218376218209989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64672305525478917478806659 97008458288218376218209989)
              ·
                refine ⟨18189085929040945540914373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97008458288218376218209989 18189085929040945540914373)
                ·
                  refine ⟨3410453611695177288921445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18189085929040945540914373 3410453611695177288921445)
                  ·
                    refine ⟨639460052192845741672771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3410453611695177288921445 639460052192845741672771)
                    ·
                      rfl

theorem cell22_1868016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_1868016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868016 prefixEnd_1868016 := by exact prefixLift 1868016
  have htrace : WordTrace (prefixWord ++ tailWord_1868016) baseStart_1868016 baseEnd_1868016 := by
    simpa [prefixWord, tailWord_1868016, baseEnd_1868016] using wordTrace_append hprefix tailTrace_1868016
  have hstable : (prefixWord ++ tailWord_1868016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868016).length < 2 ^ (prefixWord ++ tailWord_1868016).sum := by decide
  have hdescent : baseEnd_1868016 < baseStart_1868016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868018 : List Nat := [3, 2, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_1868018 : Nat := 118140960795 + 1868018 * 2 ^ 59
def prefixEnd_1868018 : Nat := 4983230072969 + 3 ^ 40 * 1868018 * 2
def baseEnd_1868018 : Nat := 639460736833718403122765

theorem tailTrace_1868018 : CollatzResearch.WordTrace tailWord_1868018 prefixEnd_1868018 639460736833718403122765 := by
  unfold tailWord_1868018
  simp only [CollatzResearch.WordTrace]
  refine ⟨17033053436624323230017177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45421475830998195280045805 17033053436624323230017177)
  ·
    refine ⟨12774790077468242422512883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17033053436624323230017177 12774790077468242422512883)
    ·
      refine ⟨19162185116202363633769325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12774790077468242422512883 19162185116202363633769325)
      ·
        refine ⟨7185819418575886362663497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19162185116202363633769325 7185819418575886362663497)
        ·
          refine ⟨5389364563931914771997623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7185819418575886362663497 5389364563931914771997623)
          ·
            refine ⟨8084046845897872157996435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5389364563931914771997623 8084046845897872157996435)
            ·
              refine ⟨12126070268846808236994653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8084046845897872157996435 12126070268846808236994653)
              ·
                refine ⟨4547276350817553088872995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12126070268846808236994653 4547276350817553088872995)
                ·
                  refine ⟨6820914526226329633309493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4547276350817553088872995 6820914526226329633309493)
                  ·
                    refine ⟨639460736833718403122765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6820914526226329633309493 639460736833718403122765)
                    ·
                      rfl

theorem cell22_1868018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_1868018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868018 prefixEnd_1868018 := by exact prefixLift 1868018
  have htrace : WordTrace (prefixWord ++ tailWord_1868018) baseStart_1868018 baseEnd_1868018 := by
    simpa [prefixWord, tailWord_1868018, baseEnd_1868018] using wordTrace_append hprefix tailTrace_1868018
  have hstable : (prefixWord ++ tailWord_1868018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868018).length < 2 ^ (prefixWord ++ tailWord_1868018).sum := by decide
  have hdescent : baseEnd_1868018 < baseStart_1868018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868039 : List Nat := [1, 1, 4, 5, 1, 2, 2, 1, 1, 4]
def baseStart_1868039 : Nat := 118140960795 + 1868039 * 2 ^ 59
def prefixEnd_1868039 : Nat := 4983230072969 + 3 ^ 40 * 1868039 * 2
def baseEnd_1868039 : Nat := 639467925562881348347701

theorem tailTrace_1868039 : CollatzResearch.WordTrace tailWord_1868039 prefixEnd_1868039 639467925562881348347701 := by
  unfold tailWord_1868039
  simp only [CollatzResearch.WordTrace]
  refine ⟨68132979679421213506583171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45421986452947475671055447 68132979679421213506583171)
  ·
    refine ⟨102199469519131820259874757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68132979679421213506583171 102199469519131820259874757)
    ·
      refine ⟨19162400534837216298726517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102199469519131820259874757 19162400534837216298726517)
      ·
        refine ⟨1796475050140989028005611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19162400534837216298726517 1796475050140989028005611)
        ·
          refine ⟨2694712575211483542008417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1796475050140989028005611 2694712575211483542008417)
          ·
            refine ⟨2021034431408612656506313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2694712575211483542008417 2021034431408612656506313)
            ·
              refine ⟨1515775823556459492379735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2021034431408612656506313 1515775823556459492379735)
              ·
                refine ⟨2273663735334689238569603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1515775823556459492379735 2273663735334689238569603)
                ·
                  refine ⟨3410495603002033857854405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2273663735334689238569603 3410495603002033857854405)
                  ·
                    refine ⟨639467925562881348347701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3410495603002033857854405 639467925562881348347701)
                    ·
                      rfl

theorem cell22_1868039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_1868039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868039 prefixEnd_1868039 := by exact prefixLift 1868039
  have htrace : WordTrace (prefixWord ++ tailWord_1868039) baseStart_1868039 baseEnd_1868039 := by
    simpa [prefixWord, tailWord_1868039, baseEnd_1868039] using wordTrace_append hprefix tailTrace_1868039
  have hstable : (prefixWord ++ tailWord_1868039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868039).length < 2 ^ (prefixWord ++ tailWord_1868039).sum := by decide
  have hdescent : baseEnd_1868039 < baseStart_1868039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868082 : List Nat := [3, 2, 1, 1, 6, 1, 2, 6]
def baseStart_1868082 : Nat := 118140960795 + 1868082 * 2 ^ 59
def prefixEnd_1868082 : Nat := 4983230072969 + 3 ^ 40 * 1868082 * 2
def baseEnd_1868082 : Nat := 71053627260182618835841

theorem tailTrace_1868082 : CollatzResearch.WordTrace tailWord_1868082 prefixEnd_1868082 71053627260182618835841 := by
  unfold tailWord_1868082
  simp only [CollatzResearch.WordTrace]
  refine ⟨17033637004566357962599625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45423032012176954566932333 17033637004566357962599625)
  ·
    refine ⟨12775227753424768471949719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17033637004566357962599625 12775227753424768471949719)
    ·
      refine ⟨19162841630137152707924579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12775227753424768471949719 19162841630137152707924579)
      ·
        refine ⟨28744262445205729061886869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19162841630137152707924579 28744262445205729061886869)
        ·
          refine ⟨1347387302119018549775947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28744262445205729061886869 1347387302119018549775947)
          ·
            refine ⟨2021080953178527824663921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347387302119018549775947 2021080953178527824663921)
            ·
              refine ⟨1515810714883895868497941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2021080953178527824663921 1515810714883895868497941)
              ·
                refine ⟨71053627260182618835841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1515810714883895868497941 71053627260182618835841)
                ·
                  rfl

theorem cell22_1868082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 6].length) (baseStart_1868082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868082 prefixEnd_1868082 := by exact prefixLift 1868082
  have htrace : WordTrace (prefixWord ++ tailWord_1868082) baseStart_1868082 baseEnd_1868082 := by
    simpa [prefixWord, tailWord_1868082, baseEnd_1868082] using wordTrace_append hprefix tailTrace_1868082
  have hstable : (prefixWord ++ tailWord_1868082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868082).length < 2 ^ (prefixWord ++ tailWord_1868082).sum := by decide
  have hdescent : baseEnd_1868082 < baseStart_1868082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868140 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 3, 4]
def baseStart_1868140 : Nat := 118140960795 + 1868140 * 2 ^ 59
def prefixEnd_1868140 : Nat := 4983230072969 + 3 ^ 40 * 1868140 * 2
def baseEnd_1868140 : Nat := 639502499926950751572391

theorem tailTrace_1868140 : CollatzResearch.WordTrace tailWord_1868140 prefixEnd_1868140 639502499926950751572391 := by
  unfold tailWord_1868140
  simp only [CollatzResearch.WordTrace]
  refine ⟨34068331726027653878004937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45424442301370205170673249 34068331726027653878004937)
  ·
    refine ⟨25551248794520740408503703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34068331726027653878004937 25551248794520740408503703)
    ·
      refine ⟨38326873191781110612755555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25551248794520740408503703 38326873191781110612755555)
      ·
        refine ⟨57490309787671665919133333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38326873191781110612755555 57490309787671665919133333)
        ·
          refine ⟨2694858271297109339959375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57490309787671665919133333 2694858271297109339959375)
          ·
            refine ⟨4042287406945664009939063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2694858271297109339959375 4042287406945664009939063)
            ·
              refine ⟨6063431110418496014908595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4042287406945664009939063 6063431110418496014908595)
              ·
                refine ⟨9095146665627744022362893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6063431110418496014908595 9095146665627744022362893)
                ·
                  refine ⟨3410679999610404008386085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9095146665627744022362893 3410679999610404008386085)
                  ·
                    refine ⟨639502499926950751572391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3410679999610404008386085 639502499926950751572391)
                    ·
                      rfl

theorem cell22_1868140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_1868140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868140 prefixEnd_1868140 := by exact prefixLift 1868140
  have htrace : WordTrace (prefixWord ++ tailWord_1868140) baseStart_1868140 baseEnd_1868140 := by
    simpa [prefixWord, tailWord_1868140, baseEnd_1868140] using wordTrace_append hprefix tailTrace_1868140
  have hstable : (prefixWord ++ tailWord_1868140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868140).length < 2 ^ (prefixWord ++ tailWord_1868140).sum := by decide
  have hdescent : baseEnd_1868140 < baseStart_1868140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868157 : List Nat := [1, 4, 1, 1, 2, 4, 3, 1, 1, 4]
def baseStart_1868157 : Nat := 118140960795 + 1868157 * 2 ^ 59
def prefixEnd_1868157 : Nat := 4983230072969 + 3 ^ 40 * 1868157 * 2
def baseEnd_1868157 : Nat := 639508319374368373897339

theorem tailTrace_1868157 : CollatzResearch.WordTrace tailWord_1868157 prefixEnd_1868157 639508319374368373897339 := by
  unfold tailWord_1868157
  simp only [CollatzResearch.WordTrace]
  refine ⟨68137283492993719659378725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45424855661995813106252483 68137283492993719659378725)
  ·
    refine ⟨12775740654936322436133511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68137283492993719659378725 12775740654936322436133511)
    ·
      refine ⟨19163610982404483654200267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12775740654936322436133511 19163610982404483654200267)
      ·
        refine ⟨28745416473606725481300401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19163610982404483654200267 28745416473606725481300401)
        ·
          refine ⟨21559062355205044110975301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28745416473606725481300401 21559062355205044110975301)
          ·
            refine ⟨4042324191600945770807869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21559062355205044110975301 4042324191600945770807869)
            ·
              refine ⟨1515871571850354664052951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4042324191600945770807869 1515871571850354664052951)
              ·
                refine ⟨2273807357775531996079427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1515871571850354664052951 2273807357775531996079427)
                ·
                  refine ⟨3410711036663297994119141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2273807357775531996079427 3410711036663297994119141)
                  ·
                    refine ⟨639508319374368373897339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3410711036663297994119141 639508319374368373897339)
                    ·
                      rfl

theorem cell22_1868157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_1868157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868157 prefixEnd_1868157 := by exact prefixLift 1868157
  have htrace : WordTrace (prefixWord ++ tailWord_1868157) baseStart_1868157 baseEnd_1868157 := by
    simpa [prefixWord, tailWord_1868157, baseEnd_1868157] using wordTrace_append hprefix tailTrace_1868157
  have hstable : (prefixWord ++ tailWord_1868157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868157).length < 2 ^ (prefixWord ++ tailWord_1868157).sum := by decide
  have hdescent : baseEnd_1868157 < baseStart_1868157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868172 : List Nat := [2, 2, 1, 2, 1, 4, 4, 2, 4]
def baseStart_1868172 : Nat := 118140960795 + 1868172 * 2 ^ 59
def prefixEnd_1868172 : Nat := 4983230072969 + 3 ^ 40 * 1868172 * 2
def baseEnd_1868172 : Nat := 213171151393637778257431

theorem tailTrace_1868172 : CollatzResearch.WordTrace tailWord_1868172 prefixEnd_1868172 213171151393637778257431 := by
  unfold tailWord_1868172
  simp only [CollatzResearch.WordTrace]
  refine ⟨34068915293969688610587385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45425220391959584814116513 34068915293969688610587385)
  ·
    refine ⟨25551686470477266457940539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34068915293969688610587385 25551686470477266457940539)
    ·
      refine ⟨38327529705715899686910809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25551686470477266457940539 38327529705715899686910809)
      ·
        refine ⟨28745647279286924765183107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38327529705715899686910809 28745647279286924765183107)
        ·
          refine ⟨43118470918930387147774661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28745647279286924765183107 43118470918930387147774661)
          ·
            refine ⟨8084713297299447590207749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43118470918930387147774661 8084713297299447590207749)
            ·
              refine ⟨1515883743243646423163953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8084713297299447590207749 1515883743243646423163953)
              ·
                refine ⟨1136912807432734817372965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1515883743243646423163953 1136912807432734817372965)
                ·
                  refine ⟨213171151393637778257431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1136912807432734817372965 213171151393637778257431)
                  ·
                    rfl

theorem cell22_1868172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_1868172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868172 prefixEnd_1868172 := by exact prefixLift 1868172
  have htrace : WordTrace (prefixWord ++ tailWord_1868172) baseStart_1868172 baseEnd_1868172 := by
    simpa [prefixWord, tailWord_1868172, baseEnd_1868172] using wordTrace_append hprefix tailTrace_1868172
  have hstable : (prefixWord ++ tailWord_1868172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868172).length < 2 ^ (prefixWord ++ tailWord_1868172).sum := by decide
  have hdescent : baseEnd_1868172 < baseStart_1868172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868183 : List Nat := [1, 1, 3, 3, 1, 1, 5, 7]
def baseStart_1868183 : Nat := 118140960795 + 1868183 * 2 ^ 59
def prefixEnd_1868183 : Nat := 4983230072969 + 3 ^ 40 * 1868183 * 2
def baseEnd_1868183 : Nat := 71057468856190330305251

theorem tailTrace_1868183 : CollatzResearch.WordTrace tailWord_1868183 prefixEnd_1868183 71057468856190330305251 := by
  unfold tailWord_1868183
  simp only [CollatzResearch.WordTrace]
  refine ⟨68138231790899526099825203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45425487860599684066550135 68138231790899526099825203)
  ·
    refine ⟨102207347686349289149737805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68138231790899526099825203 102207347686349289149737805)
    ·
      refine ⟨38327755382380983431151677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102207347686349289149737805 38327755382380983431151677)
      ·
        refine ⟨14372908268392868786681879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38327755382380983431151677 14372908268392868786681879)
        ·
          refine ⟨21559362402589303180022819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14372908268392868786681879 21559362402589303180022819)
          ·
            refine ⟨32339043603883954770034229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21559362402589303180022819 32339043603883954770034229)
            ·
              refine ⟨3031785337864120759690709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32339043603883954770034229 3031785337864120759690709)
              ·
                refine ⟨71057468856190330305251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3031785337864120759690709 71057468856190330305251)
                ·
                  rfl

theorem cell22_1868183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 7].length) (baseStart_1868183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868183 prefixEnd_1868183 := by exact prefixLift 1868183
  have htrace : WordTrace (prefixWord ++ tailWord_1868183) baseStart_1868183 baseEnd_1868183 := by
    simpa [prefixWord, tailWord_1868183, baseEnd_1868183] using wordTrace_append hprefix tailTrace_1868183
  have hstable : (prefixWord ++ tailWord_1868183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868183).length < 2 ^ (prefixWord ++ tailWord_1868183).sum := by decide
  have hdescent : baseEnd_1868183 < baseStart_1868183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868232 : List Nat := [2, 1, 3, 1, 3, 3, 2, 1, 3, 3]
def baseStart_1868232 : Nat := 118140960795 + 1868232 * 2 ^ 59
def prefixEnd_1868232 : Nat := 4983230072969 + 3 ^ 40 * 1868232 * 2
def baseEnd_1868232 : Nat := 639533993407093178272109

theorem tailTrace_1868232 : CollatzResearch.WordTrace tailWord_1868232 prefixEnd_1868232 639533993407093178272109 := by
  unfold tailWord_1868232
  simp only [CollatzResearch.WordTrace]
  refine ⟨34070009483861003734179475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45426679311814671645572633 34070009483861003734179475)
  ·
    refine ⟨51105014225791505601269213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34070009483861003734179475 51105014225791505601269213)
    ·
      refine ⟨19164380334671814600475955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51105014225791505601269213 19164380334671814600475955)
      ·
        refine ⟨28746570502007721900713933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19164380334671814600475955 28746570502007721900713933)
        ·
          refine ⟨10779963938252895712767725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28746570502007721900713933 10779963938252895712767725)
          ·
            refine ⟨4042486476844835892287897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10779963938252895712767725 4042486476844835892287897)
            ·
              refine ⟨3031864857633626919215923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4042486476844835892287897 3031864857633626919215923)
              ·
                refine ⟨4547797286450440378823885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3031864857633626919215923 4547797286450440378823885)
                ·
                  refine ⟨1705423982418915142058957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4547797286450440378823885 1705423982418915142058957)
                  ·
                    refine ⟨639533993407093178272109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1705423982418915142058957 639533993407093178272109)
                    ·
                      rfl

theorem cell22_1868232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_1868232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868232 prefixEnd_1868232 := by exact prefixLift 1868232
  have htrace : WordTrace (prefixWord ++ tailWord_1868232) baseStart_1868232 baseEnd_1868232 := by
    simpa [prefixWord, tailWord_1868232, baseEnd_1868232] using wordTrace_append hprefix tailTrace_1868232
  have hstable : (prefixWord ++ tailWord_1868232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868232).length < 2 ^ (prefixWord ++ tailWord_1868232).sum := by decide
  have hdescent : baseEnd_1868232 < baseStart_1868232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868266 : List Nat := [3, 1, 3, 1, 3, 3, 1, 3, 1, 3]
def baseStart_1868266 : Nat := 118140960795 + 1868266 * 2 ^ 59
def prefixEnd_1868266 : Nat := 4983230072969 + 3 ^ 40 * 1868266 * 2
def baseEnd_1868266 : Nat := 639545632301928422922005

theorem tailTrace_1868266 : CollatzResearch.WordTrace tailWord_1868266 prefixEnd_1868266 639545632301928422922005 := by
  unfold tailWord_1868266
  simp only [CollatzResearch.WordTrace]
  refine ⟨17035314762399707818774163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45427506033065887516731101 17035314762399707818774163)
  ·
    refine ⟨25552972143599561728161245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17035314762399707818774163 25552972143599561728161245)
    ·
      refine ⟨9582364553849835648060467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25552972143599561728161245 9582364553849835648060467)
      ·
        refine ⟨14373546830774753472090701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9582364553849835648060467 14373546830774753472090701)
        ·
          refine ⟨5390080061540532552034013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14373546830774753472090701 5390080061540532552034013)
          ·
            refine ⟨2021280023077699707012755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5390080061540532552034013 2021280023077699707012755)
            ·
              refine ⟨3031920034616549560519133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2021280023077699707012755 3031920034616549560519133)
              ·
                refine ⟨1136970012981206085194675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3031920034616549560519133 1136970012981206085194675)
                ·
                  refine ⟨1705455019471809127792013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1136970012981206085194675 1705455019471809127792013)
                  ·
                    refine ⟨639545632301928422922005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1705455019471809127792013 639545632301928422922005)
                    ·
                      rfl

theorem cell22_1868266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_1868266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868266 prefixEnd_1868266 := by exact prefixLift 1868266
  have htrace : WordTrace (prefixWord ++ tailWord_1868266) baseStart_1868266 baseEnd_1868266 := by
    simpa [prefixWord, tailWord_1868266, baseEnd_1868266] using wordTrace_append hprefix tailTrace_1868266
  have hstable : (prefixWord ++ tailWord_1868266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868266).length < 2 ^ (prefixWord ++ tailWord_1868266).sum := by decide
  have hdescent : baseEnd_1868266 < baseStart_1868266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868275 : List Nat := [1, 1, 1, 2, 2, 2, 3, 5, 1, 4]
def baseStart_1868275 : Nat := 118140960795 + 1868275 * 2 ^ 59
def prefixEnd_1868275 : Nat := 4983230072969 + 3 ^ 40 * 1868275 * 2
def baseEnd_1868275 : Nat := 639548713185855399446977

theorem tailTrace_1868275 : CollatzResearch.WordTrace tailWord_1868275 prefixEnd_1868275 639548713185855399446977 := by
  unfold tailWord_1868275
  simp only [CollatzResearch.WordTrace]
  refine ⟨68141587306566225812174279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45427724871044150541449519 68141587306566225812174279)
  ·
    refine ⟨102212380959849338718261419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68141587306566225812174279 102212380959849338718261419)
    ·
      refine ⟨153318571439774008077392129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102212380959849338718261419 153318571439774008077392129)
      ·
        refine ⟨114988928579830506058044097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153318571439774008077392129 114988928579830506058044097)
        ·
          refine ⟨86241696434872879543533073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114988928579830506058044097 86241696434872879543533073)
          ·
            refine ⟨64681272326154659657649805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86241696434872879543533073 64681272326154659657649805)
            ·
              refine ⟨24255477122307997371618677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64681272326154659657649805 24255477122307997371618677)
              ·
                refine ⟨2273950980216374753589251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24255477122307997371618677 2273950980216374753589251)
                ·
                  refine ⟨3410926470324562130383877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2273950980216374753589251 3410926470324562130383877)
                  ·
                    refine ⟨639548713185855399446977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3410926470324562130383877 639548713185855399446977)
                    ·
                      rfl

theorem cell22_1868275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 4].length) (baseStart_1868275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868275 prefixEnd_1868275 := by exact prefixLift 1868275
  have htrace : WordTrace (prefixWord ++ tailWord_1868275) baseStart_1868275 baseEnd_1868275 := by
    simpa [prefixWord, tailWord_1868275, baseEnd_1868275] using wordTrace_append hprefix tailTrace_1868275
  have hstable : (prefixWord ++ tailWord_1868275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868275).length < 2 ^ (prefixWord ++ tailWord_1868275).sum := by decide
  have hdescent : baseEnd_1868275 < baseStart_1868275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868305 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 6, 3]
def baseStart_1868305 : Nat := 118140960795 + 1868305 * 2 ^ 59
def prefixEnd_1868305 : Nat := 4983230072969 + 3 ^ 40 * 1868305 * 2
def baseEnd_1868305 : Nat := 639558982798945321196885

theorem tailTrace_1868305 : CollatzResearch.WordTrace tailWord_1868305 prefixEnd_1868305 639558982798945321196885 := by
  unfold tailWord_1868305
  simp only [CollatzResearch.WordTrace]
  refine ⟨68142681496457540935766369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45428454330971693957177579 68142681496457540935766369)
  ·
    refine ⟨51107011122343155701824777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68142681496457540935766369 51107011122343155701824777)
    ·
      refine ⟨38330258341757366776368583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51107011122343155701824777 38330258341757366776368583)
      ·
        refine ⟨57495387512636050164552875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38330258341757366776368583 57495387512636050164552875)
        ·
          refine ⟨86243081268954075246829313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57495387512636050164552875 86243081268954075246829313)
          ·
            refine ⟨64682310951715556435121985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86243081268954075246829313 64682310951715556435121985)
            ·
              refine ⟨48511733213786667326341489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64682310951715556435121985 48511733213786667326341489)
              ·
                refine ⟨36383799910340000494756117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48511733213786667326341489 36383799910340000494756117)
                ·
                  refine ⟨1705490620797187523191693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36383799910340000494756117 1705490620797187523191693)
                  ·
                    refine ⟨639558982798945321196885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1705490620797187523191693 639558982798945321196885)
                    ·
                      rfl

theorem cell22_1868305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_1868305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868305 prefixEnd_1868305 := by exact prefixLift 1868305
  have htrace : WordTrace (prefixWord ++ tailWord_1868305) baseStart_1868305 baseEnd_1868305 := by
    simpa [prefixWord, tailWord_1868305, baseEnd_1868305] using wordTrace_append hprefix tailTrace_1868305
  have hstable : (prefixWord ++ tailWord_1868305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868305).length < 2 ^ (prefixWord ++ tailWord_1868305).sum := by decide
  have hdescent : baseEnd_1868305 < baseStart_1868305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868384 : List Nat := [2, 1, 1, 3, 2, 1, 3, 5, 1, 3]
def baseStart_1868384 : Nat := 118140960795 + 1868384 * 2 ^ 59
def prefixEnd_1868384 : Nat := 4983230072969 + 3 ^ 40 * 1868384 * 2
def baseEnd_1868384 : Nat := 639586026113415448471643

theorem tailTrace_1868384 : CollatzResearch.WordTrace tailWord_1868384 prefixEnd_1868384 639586026113415448471643 := by
  unfold tailWord_1868384
  simp only [CollatzResearch.WordTrace]
  refine ⟨34072781431585668713946103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45430375242114224951928137 34072781431585668713946103)
  ·
    refine ⟨51109172147378503070919155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34072781431585668713946103 51109172147378503070919155)
    ·
      refine ⟨76663758221067754606378733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51109172147378503070919155 76663758221067754606378733)
      ·
        refine ⟨28748909332900407977392025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76663758221067754606378733 28748909332900407977392025)
        ·
          refine ⟨21561681999675305983044019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28748909332900407977392025 21561681999675305983044019)
          ·
            refine ⟨32342522999512958974566029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21561681999675305983044019 32342522999512958974566029)
            ·
              refine ⟨12128446124817359615462261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32342522999512958974566029 12128446124817359615462261)
              ·
                refine ⟨1137041824201627463949587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12128446124817359615462261 1137041824201627463949587)
                ·
                  refine ⟨1705562736302441195924381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137041824201627463949587 1705562736302441195924381)
                  ·
                    refine ⟨639586026113415448471643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1705562736302441195924381 639586026113415448471643)
                    ·
                      rfl

theorem cell22_1868384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 1, 3].length) (baseStart_1868384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868384 prefixEnd_1868384 := by exact prefixLift 1868384
  have htrace : WordTrace (prefixWord ++ tailWord_1868384) baseStart_1868384 baseEnd_1868384 := by
    simpa [prefixWord, tailWord_1868384, baseEnd_1868384] using wordTrace_append hprefix tailTrace_1868384
  have hstable : (prefixWord ++ tailWord_1868384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868384).length < 2 ^ (prefixWord ++ tailWord_1868384).sum := by decide
  have hdescent : baseEnd_1868384 < baseStart_1868384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868397 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 7]
def baseStart_1868397 : Nat := 118140960795 + 1868397 * 2 ^ 59
def prefixEnd_1868397 : Nat := 4983230072969 + 3 ^ 40 * 1868397 * 2
def baseEnd_1868397 : Nat := 213196825426362582632201

theorem tailTrace_1868397 : CollatzResearch.WordTrace tailWord_1868397 prefixEnd_1868397 213196825426362582632201 := by
  unfold tailWord_1868397
  simp only [CollatzResearch.WordTrace]
  refine ⟨68146037012124240648115445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45430691341416160432076963 68146037012124240648115445)
  ·
    refine ⟨6388690969886647560760823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68146037012124240648115445 6388690969886647560760823)
    ·
      refine ⟨9583036454829971341141235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6388690969886647560760823 9583036454829971341141235)
      ·
        refine ⟨14374554682244957011711853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9583036454829971341141235 14374554682244957011711853)
        ·
          refine ⟨5390458005841858879391945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14374554682244957011711853 5390458005841858879391945)
          ·
            refine ⟨4042843504381394159543959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5390458005841858879391945 4042843504381394159543959)
            ·
              refine ⟨6064265256572091239315939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4042843504381394159543959 6064265256572091239315939)
              ·
                refine ⟨9096397884858136858973909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6064265256572091239315939 9096397884858136858973909)
                ·
                  refine ⟨213196825426362582632201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9096397884858136858973909 213196825426362582632201)
                  ·
                    rfl

theorem cell22_1868397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_1868397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868397 prefixEnd_1868397 := by exact prefixLift 1868397
  have htrace : WordTrace (prefixWord ++ tailWord_1868397) baseStart_1868397 baseEnd_1868397 := by
    simpa [prefixWord, tailWord_1868397, baseEnd_1868397] using wordTrace_append hprefix tailTrace_1868397
  have hstable : (prefixWord ++ tailWord_1868397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868397).length < 2 ^ (prefixWord ++ tailWord_1868397).sum := by decide
  have hdescent : baseEnd_1868397 < baseStart_1868397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868444 : List Nat := [2, 2, 3, 2, 2, 1, 2, 3, 1, 4]
def baseStart_1868444 : Nat := 118140960795 + 1868444 * 2 ^ 59
def prefixEnd_1868444 : Nat := 4983230072969 + 3 ^ 40 * 1868444 * 2
def baseEnd_1868444 : Nat := 639606565339595291971459

theorem tailTrace_1868444 : CollatzResearch.WordTrace tailWord_1868444 prefixEnd_1868444 639606565339595291971459 := by
  unfold tailWord_1868444
  simp only [CollatzResearch.WordTrace]
  refine ⟨34073875621476983837538193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45431834161969311783384257 34073875621476983837538193)
  ·
    refine ⟨25555406716107737878153645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34073875621476983837538193 25555406716107737878153645)
    ·
      refine ⟨9583277518540401704307617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25555406716107737878153645 9583277518540401704307617)
      ·
        refine ⟨7187458138905301278230713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9583277518540401704307617 7187458138905301278230713)
        ·
          refine ⟨5390593604178975958673035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7187458138905301278230713 5390593604178975958673035)
          ·
            refine ⟨8085890406268463938009553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5390593604178975958673035 8085890406268463938009553)
            ·
              refine ⟨6064417804701347953507165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8085890406268463938009553 6064417804701347953507165)
              ·
                refine ⟨2274156676763005482565187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6064417804701347953507165 2274156676763005482565187)
                ·
                  refine ⟨3411235015144508223847781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274156676763005482565187 3411235015144508223847781)
                  ·
                    refine ⟨639606565339595291971459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3411235015144508223847781 639606565339595291971459)
                    ·
                      rfl

theorem cell22_1868444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_1868444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868444 prefixEnd_1868444 := by exact prefixLift 1868444
  have htrace : WordTrace (prefixWord ++ tailWord_1868444) baseStart_1868444 baseEnd_1868444 := by
    simpa [prefixWord, tailWord_1868444, baseEnd_1868444] using wordTrace_append hprefix tailTrace_1868444
  have hstable : (prefixWord ++ tailWord_1868444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868444).length < 2 ^ (prefixWord ++ tailWord_1868444).sum := by decide
  have hdescent : baseEnd_1868444 < baseStart_1868444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868474 : List Nat := [3, 1, 1, 1, 2, 3, 3, 3, 2, 3]
def baseStart_1868474 : Nat := 118140960795 + 1868474 * 2 ^ 59
def prefixEnd_1868474 : Nat := 4983230072969 + 3 ^ 40 * 1868474 * 2
def baseEnd_1868474 : Nat := 639616834952685213721367

theorem tailTrace_1868474 : CollatzResearch.WordTrace tailWord_1868474 prefixEnd_1868474 639616834952685213721367 := by
  unfold tailWord_1868474
  simp only [CollatzResearch.WordTrace]
  refine ⟨17037211358211320699667119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45432563621896855199112317 17037211358211320699667119)
  ·
    refine ⟨25555817037316981049500679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17037211358211320699667119 25555817037316981049500679)
    ·
      refine ⟨38333725555975471574251019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25555817037316981049500679 38333725555975471574251019)
      ·
        refine ⟨57500588333963207361376529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38333725555975471574251019 57500588333963207361376529)
        ·
          refine ⟨43125441250472405521032397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57500588333963207361376529 43125441250472405521032397)
          ·
            refine ⟨16172040468927152070387149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43125441250472405521032397 16172040468927152070387149)
            ·
              refine ⟨6064515175847682026395181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16172040468927152070387149 6064515175847682026395181)
              ·
                refine ⟨2274193190942880759898193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6064515175847682026395181 2274193190942880759898193)
                ·
                  refine ⟨1705644893207160569923645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2274193190942880759898193 1705644893207160569923645)
                  ·
                    refine ⟨639616834952685213721367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1705644893207160569923645 639616834952685213721367)
                    ·
                      rfl

theorem cell22_1868474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_1868474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868474 prefixEnd_1868474 := by exact prefixLift 1868474
  have htrace : WordTrace (prefixWord ++ tailWord_1868474) baseStart_1868474 baseEnd_1868474 := by
    simpa [prefixWord, tailWord_1868474, baseEnd_1868474] using wordTrace_append hprefix tailTrace_1868474
  have hstable : (prefixWord ++ tailWord_1868474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868474).length < 2 ^ (prefixWord ++ tailWord_1868474).sum := by decide
  have hdescent : baseEnd_1868474 < baseStart_1868474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868508 : List Nat := [2, 2, 5, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1868508 : Nat := 118140960795 + 1868508 * 2 ^ 59
def prefixEnd_1868508 : Nat := 4983230072969 + 3 ^ 40 * 1868508 * 2
def baseEnd_1868508 : Nat := 639628473847520458371263

theorem tailTrace_1868508 : CollatzResearch.WordTrace tailWord_1868508 prefixEnd_1868508 639628473847520458371263 := by
  unfold tailWord_1868508
  simp only [CollatzResearch.WordTrace]
  refine ⟨34075042757361053302703089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45433390343148071070270785 34075042757361053302703089)
  ·
    refine ⟨25556282068020789977027317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34075042757361053302703089 25556282068020789977027317)
    ·
      refine ⟨2395901443876949060346311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25556282068020789977027317 2395901443876949060346311)
      ·
        refine ⟨3593852165815423590519467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2395901443876949060346311 3593852165815423590519467)
        ·
          refine ⟨5390778248723135385779201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3593852165815423590519467 5390778248723135385779201)
          ·
            refine ⟨4043083686542351539334401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5390778248723135385779201 4043083686542351539334401)
            ·
              refine ⟨3032312764906763654500801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4043083686542351539334401 3032312764906763654500801)
              ·
                refine ⟨2274234573680072740875601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3032312764906763654500801 2274234573680072740875601)
                ·
                  refine ⟨1705675930260054555656701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2274234573680072740875601 1705675930260054555656701)
                  ·
                    refine ⟨639628473847520458371263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1705675930260054555656701 639628473847520458371263)
                    ·
                      rfl

theorem cell22_1868508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1868508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868508 prefixEnd_1868508 := by exact prefixLift 1868508
  have htrace : WordTrace (prefixWord ++ tailWord_1868508) baseStart_1868508 baseEnd_1868508 := by
    simpa [prefixWord, tailWord_1868508, baseEnd_1868508] using wordTrace_append hprefix tailTrace_1868508
  have hstable : (prefixWord ++ tailWord_1868508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868508).length < 2 ^ (prefixWord ++ tailWord_1868508).sum := by decide
  have hdescent : baseEnd_1868508 < baseStart_1868508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868517 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 2, 6]
def baseStart_1868517 : Nat := 118140960795 + 1868517 * 2 ^ 59
def prefixEnd_1868517 : Nat := 4983230072969 + 3 ^ 40 * 1868517 * 2
def baseEnd_1868517 : Nat := 639631554731447434896235

theorem tailTrace_1868517 : CollatzResearch.WordTrace tailWord_1868517 prefixEnd_1868517 639631554731447434896235 := by
  unfold tailWord_1868517
  simp only [CollatzResearch.WordTrace]
  refine ⟨68150413771689501142483805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45433609181126334094989203 68150413771689501142483805)
  ·
    refine ⟨25556405164383562928431427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68150413771689501142483805 25556405164383562928431427)
    ·
      refine ⟨38334607746575344392647141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25556405164383562928431427 38334607746575344392647141)
      ·
        refine ⟨7187738952482877073621339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38334607746575344392647141 7187738952482877073621339)
        ·
          refine ⟨10781608428724315610432009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7187738952482877073621339 10781608428724315610432009)
          ·
            refine ⟨8086206321543236707824007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10781608428724315610432009 8086206321543236707824007)
            ·
              refine ⟨12129309482314855061736011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8086206321543236707824007 12129309482314855061736011)
              ·
                refine ⟨18193964223472282592604017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12129309482314855061736011 18193964223472282592604017)
                ·
                  refine ⟨13645473167604211944453013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18193964223472282592604017 13645473167604211944453013)
                  ·
                    refine ⟨639631554731447434896235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13645473167604211944453013 639631554731447434896235)
                    ·
                      rfl

theorem cell22_1868517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_1868517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868517 prefixEnd_1868517 := by exact prefixLift 1868517
  have htrace : WordTrace (prefixWord ++ tailWord_1868517) baseStart_1868517 baseEnd_1868517 := by
    simpa [prefixWord, tailWord_1868517, baseEnd_1868517] using wordTrace_append hprefix tailTrace_1868517
  have hstable : (prefixWord ++ tailWord_1868517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868517).length < 2 ^ (prefixWord ++ tailWord_1868517).sum := by decide
  have hdescent : baseEnd_1868517 < baseStart_1868517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868626 : List Nat := [3, 2, 2, 1, 1, 2, 2, 4, 2, 3]
def baseStart_1868626 : Nat := 118140960795 + 1868626 * 2 ^ 59
def prefixEnd_1868626 : Nat := 4983230072969 + 3 ^ 40 * 1868626 * 2
def baseEnd_1868626 : Nat := 639668867659007483920901

theorem tailTrace_1868626 : CollatzResearch.WordTrace tailWord_1868626 prefixEnd_1868626 639668867659007483920901 := by
  unfold tailWord_1868626
  simp only [CollatzResearch.WordTrace]
  refine ⟨17038597332073653189550433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45436259552196408505467821 17038597332073653189550433)
  ·
    refine ⟨12778947999055239892162825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17038597332073653189550433 12778947999055239892162825)
    ·
      refine ⟨9584210999291429919122119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12778947999055239892162825 9584210999291429919122119)
      ·
        refine ⟨14376316498937144878683179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9584210999291429919122119 14376316498937144878683179)
        ·
          refine ⟨21564474748405717318024769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14376316498937144878683179 21564474748405717318024769)
          ·
            refine ⟨16173356061304287988518577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21564474748405717318024769 16173356061304287988518577)
            ·
              refine ⟨12130017045978215991388933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16173356061304287988518577 12130017045978215991388933)
              ·
                refine ⟨2274378196120915498385425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12130017045978215991388933 2274378196120915498385425)
                ·
                  refine ⟨1705783647090686623789069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2274378196120915498385425 1705783647090686623789069)
                  ·
                    refine ⟨639668867659007483920901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1705783647090686623789069 639668867659007483920901)
                    ·
                      rfl

theorem cell22_1868626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_1868626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868626 prefixEnd_1868626 := by exact prefixLift 1868626
  have htrace : WordTrace (prefixWord ++ tailWord_1868626) baseStart_1868626 baseEnd_1868626 := by
    simpa [prefixWord, tailWord_1868626, baseEnd_1868626] using wordTrace_append hprefix tailTrace_1868626
  have hstable : (prefixWord ++ tailWord_1868626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868626).length < 2 ^ (prefixWord ++ tailWord_1868626).sum := by decide
  have hdescent : baseEnd_1868626 < baseStart_1868626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868628 : List Nat := [2, 4, 1, 1, 5, 1, 1, 1, 6]
def baseStart_1868628 : Nat := 118140960795 + 1868628 * 2 ^ 59
def prefixEnd_1868628 : Nat := 4983230072969 + 3 ^ 40 * 1868628 * 2
def baseEnd_1868628 : Nat := 213223184099960048456965

theorem tailTrace_1868628 : CollatzResearch.WordTrace tailWord_1868628 prefixEnd_1868628 213223184099960048456965 := by
  unfold tailWord_1868628
  simp only [CollatzResearch.WordTrace]
  refine ⟨34077231137143683549887269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45436308182858244733183025 34077231137143683549887269)
  ·
    refine ⟨6389480838214440665603863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34077231137143683549887269 6389480838214440665603863)
    ·
      refine ⟨9584221257321660998405795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6389480838214440665603863 9584221257321660998405795)
      ·
        refine ⟨14376331885982491497608693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9584221257321660998405795 14376331885982491497608693)
        ·
          refine ⟨1347781114310858577900815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14376331885982491497608693 1347781114310858577900815)
          ·
            refine ⟨2021671671466287866851223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347781114310858577900815 2021671671466287866851223)
            ·
              refine ⟨3032507507199431800276835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2021671671466287866851223 3032507507199431800276835)
              ·
                refine ⟨4548761260799147700415253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3032507507199431800276835 4548761260799147700415253)
                ·
                  refine ⟨213223184099960048456965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4548761260799147700415253 213223184099960048456965)
                  ·
                    rfl

theorem cell22_1868628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_1868628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868628 prefixEnd_1868628 := by exact prefixLift 1868628
  have htrace : WordTrace (prefixWord ++ tailWord_1868628) baseStart_1868628 baseEnd_1868628 := by
    simpa [prefixWord, tailWord_1868628, baseEnd_1868628] using wordTrace_append hprefix tailTrace_1868628
  have hstable : (prefixWord ++ tailWord_1868628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868628).length < 2 ^ (prefixWord ++ tailWord_1868628).sum := by decide
  have hdescent : baseEnd_1868628 < baseStart_1868628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868643 : List Nat := [1, 1, 1, 5, 3, 1, 4, 1, 2, 3]
def baseStart_1868643 : Nat := 118140960795 + 1868643 * 2 ^ 59
def prefixEnd_1868643 : Nat := 4983230072969 + 3 ^ 40 * 1868643 * 2
def baseEnd_1868643 : Nat := 639674687106425106245849

theorem tailTrace_1868643 : CollatzResearch.WordTrace tailWord_1868643 prefixEnd_1868643 639674687106425106245849 := by
  unfold tailWord_1868643
  simp only [CollatzResearch.WordTrace]
  refine ⟨68155009369233024661570583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45436672912822016441047055 68155009369233024661570583)
  ·
    refine ⟨102232514053849536992355875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68155009369233024661570583 102232514053849536992355875)
    ·
      refine ⟨153348771080774305488533813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102232514053849536992355875 153348771080774305488533813)
      ·
        refine ⟨14376447288822591139550045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153348771080774305488533813 14376447288822591139550045)
        ·
          refine ⟨5391167733308471677331267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14376447288822591139550045 5391167733308471677331267)
          ·
            refine ⟨8086751599962707515996901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5391167733308471677331267 8086751599962707515996901)
            ·
              refine ⟨1516265924993007659249419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8086751599962707515996901 1516265924993007659249419)
              ·
                refine ⟨2274398887489511488874129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516265924993007659249419 2274398887489511488874129)
                ·
                  refine ⟨1705799165617133616655597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2274398887489511488874129 1705799165617133616655597)
                  ·
                    refine ⟨639674687106425106245849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1705799165617133616655597 639674687106425106245849)
                    ·
                      rfl

theorem cell22_1868643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 2, 3].length) (baseStart_1868643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868643 prefixEnd_1868643 := by exact prefixLift 1868643
  have htrace : WordTrace (prefixWord ++ tailWord_1868643) baseStart_1868643 baseEnd_1868643 := by
    simpa [prefixWord, tailWord_1868643, baseEnd_1868643] using wordTrace_append hprefix tailTrace_1868643
  have hstable : (prefixWord ++ tailWord_1868643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868643).length < 2 ^ (prefixWord ++ tailWord_1868643).sum := by decide
  have hdescent : baseEnd_1868643 < baseStart_1868643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868667 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 9]
def baseStart_1868667 : Nat := 118140960795 + 1868667 * 2 ^ 59
def prefixEnd_1868667 : Nat := 4983230072969 + 3 ^ 40 * 1868667 * 2
def baseEnd_1868667 : Nat := 213227634265632347881925

theorem tailTrace_1868667 : CollatzResearch.WordTrace tailWord_1868667 prefixEnd_1868667 213227634265632347881925 := by
  unfold tailWord_1868667
  simp only [CollatzResearch.WordTrace]
  refine ⟨68155884721146076760444255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45437256480764051173629503 68155884721146076760444255)
  ·
    refine ⟨102233827081719115140666383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68155884721146076760444255 102233827081719115140666383)
    ·
      refine ⟨153350740622578672710999575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102233827081719115140666383 153350740622578672710999575)
      ·
        refine ⟨230026110933868009066499363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153350740622578672710999575 230026110933868009066499363)
        ·
          refine ⟨345039166400802013599749045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230026110933868009066499363 345039166400802013599749045)
          ·
            refine ⟨32347421850075188774976473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 345039166400802013599749045 32347421850075188774976473)
            ·
              refine ⟨24260566387556391581232355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32347421850075188774976473 24260566387556391581232355)
              ·
                refine ⟨36390849581334587371848533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24260566387556391581232355 36390849581334587371848533)
                ·
                  refine ⟨213227634265632347881925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36390849581334587371848533 213227634265632347881925)
                  ·
                    rfl

theorem cell22_1868667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 9].length) (baseStart_1868667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868667 prefixEnd_1868667 := by exact prefixLift 1868667
  have htrace : WordTrace (prefixWord ++ tailWord_1868667) baseStart_1868667 baseEnd_1868667 := by
    simpa [prefixWord, tailWord_1868667, baseEnd_1868667] using wordTrace_append hprefix tailTrace_1868667
  have hstable : (prefixWord ++ tailWord_1868667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868667).length < 2 ^ (prefixWord ++ tailWord_1868667).sum := by decide
  have hdescent : baseEnd_1868667 < baseStart_1868667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868684 : List Nat := [2, 2, 1, 2, 1, 2, 3, 4, 5]
def baseStart_1868684 : Nat := 118140960795 + 1868684 * 2 ^ 59
def prefixEnd_1868684 : Nat := 4983230072969 + 3 ^ 40 * 1868684 * 2
def baseEnd_1868684 : Nat := 213229574081438221990241

theorem tailTrace_1868684 : CollatzResearch.WordTrace tailWord_1868684 prefixEnd_1868684 213229574081438221990241 := by
  unfold tailWord_1868684
  simp only [CollatzResearch.WordTrace]
  refine ⟨34078252381042244331906553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45437669841389659109208737 34078252381042244331906553)
  ·
    refine ⟨25558689285781683248929915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34078252381042244331906553 25558689285781683248929915)
    ·
      refine ⟨38338033928672524873394873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25558689285781683248929915 38338033928672524873394873)
      ·
        refine ⟨28753525446504393655046155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38338033928672524873394873 28753525446504393655046155)
        ·
          refine ⟨43130288169756590482569233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28753525446504393655046155 43130288169756590482569233)
          ·
            refine ⟨32347716127317442861926925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43130288169756590482569233 32347716127317442861926925)
            ·
              refine ⟨12130393547744041073222597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32347716127317442861926925 12130393547744041073222597)
              ·
                refine ⟨2274448790202007701229237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12130393547744041073222597 2274448790202007701229237)
                ·
                  refine ⟨213229574081438221990241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2274448790202007701229237 213229574081438221990241)
                  ·
                    rfl

theorem cell22_1868684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_1868684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868684 prefixEnd_1868684 := by exact prefixLift 1868684
  have htrace : WordTrace (prefixWord ++ tailWord_1868684) baseStart_1868684 baseEnd_1868684 := by
    simpa [prefixWord, tailWord_1868684, baseEnd_1868684] using wordTrace_append hprefix tailTrace_1868684
  have hstable : (prefixWord ++ tailWord_1868684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868684).length < 2 ^ (prefixWord ++ tailWord_1868684).sum := by decide
  have hdescent : baseEnd_1868684 < baseStart_1868684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868759 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 6, 4]
def baseStart_1868759 : Nat := 118140960795 + 1868759 * 2 ^ 59
def prefixEnd_1868759 : Nat := 4983230072969 + 3 ^ 40 * 1868759 * 2
def baseEnd_1868759 : Nat := 639714396277039470345493

theorem tailTrace_1868759 : CollatzResearch.WordTrace tailWord_1868759 prefixEnd_1868759 639714396277039470345493 := by
  unfold tailWord_1868759
  simp only [CollatzResearch.WordTrace]
  refine ⟨68159240236812776472793331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45439493491208517648528887 68159240236812776472793331)
  ·
    refine ⟨102238860355219164709189997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68159240236812776472793331 102238860355219164709189997)
    ·
      refine ⟨38339572633207186765946249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102238860355219164709189997 38339572633207186765946249)
      ·
        refine ⟨28754679474905390074459687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38339572633207186765946249 28754679474905390074459687)
        ·
          refine ⟨43132019212358085111689531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28754679474905390074459687 43132019212358085111689531)
          ·
            refine ⟨64698028818537127667534297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43132019212358085111689531 64698028818537127667534297)
            ·
              refine ⟨48523521613902845750650723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64698028818537127667534297 48523521613902845750650723)
              ·
                refine ⟨72785282420854268625976085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48523521613902845750650723 72785282420854268625976085)
                ·
                  refine ⟨3411810113477543841842629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72785282420854268625976085 3411810113477543841842629)
                  ·
                    refine ⟨639714396277039470345493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3411810113477543841842629 639714396277039470345493)
                    ·
                      rfl

theorem cell22_1868759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_1868759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868759 prefixEnd_1868759 := by exact prefixLift 1868759
  have htrace : WordTrace (prefixWord ++ tailWord_1868759) baseStart_1868759 baseEnd_1868759 := by
    simpa [prefixWord, tailWord_1868759, baseEnd_1868759] using wordTrace_append hprefix tailTrace_1868759
  have hstable : (prefixWord ++ tailWord_1868759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868759).length < 2 ^ (prefixWord ++ tailWord_1868759).sum := by decide
  have hdescent : baseEnd_1868759 < baseStart_1868759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868761 : List Nat := [1, 2, 1, 2, 5, 1, 3, 1, 1, 5]
def baseStart_1868761 : Nat := 118140960795 + 1868761 * 2 ^ 59
def prefixEnd_1868761 : Nat := 4983230072969 + 3 ^ 40 * 1868761 * 2
def baseEnd_1868761 : Nat := 639715080917912131795487

theorem tailTrace_1868761 : CollatzResearch.WordTrace tailWord_1868761 prefixEnd_1868761 639715080917912131795487 := by
  unfold tailWord_1868761
  simp only [CollatzResearch.WordTrace]
  refine ⟨68159313182805530814366137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45439542121870353876244091 68159313182805530814366137)
  ·
    refine ⟨51119484887104148110774603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68159313182805530814366137 51119484887104148110774603)
    ·
      refine ⟨76679227330656222166161905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51119484887104148110774603 76679227330656222166161905)
      ·
        refine ⟨57509420497992166624621429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76679227330656222166161905 57509420497992166624621429)
        ·
          refine ⟨5391508171686765621058259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57509420497992166624621429 5391508171686765621058259)
          ·
            refine ⟨8087262257530148431587389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5391508171686765621058259 8087262257530148431587389)
            ·
              refine ⟨3032723346573805661845271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8087262257530148431587389 3032723346573805661845271)
              ·
                refine ⟨4549085019860708492767907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3032723346573805661845271 4549085019860708492767907)
                ·
                  refine ⟨6823627529791062739151861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4549085019860708492767907 6823627529791062739151861)
                  ·
                    refine ⟨639715080917912131795487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6823627529791062739151861 639715080917912131795487)
                    ·
                      rfl

theorem cell22_1868761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 5].length) (baseStart_1868761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868761 prefixEnd_1868761 := by exact prefixLift 1868761
  have htrace : WordTrace (prefixWord ++ tailWord_1868761) baseStart_1868761 baseEnd_1868761 := by
    simpa [prefixWord, tailWord_1868761, baseEnd_1868761] using wordTrace_append hprefix tailTrace_1868761
  have hstable : (prefixWord ++ tailWord_1868761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868761).length < 2 ^ (prefixWord ++ tailWord_1868761).sum := by decide
  have hdescent : baseEnd_1868761 < baseStart_1868761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868857 : List Nat := [1, 2, 1, 5, 2, 1, 4, 2, 1, 3]
def baseStart_1868857 : Nat := 118140960795 + 1868857 * 2 ^ 59
def prefixEnd_1868857 : Nat := 4983230072969 + 3 ^ 40 * 1868857 * 2
def baseEnd_1868857 : Nat := 639747943679799881395193

theorem tailTrace_1868857 : CollatzResearch.WordTrace tailWord_1868857 prefixEnd_1868857 639747943679799881395193 := by
  unfold tailWord_1868857
  simp only [CollatzResearch.WordTrace]
  refine ⟨68162814590457739209860825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45441876393638492806573883 68162814590457739209860825)
  ·
    refine ⟨51122110942843304407395619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68162814590457739209860825 51122110942843304407395619)
    ·
      refine ⟨76683166414264956611093429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51122110942843304407395619 76683166414264956611093429)
      ·
        refine ⟨7189046851337339682290009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76683166414264956611093429 7189046851337339682290009)
        ·
          refine ⟨5391785138503004761717507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7189046851337339682290009 5391785138503004761717507)
          ·
            refine ⟨8087677707754507142576261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5391785138503004761717507 8087677707754507142576261)
            ·
              refine ⟨1516439570203970089233049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8087677707754507142576261 1516439570203970089233049)
              ·
                refine ⟨1137329677652977566924787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1516439570203970089233049 1137329677652977566924787)
                ·
                  refine ⟨1705994516479466350387181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137329677652977566924787 1705994516479466350387181)
                  ·
                    refine ⟨639747943679799881395193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1705994516479466350387181 639747943679799881395193)
                    ·
                      rfl

theorem cell22_1868857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 1, 3].length) (baseStart_1868857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868857 prefixEnd_1868857 := by exact prefixLift 1868857
  have htrace : WordTrace (prefixWord ++ tailWord_1868857) baseStart_1868857 baseEnd_1868857 := by
    simpa [prefixWord, tailWord_1868857, baseEnd_1868857] using wordTrace_append hprefix tailTrace_1868857
  have hstable : (prefixWord ++ tailWord_1868857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868857).length < 2 ^ (prefixWord ++ tailWord_1868857).sum := by decide
  have hdescent : baseEnd_1868857 < baseStart_1868857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868870 : List Nat := [6, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_1868870 : Nat := 118140960795 + 1868870 * 2 ^ 59
def prefixEnd_1868870 : Nat := 4983230072969 + 3 ^ 40 * 1868870 * 2
def baseEnd_1868870 : Nat := 213250797948490726940051

theorem tailTrace_1868870 : CollatzResearch.WordTrace tailWord_1868870 prefixEnd_1868870 213250797948490726940051 := by
  unfold tailWord_1868870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2130102773106582575940127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45442192492940428286722709 2130102773106582575940127)
  ·
    refine ⟨3195154159659873863910191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2130102773106582575940127 3195154159659873863910191)
    ·
      refine ⟨4792731239489810795865287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3195154159659873863910191 4792731239489810795865287)
      ·
        refine ⟨7189096859234716193797931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4792731239489810795865287 7189096859234716193797931)
        ·
          refine ⟨10783645288852074290696897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7189096859234716193797931 10783645288852074290696897)
          ·
            refine ⟨8087733966639055718022673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10783645288852074290696897 8087733966639055718022673)
            ·
              refine ⟨6065800474979291788517005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8087733966639055718022673 6065800474979291788517005)
              ·
                refine ⟨2274675178117234420693877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6065800474979291788517005 2274675178117234420693877)
                ·
                  refine ⟨213250797948490726940051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2274675178117234420693877 213250797948490726940051)
                  ·
                    rfl

theorem cell22_1868870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_1868870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868870 prefixEnd_1868870 := by exact prefixLift 1868870
  have htrace : WordTrace (prefixWord ++ tailWord_1868870) baseStart_1868870 baseEnd_1868870 := by
    simpa [prefixWord, tailWord_1868870, baseEnd_1868870] using wordTrace_append hprefix tailTrace_1868870
  have hstable : (prefixWord ++ tailWord_1868870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868870).length < 2 ^ (prefixWord ++ tailWord_1868870).sum := by decide
  have hdescent : baseEnd_1868870 < baseStart_1868870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868896 : List Nat := [2, 1, 1, 3, 2, 2, 1, 4, 1, 5]
def baseStart_1868896 : Nat := 118140960795 + 1868896 * 2 ^ 59
def prefixEnd_1868896 : Nat := 4983230072969 + 3 ^ 40 * 1868896 * 2
def baseEnd_1868896 : Nat := 639761294176816779670073

theorem tailTrace_1868896 : CollatzResearch.WordTrace tailWord_1868896 prefixEnd_1868896 639761294176816779670073 := by
  unfold tailWord_1868896
  simp only [CollatzResearch.WordTrace]
  refine ⟨34082118518658224435265271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45442824691544299247020361 34082118518658224435265271)
  ·
    refine ⟨51123177777987336652897907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34082118518658224435265271 51123177777987336652897907)
    ·
      refine ⟨76684766666981004979346861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51123177777987336652897907 76684766666981004979346861)
      ·
        refine ⟨28756787500117876867255073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76684766666981004979346861 28756787500117876867255073)
        ·
          refine ⟨21567590625088407650441305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28756787500117876867255073 21567590625088407650441305)
          ·
            refine ⟨16175692968816305737830979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21567590625088407650441305 16175692968816305737830979)
            ·
              refine ⟨24263539453224458606746469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16175692968816305737830979 24263539453224458606746469)
              ·
                refine ⟨4549413647479585988764963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24263539453224458606746469 4549413647479585988764963)
                ·
                  refine ⟨6824120471219378983147445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4549413647479585988764963 6824120471219378983147445)
                  ·
                    refine ⟨639761294176816779670073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6824120471219378983147445 639761294176816779670073)
                    ·
                      rfl

theorem cell22_1868896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_1868896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868896 prefixEnd_1868896 := by exact prefixLift 1868896
  have htrace : WordTrace (prefixWord ++ tailWord_1868896) baseStart_1868896 baseEnd_1868896 := by
    simpa [prefixWord, tailWord_1868896, baseEnd_1868896] using wordTrace_append hprefix tailTrace_1868896
  have hstable : (prefixWord ++ tailWord_1868896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868896).length < 2 ^ (prefixWord ++ tailWord_1868896).sum := by decide
  have hdescent : baseEnd_1868896 < baseStart_1868896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868911 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 4, 4]
def baseStart_1868911 : Nat := 118140960795 + 1868911 * 2 ^ 59
def prefixEnd_1868911 : Nat := 4983230072969 + 3 ^ 40 * 1868911 * 2
def baseEnd_1868911 : Nat := 639766428983361740545027

theorem tailTrace_1868911 : CollatzResearch.WordTrace tailWord_1868911 prefixEnd_1868911 639766428983361740545027 := by
  unfold tailWord_1868911
  simp only [CollatzResearch.WordTrace]
  refine ⟨68164784132262106432326587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45443189421508070954884391 68164784132262106432326587)
  ·
    refine ⟨102247176198393159648489881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68164784132262106432326587 102247176198393159648489881)
    ·
      refine ⟨76685382148794869736367411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102247176198393159648489881 76685382148794869736367411)
      ·
        refine ⟨115028073223192304604551117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76685382148794869736367411 115028073223192304604551117)
        ·
          refine ⟨43135527458697114226706669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115028073223192304604551117 43135527458697114226706669)
          ·
            refine ⟨16175822797011417835015001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43135527458697114226706669 16175822797011417835015001)
            ·
              refine ⟨12131867097758563376261251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16175822797011417835015001 12131867097758563376261251)
              ·
                refine ⟨18197800646637845064391877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12131867097758563376261251 18197800646637845064391877)
                ·
                  refine ⟨3412087621244595949573477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18197800646637845064391877 3412087621244595949573477)
                  ·
                    refine ⟨639766428983361740545027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3412087621244595949573477 639766428983361740545027)
                    ·
                      rfl

theorem cell22_1868911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_1868911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868911 prefixEnd_1868911 := by exact prefixLift 1868911
  have htrace : WordTrace (prefixWord ++ tailWord_1868911) baseStart_1868911 baseEnd_1868911 := by
    simpa [prefixWord, tailWord_1868911, baseEnd_1868911] using wordTrace_append hprefix tailTrace_1868911
  have hstable : (prefixWord ++ tailWord_1868911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868911).length < 2 ^ (prefixWord ++ tailWord_1868911).sum := by decide
  have hdescent : baseEnd_1868911 < baseStart_1868911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868913 : List Nat := [1, 2, 2, 2, 1, 1, 2, 6, 2, 3]
def baseStart_1868913 : Nat := 118140960795 + 1868913 * 2 ^ 59
def prefixEnd_1868913 : Nat := 4983230072969 + 3 ^ 40 * 1868913 * 2
def baseEnd_1868913 : Nat := 639767113624234401995021

theorem tailTrace_1868913 : CollatzResearch.WordTrace tailWord_1868913 prefixEnd_1868913 639767113624234401995021 := by
  unfold tailWord_1868913
  simp only [CollatzResearch.WordTrace]
  refine ⟨68164857078254860773899393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45443238052169907182599595 68164857078254860773899393)
  ·
    refine ⟨51123642808691145580424545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68164857078254860773899393 51123642808691145580424545)
    ·
      refine ⟨38342732106518359185318409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51123642808691145580424545 38342732106518359185318409)
      ·
        refine ⟨28757049079888769388988807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38342732106518359185318409 28757049079888769388988807)
        ·
          refine ⟨43135573619833154083483211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28757049079888769388988807 43135573619833154083483211)
          ·
            refine ⟨64703360429749731125224817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43135573619833154083483211 64703360429749731125224817)
            ·
              refine ⟨48527520322312298343918613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64703360429749731125224817 48527520322312298343918613)
              ·
                refine ⟨2274727515108388984871185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48527520322312298343918613 2274727515108388984871185)
                ·
                  refine ⟨1706045636331291738653389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2274727515108388984871185 1706045636331291738653389)
                  ·
                    refine ⟨639767113624234401995021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1706045636331291738653389 639767113624234401995021)
                    ·
                      rfl

theorem cell22_1868913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_1868913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868913 prefixEnd_1868913 := by exact prefixLift 1868913
  have htrace : WordTrace (prefixWord ++ tailWord_1868913) baseStart_1868913 baseEnd_1868913 := by
    simpa [prefixWord, tailWord_1868913, baseEnd_1868913] using wordTrace_append hprefix tailTrace_1868913
  have hstable : (prefixWord ++ tailWord_1868913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868913).length < 2 ^ (prefixWord ++ tailWord_1868913).sum := by decide
  have hdescent : baseEnd_1868913 < baseStart_1868913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868975 : List Nat := [1, 1, 2, 1, 2, 3, 2, 6, 1, 3]
def baseStart_1868975 : Nat := 118140960795 + 1868975 * 2 ^ 59
def prefixEnd_1868975 : Nat := 4983230072969 + 3 ^ 40 * 1868975 * 2
def baseEnd_1868975 : Nat := 639788337491286906944831

theorem tailTrace_1868975 : CollatzResearch.WordTrace tailWord_1868975 prefixEnd_1868975 639788337491286906944831 := by
  unfold tailWord_1868975
  simp only [CollatzResearch.WordTrace]
  refine ⟨68167118404030245362656379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45444745602686830241770919 68167118404030245362656379)
  ·
    refine ⟨102250677606045368043984569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68167118404030245362656379 102250677606045368043984569)
    ·
      refine ⟨76688008204534026032988427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102250677606045368043984569 76688008204534026032988427)
      ·
        refine ⟨115032012306801039049482641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76688008204534026032988427 115032012306801039049482641)
        ·
          refine ⟨86274009230100779287111981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115032012306801039049482641 86274009230100779287111981)
          ·
            refine ⟨32352753461287792232666993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86274009230100779287111981 32352753461287792232666993)
            ·
              refine ⟨24264565095965844174500245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32352753461287792232666993 24264565095965844174500245)
              ·
                refine ⟨1137401488873398945679699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24264565095965844174500245 1137401488873398945679699)
                ·
                  refine ⟨1706102233310098418519549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137401488873398945679699 1706102233310098418519549)
                  ·
                    refine ⟨639788337491286906944831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1706102233310098418519549 639788337491286906944831)
                    ·
                      rfl

theorem cell22_1868975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 1, 3].length) (baseStart_1868975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868975 prefixEnd_1868975 := by exact prefixLift 1868975
  have htrace : WordTrace (prefixWord ++ tailWord_1868975) baseStart_1868975 baseEnd_1868975 := by
    simpa [prefixWord, tailWord_1868975, baseEnd_1868975] using wordTrace_append hprefix tailTrace_1868975
  have hstable : (prefixWord ++ tailWord_1868975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868975).length < 2 ^ (prefixWord ++ tailWord_1868975).sum := by decide
  have hdescent : baseEnd_1868975 < baseStart_1868975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868986 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 1, 7]
def baseStart_1868986 : Nat := 118140960795 + 1868986 * 2 ^ 59
def prefixEnd_1868986 : Nat := 4983230072969 + 3 ^ 40 * 1868986 * 2
def baseEnd_1868986 : Nat := 639792103016086544919797

theorem tailTrace_1868986 : CollatzResearch.WordTrace tailWord_1868986 prefixEnd_1868986 639792103016086544919797 := by
  unfold tailWord_1868986
  simp only [CollatzResearch.WordTrace]
  refine ⟨17041879901747598560326703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45445013071326929494204541 17041879901747598560326703)
  ·
    refine ⟨25562819852621397840490055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17041879901747598560326703 25562819852621397840490055)
    ·
      refine ⟨38344229778932096760735083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25562819852621397840490055 38344229778932096760735083)
      ·
        refine ⟨57516344668398145141102625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38344229778932096760735083 57516344668398145141102625)
        ·
          refine ⟨43137258501298608855826969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57516344668398145141102625 43137258501298608855826969)
          ·
            refine ⟨32352943875973956641870227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43137258501298608855826969 32352943875973956641870227)
            ·
              refine ⟨48529415813960934962805341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32352943875973956641870227 48529415813960934962805341)
              ·
                refine ⟨18198530930235350611052003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48529415813960934962805341 18198530930235350611052003)
                ·
                  refine ⟨27297796395353025916578005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18198530930235350611052003 27297796395353025916578005)
                  ·
                    refine ⟨639792103016086544919797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27297796395353025916578005 639792103016086544919797)
                    ·
                      rfl

theorem cell22_1868986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_1868986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1868986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1868986 prefixEnd_1868986 := by exact prefixLift 1868986
  have htrace : WordTrace (prefixWord ++ tailWord_1868986) baseStart_1868986 baseEnd_1868986 := by
    simpa [prefixWord, tailWord_1868986, baseEnd_1868986] using wordTrace_append hprefix tailTrace_1868986
  have hstable : (prefixWord ++ tailWord_1868986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868986).length < 2 ^ (prefixWord ++ tailWord_1868986).sum := by decide
  have hdescent : baseEnd_1868986 < baseStart_1868986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869048 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 8, 3]
def baseStart_1869048 : Nat := 118140960795 + 1869048 * 2 ^ 59
def prefixEnd_1869048 : Nat := 4983230072969 + 3 ^ 40 * 1869048 * 2
def baseEnd_1869048 : Nat := 639813326883139049869607

theorem tailTrace_1869048 : CollatzResearch.WordTrace tailWord_1869048 prefixEnd_1869048 639813326883139049869607 := by
  unfold tailWord_1869048
  simp only [CollatzResearch.WordTrace]
  refine ⟨34084890466382889415031899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45446520621843852553375865 34084890466382889415031899)
  ·
    refine ⟨51127335699574334122547849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34084890466382889415031899 51127335699574334122547849)
    ·
      refine ⟨38345501774680750591910887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51127335699574334122547849 38345501774680750591910887)
      ·
        refine ⟨57518252662021125887866331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38345501774680750591910887 57518252662021125887866331)
        ·
          refine ⟨86277378993031688831799497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57518252662021125887866331 86277378993031688831799497)
          ·
            refine ⟨64708034244773766623849623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86277378993031688831799497 64708034244773766623849623)
            ·
              refine ⟨97062051367160649935774435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64708034244773766623849623 97062051367160649935774435)
              ·
                refine ⟨145593077050740974903661653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97062051367160649935774435 145593077050740974903661653)
                ·
                  refine ⟨1706168871688370799652285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 145593077050740974903661653 1706168871688370799652285)
                  ·
                    refine ⟨639813326883139049869607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1706168871688370799652285 639813326883139049869607)
                    ·
                      rfl

theorem cell22_1869048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_1869048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869048 prefixEnd_1869048 := by exact prefixLift 1869048
  have htrace : WordTrace (prefixWord ++ tailWord_1869048) baseStart_1869048 baseEnd_1869048 := by
    simpa [prefixWord, tailWord_1869048, baseEnd_1869048] using wordTrace_append hprefix tailTrace_1869048
  have hstable : (prefixWord ++ tailWord_1869048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869048).length < 2 ^ (prefixWord ++ tailWord_1869048).sum := by decide
  have hdescent : baseEnd_1869048 < baseStart_1869048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869082 : List Nat := [3, 1, 1, 3, 3, 1, 3, 2, 2, 3]
def baseStart_1869082 : Nat := 118140960795 + 1869082 * 2 ^ 59
def prefixEnd_1869082 : Nat := 4983230072969 + 3 ^ 40 * 1869082 * 2
def baseEnd_1869082 : Nat := 639824965777974294519503

theorem tailTrace_1869082 : CollatzResearch.WordTrace tailWord_1869082 prefixEnd_1869082 639824965777974294519503 := by
  unfold tailWord_1869082
  simp only [CollatzResearch.WordTrace]
  refine ⟨17042755253660650659200375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45447347343095068424534333 17042755253660650659200375)
  ·
    refine ⟨25564132880490975988800563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17042755253660650659200375 25564132880490975988800563)
    ·
      refine ⟨38346199320736463983200845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25564132880490975988800563 38346199320736463983200845)
      ·
        refine ⟨14379824745276173993700317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38346199320736463983200845 14379824745276173993700317)
        ·
          refine ⟨5392434279478565247637619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14379824745276173993700317 5392434279478565247637619)
          ·
            refine ⟨8088651419217847871456429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5392434279478565247637619 8088651419217847871456429)
            ·
              refine ⟨3033244282206692951796161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8088651419217847871456429 3033244282206692951796161)
              ·
                refine ⟨2274933211655019713847121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3033244282206692951796161 2274933211655019713847121)
                ·
                  refine ⟨1706199908741264785385341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2274933211655019713847121 1706199908741264785385341)
                  ·
                    refine ⟨639824965777974294519503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1706199908741264785385341 639824965777974294519503)
                    ·
                      rfl

theorem cell22_1869082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_1869082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869082 prefixEnd_1869082 := by exact prefixLift 1869082
  have htrace : WordTrace (prefixWord ++ tailWord_1869082) baseStart_1869082 baseEnd_1869082 := by
    simpa [prefixWord, tailWord_1869082, baseEnd_1869082] using wordTrace_append hprefix tailTrace_1869082
  have hstable : (prefixWord ++ tailWord_1869082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869082).length < 2 ^ (prefixWord ++ tailWord_1869082).sum := by decide
  have hdescent : baseEnd_1869082 < baseStart_1869082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869140 : List Nat := [2, 4, 1, 1, 2, 1, 2, 4, 5]
def baseStart_1869140 : Nat := 118140960795 + 1869140 * 2 ^ 59
def prefixEnd_1869140 : Nat := 4983230072969 + 3 ^ 40 * 1869140 * 2
def baseEnd_1869140 : Nat := 213281606787760492189775

theorem tailTrace_1869140 : CollatzResearch.WordTrace tailWord_1869140 prefixEnd_1869140 213281606787760492189775 := by
  unfold tailWord_1869140
  simp only [CollatzResearch.WordTrace]
  refine ⟨34086568224216239271206437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45448757632288319028275249 34086568224216239271206437)
  ·
    refine ⟨6391231542040544863351207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34086568224216239271206437 6391231542040544863351207)
    ·
      refine ⟨9586847313060817295026811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6391231542040544863351207 9586847313060817295026811)
      ·
        refine ⟨14380270969591225942540217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9586847313060817295026811 14380270969591225942540217)
        ·
          refine ⟨10785203227193419456905163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14380270969591225942540217 10785203227193419456905163)
          ·
            refine ⟨16177804840790129185357745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10785203227193419456905163 16177804840790129185357745)
            ·
              refine ⟨12133353630592596889018309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16177804840790129185357745 12133353630592596889018309)
              ·
                refine ⟨2275003805736111916690933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12133353630592596889018309 2275003805736111916690933)
                ·
                  refine ⟨213281606787760492189775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2275003805736111916690933 213281606787760492189775)
                  ·
                    rfl

theorem cell22_1869140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_1869140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869140 prefixEnd_1869140 := by exact prefixLift 1869140
  have htrace : WordTrace (prefixWord ++ tailWord_1869140) baseStart_1869140 baseEnd_1869140 := by
    simpa [prefixWord, tailWord_1869140, baseEnd_1869140] using wordTrace_append hprefix tailTrace_1869140
  have hstable : (prefixWord ++ tailWord_1869140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869140).length < 2 ^ (prefixWord ++ tailWord_1869140).sum := by decide
  have hdescent : baseEnd_1869140 < baseStart_1869140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869144 : List Nat := [2, 1, 2, 2, 1, 1, 7, 2, 1, 3]
def baseStart_1869144 : Nat := 118140960795 + 1869144 * 2 ^ 59
def prefixEnd_1869144 : Nat := 4983230072969 + 3 ^ 40 * 1869144 * 2
def baseEnd_1869144 : Nat := 639846189645026799469313

theorem tailTrace_1869144 : CollatzResearch.WordTrace tailWord_1869144 prefixEnd_1869144 639846189645026799469313 := by
  unfold tailWord_1869144
  simp only [CollatzResearch.WordTrace]
  refine ⟨34086641170208993612779243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45448854893611991483705657 34086641170208993612779243)
  ·
    refine ⟨51129961755313490419168865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34086641170208993612779243 51129961755313490419168865)
    ·
      refine ⟨38347471316485117814376649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51129961755313490419168865 38347471316485117814376649)
      ·
        refine ⟨28760603487363838360782487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38347471316485117814376649 28760603487363838360782487)
        ·
          refine ⟨43140905231045757541173731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28760603487363838360782487 43140905231045757541173731)
          ·
            refine ⟨64711357846568636311760597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43140905231045757541173731 64711357846568636311760597)
            ·
              refine ⟨1516672449528952413556889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 64711357846568636311760597 1516672449528952413556889)
              ·
                refine ⟨1137504337146714310167667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1516672449528952413556889 1137504337146714310167667)
                ·
                  refine ⟨1706256505720071465251501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137504337146714310167667 1706256505720071465251501)
                  ·
                    refine ⟨639846189645026799469313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1706256505720071465251501 639846189645026799469313)
                    ·
                      rfl

theorem cell22_1869144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 1, 3].length) (baseStart_1869144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869144 prefixEnd_1869144 := by exact prefixLift 1869144
  have htrace : WordTrace (prefixWord ++ tailWord_1869144) baseStart_1869144 baseEnd_1869144 := by
    simpa [prefixWord, tailWord_1869144, baseEnd_1869144] using wordTrace_append hprefix tailTrace_1869144
  have hstable : (prefixWord ++ tailWord_1869144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869144).length < 2 ^ (prefixWord ++ tailWord_1869144).sum := by decide
  have hdescent : baseEnd_1869144 < baseStart_1869144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869168 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 8]
def baseStart_1869168 : Nat := 118140960795 + 1869168 * 2 ^ 59
def prefixEnd_1869168 : Nat := 4983230072969 + 3 ^ 40 * 1869168 * 2
def baseEnd_1869168 : Nat := 213284801778499578956413

theorem tailTrace_1869168 : CollatzResearch.WordTrace tailWord_1869168 prefixEnd_1869168 213284801778499578956413 := by
  unfold tailWord_1869168
  simp only [CollatzResearch.WordTrace]
  refine ⟨34087078846165519662216079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45449438461554026216288105 34087078846165519662216079)
  ·
    refine ⟨51130618269248279493324119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34087078846165519662216079 51130618269248279493324119)
    ·
      refine ⟨76695927403872419239986179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51130618269248279493324119 76695927403872419239986179)
      ·
        refine ⟨115043891105808628859979269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76695927403872419239986179 115043891105808628859979269)
        ·
          refine ⟨21570729582339117911246113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115043891105808628859979269 21570729582339117911246113)
          ·
            refine ⟨16178047186754338433434585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21570729582339117911246113 16178047186754338433434585)
            ·
              refine ⟨12133535390065753825075939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16178047186754338433434585 12133535390065753825075939)
              ·
                refine ⟨18200303085098630737613909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12133535390065753825075939 18200303085098630737613909)
                ·
                  refine ⟨213284801778499578956413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18200303085098630737613909 213284801778499578956413)
                  ·
                    rfl

theorem cell22_1869168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 8].length) (baseStart_1869168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869168 prefixEnd_1869168 := by exact prefixLift 1869168
  have htrace : WordTrace (prefixWord ++ tailWord_1869168) baseStart_1869168 baseEnd_1869168 := by
    simpa [prefixWord, tailWord_1869168, baseEnd_1869168] using wordTrace_append hprefix tailTrace_1869168
  have hstable : (prefixWord ++ tailWord_1869168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869168).length < 2 ^ (prefixWord ++ tailWord_1869168).sum := by decide
  have hdescent : baseEnd_1869168 < baseStart_1869168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869170 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_1869170 : Nat := 118140960795 + 1869170 * 2 ^ 59
def prefixEnd_1869170 : Nat := 4983230072969 + 3 ^ 40 * 1869170 * 2
def baseEnd_1869170 : Nat := 639855089976371398319233

theorem tailTrace_1869170 : CollatzResearch.WordTrace tailWord_1869170 prefixEnd_1869170 639855089976371398319233 := by
  unfold tailWord_1869170
  simp only [CollatzResearch.WordTrace]
  refine ⟨17043557659580948416501241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45449487092215862444003309 17043557659580948416501241)
  ·
    refine ⟨12782668244685711312375931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17043557659580948416501241 12782668244685711312375931)
    ·
      refine ⟨19174002367028566968563897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12782668244685711312375931 19174002367028566968563897)
      ·
        refine ⟨14380501775271425226422923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19174002367028566968563897 14380501775271425226422923)
        ·
          refine ⟨21570752662907137839634385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14380501775271425226422923 21570752662907137839634385)
          ·
            refine ⟨16178064497180353379725789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21570752662907137839634385 16178064497180353379725789)
            ·
              refine ⟨6066774186442632517397171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16178064497180353379725789 6066774186442632517397171)
              ·
                refine ⟨9100161279663948776095757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6066774186442632517397171 9100161279663948776095757)
                ·
                  refine ⟨3412560479873980791035909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9100161279663948776095757 3412560479873980791035909)
                  ·
                    refine ⟨639855089976371398319233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3412560479873980791035909 639855089976371398319233)
                    ·
                      rfl

theorem cell22_1869170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_1869170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869170 prefixEnd_1869170 := by exact prefixLift 1869170
  have htrace : WordTrace (prefixWord ++ tailWord_1869170) baseStart_1869170 baseEnd_1869170 := by
    simpa [prefixWord, tailWord_1869170, baseEnd_1869170] using wordTrace_append hprefix tailTrace_1869170
  have hstable : (prefixWord ++ tailWord_1869170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869170).length < 2 ^ (prefixWord ++ tailWord_1869170).sum := by decide
  have hdescent : baseEnd_1869170 < baseStart_1869170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869262 : List Nat := [4, 1, 1, 1, 2, 1, 3, 3, 3, 3]
def baseStart_1869262 : Nat := 118140960795 + 1869262 * 2 ^ 59
def prefixEnd_1869262 : Nat := 4983230072969 + 3 ^ 40 * 1869262 * 2
def baseEnd_1869262 : Nat := 639886583456513825018951

theorem tailTrace_1869262 : CollatzResearch.WordTrace tailWord_1869262 prefixEnd_1869262 639886583456513825018951 := by
  unfold tailWord_1869262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8522198269248811672294255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45451724102660328918902693 8522198269248811672294255)
  ·
    refine ⟨12783297403873217508441383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8522198269248811672294255 12783297403873217508441383)
    ·
      refine ⟨19174946105809826262662075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12783297403873217508441383 19174946105809826262662075)
      ·
        refine ⟨28762419158714739393993113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19174946105809826262662075 28762419158714739393993113)
        ·
          refine ⟨21571814369036054545494835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28762419158714739393993113 21571814369036054545494835)
          ·
            refine ⟨32357721553554081818242253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21571814369036054545494835 32357721553554081818242253)
            ·
              refine ⟨12134145582582780681840845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32357721553554081818242253 12134145582582780681840845)
              ·
                refine ⟨4550304593468542755690317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12134145582582780681840845 4550304593468542755690317)
                ·
                  refine ⟨1706364222550703533383869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4550304593468542755690317 1706364222550703533383869)
                  ·
                    refine ⟨639886583456513825018951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1706364222550703533383869 639886583456513825018951)
                    ·
                      rfl

theorem cell22_1869262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_1869262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869262 prefixEnd_1869262 := by exact prefixLift 1869262
  have htrace : WordTrace (prefixWord ++ tailWord_1869262) baseStart_1869262 baseEnd_1869262 := by
    simpa [prefixWord, tailWord_1869262, baseEnd_1869262] using wordTrace_append hprefix tailTrace_1869262
  have hstable : (prefixWord ++ tailWord_1869262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869262).length < 2 ^ (prefixWord ++ tailWord_1869262).sum := by decide
  have hdescent : baseEnd_1869262 < baseStart_1869262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869296 : List Nat := [2, 1, 1, 1, 3, 6, 1, 3, 1, 3]
def baseStart_1869296 : Nat := 118140960795 + 1869296 * 2 ^ 59
def prefixEnd_1869296 : Nat := 4983230072969 + 3 ^ 40 * 1869296 * 2
def baseEnd_1869296 : Nat := 639898222351349069668847

theorem tailTrace_1869296 : CollatzResearch.WordTrace tailWord_1869296 prefixEnd_1869296 639898222351349069668847 := by
  unfold tailWord_1869296
  simp only [CollatzResearch.WordTrace]
  refine ⟨34089413117933658592545871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45452550823911544790061161 34089413117933658592545871)
  ·
    refine ⟨51134119676900487888818807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34089413117933658592545871 51134119676900487888818807)
    ·
      refine ⟨76701179515350731833228211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51134119676900487888818807 76701179515350731833228211)
      ·
        refine ⟨115051769273026097749842317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76701179515350731833228211 115051769273026097749842317)
        ·
          refine ⟨43144413477384786656190869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115051769273026097749842317 43144413477384786656190869)
          ·
            refine ⟨2022394381752411874508947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43144413477384786656190869 2022394381752411874508947)
            ·
              refine ⟨3033591572628617811763421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2022394381752411874508947 3033591572628617811763421)
              ·
                refine ⟨1137596839735731679411283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3033591572628617811763421 1137596839735731679411283)
                ·
                  refine ⟨1706395259603597519116925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137596839735731679411283 1706395259603597519116925)
                  ·
                    refine ⟨639898222351349069668847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1706395259603597519116925 639898222351349069668847)
                    ·
                      rfl

theorem cell22_1869296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 1, 3].length) (baseStart_1869296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869296 prefixEnd_1869296 := by exact prefixLift 1869296
  have htrace : WordTrace (prefixWord ++ tailWord_1869296) baseStart_1869296 baseEnd_1869296 := by
    simpa [prefixWord, tailWord_1869296, baseEnd_1869296] using wordTrace_append hprefix tailTrace_1869296
  have hstable : (prefixWord ++ tailWord_1869296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869296).length < 2 ^ (prefixWord ++ tailWord_1869296).sum := by decide
  have hdescent : baseEnd_1869296 < baseStart_1869296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869305 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 5, 4]
def baseStart_1869305 : Nat := 118140960795 + 1869305 * 2 ^ 59
def prefixEnd_1869305 : Nat := 4983230072969 + 3 ^ 40 * 1869305 * 2
def baseEnd_1869305 : Nat := 639901303235276046193819

theorem tailTrace_1869305 : CollatzResearch.WordTrace tailWord_1869305 prefixEnd_1869305 639901303235276046193819 := by
  unfold tailWord_1869305
  simp only [CollatzResearch.WordTrace]
  refine ⟨68179154492834711722169369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45452769661889807814779579 68179154492834711722169369)
  ·
    refine ⟨51134365869626033791627027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68179154492834711722169369 51134365869626033791627027)
    ·
      refine ⟨76701548804439050687440541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51134365869626033791627027 76701548804439050687440541)
      ·
        refine ⟨28763080801664644007790203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76701548804439050687440541 28763080801664644007790203)
        ·
          refine ⟨43144621202496966011685305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28763080801664644007790203 43144621202496966011685305)
          ·
            refine ⟨32358465901872724508763979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43144621202496966011685305 32358465901872724508763979)
            ·
              refine ⟨48537698852809086763145969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32358465901872724508763979 48537698852809086763145969)
              ·
                refine ⟨36403274139606815072359477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48537698852809086763145969 36403274139606815072359477)
                ·
                  refine ⟨3412806950588138913033701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36403274139606815072359477 3412806950588138913033701)
                  ·
                    refine ⟨639901303235276046193819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3412806950588138913033701 639901303235276046193819)
                    ·
                      rfl

theorem cell22_1869305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_1869305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869305 prefixEnd_1869305 := by exact prefixLift 1869305
  have htrace : WordTrace (prefixWord ++ tailWord_1869305) baseStart_1869305 baseEnd_1869305 := by
    simpa [prefixWord, tailWord_1869305, baseEnd_1869305] using wordTrace_append hprefix tailTrace_1869305
  have hstable : (prefixWord ++ tailWord_1869305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869305).length < 2 ^ (prefixWord ++ tailWord_1869305).sum := by decide
  have hdescent : baseEnd_1869305 < baseStart_1869305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869313 : List Nat := [1, 2, 4, 1, 4, 1, 3, 2, 1, 3]
def baseStart_1869313 : Nat := 118140960795 + 1869313 * 2 ^ 59
def prefixEnd_1869313 : Nat := 4983230072969 + 3 ^ 40 * 1869313 * 2
def baseEnd_1869313 : Nat := 639904041798766691993795

theorem tailTrace_1869313 : CollatzResearch.WordTrace tailWord_1869313 prefixEnd_1869313 639904041798766691993795 := by
  unfold tailWord_1869313
  simp only [CollatzResearch.WordTrace]
  refine ⟨68179446276805729088460593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45452964184537152725640395 68179446276805729088460593)
  ·
    refine ⟨51134584707604296816345445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68179446276805729088460593 51134584707604296816345445)
    ·
      refine ⟨9587734632675805653064771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51134584707604296816345445 9587734632675805653064771)
      ·
        refine ⟨14381601949013708479597157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9587734632675805653064771 14381601949013708479597157)
        ·
          refine ⟨2696550365440070339924467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14381601949013708479597157 2696550365440070339924467)
          ·
            refine ⟨4044825548160105509886701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2696550365440070339924467 4044825548160105509886701)
            ·
              refine ⟨1516809580560039566207513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4044825548160105509886701 1516809580560039566207513)
              ·
                refine ⟨1137607185420029674655635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1516809580560039566207513 1137607185420029674655635)
                ·
                  refine ⟨1706410778130044511983453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137607185420029674655635 1706410778130044511983453)
                  ·
                    refine ⟨639904041798766691993795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1706410778130044511983453 639904041798766691993795)
                    ·
                      rfl

theorem cell22_1869313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_1869313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869313 prefixEnd_1869313 := by exact prefixLift 1869313
  have htrace : WordTrace (prefixWord ++ tailWord_1869313) baseStart_1869313 baseEnd_1869313 := by
    simpa [prefixWord, tailWord_1869313, baseEnd_1869313] using wordTrace_append hprefix tailTrace_1869313
  have hstable : (prefixWord ++ tailWord_1869313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869313).length < 2 ^ (prefixWord ++ tailWord_1869313).sum := by decide
  have hdescent : baseEnd_1869313 < baseStart_1869313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869326 : List Nat := [4, 1, 1, 2, 4, 2, 2, 1, 5]
def baseStart_1869326 : Nat := 118140960795 + 1869326 * 2 ^ 59
def prefixEnd_1869326 : Nat := 4983230072969 + 3 ^ 40 * 1869326 * 2
def baseEnd_1869326 : Nat := 213302830654812997139585

theorem tailTrace_1869326 : CollatzResearch.WordTrace tailWord_1869326 prefixEnd_1869326 213302830654812997139585 := by
  unfold tailWord_1869326
  simp only [CollatzResearch.WordTrace]
  refine ⟨8522490053219829038585479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45453280283839088205789221 8522490053219829038585479)
  ·
    refine ⟨12783735079829743557878219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8522490053219829038585479 12783735079829743557878219)
    ·
      refine ⟨19175602619744615336817329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12783735079829743557878219 19175602619744615336817329)
      ·
        refine ⟨14381701964808461502612997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19175602619744615336817329 14381701964808461502612997)
        ·
          refine ⟨2696569118401586531739937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14381701964808461502612997 2696569118401586531739937)
          ·
            refine ⟨2022426838801189898804953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2696569118401586531739937 2022426838801189898804953)
            ·
              refine ⟨1516820129100892424103715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2022426838801189898804953 1516820129100892424103715)
              ·
                refine ⟨2275230193651338636155573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516820129100892424103715 2275230193651338636155573)
                ·
                  refine ⟨213302830654812997139585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2275230193651338636155573 213302830654812997139585)
                  ·
                    rfl

theorem cell22_1869326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_1869326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869326 prefixEnd_1869326 := by exact prefixLift 1869326
  have htrace : WordTrace (prefixWord ++ tailWord_1869326) baseStart_1869326 baseEnd_1869326 := by
    simpa [prefixWord, tailWord_1869326, baseEnd_1869326] using wordTrace_append hprefix tailTrace_1869326
  have hstable : (prefixWord ++ tailWord_1869326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869326).length < 2 ^ (prefixWord ++ tailWord_1869326).sum := by decide
  have hdescent : baseEnd_1869326 < baseStart_1869326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869354 : List Nat := [3, 1, 4, 1, 1, 1, 2, 5, 4]
def baseStart_1869354 : Nat := 118140960795 + 1869354 * 2 ^ 59
def prefixEnd_1869354 : Nat := 4983230072969 + 3 ^ 40 * 1869354 * 2
def baseEnd_1869354 : Nat := 213306025645552083906223

theorem tailTrace_1869354 : CollatzResearch.WordTrace tailWord_1869354 prefixEnd_1869354 213306025645552083906223 := by
  unfold tailWord_1869354
  simp only [CollatzResearch.WordTrace]
  refine ⟨17045235417414298272675779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45453961113104795393802077 17045235417414298272675779)
  ·
    refine ⟨25567853126121447409013669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17045235417414298272675779 25567853126121447409013669)
    ·
      refine ⟨4793972461147771389190063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25567853126121447409013669 4793972461147771389190063)
      ·
        refine ⟨7190958691721657083785095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4793972461147771389190063 7190958691721657083785095)
        ·
          refine ⟨10786438037582485625677643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7190958691721657083785095 10786438037582485625677643)
          ·
            refine ⟨16179657056373728438516465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10786438037582485625677643 16179657056373728438516465)
            ·
              refine ⟨12134742792280296328887349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16179657056373728438516465 12134742792280296328887349)
              ·
                refine ⟨1137632136776277780833189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12134742792280296328887349 1137632136776277780833189)
                ·
                  refine ⟨213306025645552083906223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1137632136776277780833189 213306025645552083906223)
                  ·
                    rfl

theorem cell22_1869354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_1869354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869354 prefixEnd_1869354 := by exact prefixLift 1869354
  have htrace : WordTrace (prefixWord ++ tailWord_1869354) baseStart_1869354 baseEnd_1869354 := by
    simpa [prefixWord, tailWord_1869354, baseEnd_1869354] using wordTrace_append hprefix tailTrace_1869354
  have hstable : (prefixWord ++ tailWord_1869354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869354).length < 2 ^ (prefixWord ++ tailWord_1869354).sum := by decide
  have hdescent : baseEnd_1869354 < baseStart_1869354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869365 : List Nat := [1, 3, 3, 1, 1, 13]
def baseStart_1869365 : Nat := 118140960795 + 1869365 * 2 ^ 59
def prefixEnd_1869365 : Nat := 4983230072969 + 3 ^ 40 * 1869365 * 2
def baseEnd_1869365 : Nat := 7900269660017973946835

theorem tailTrace_1869365 : CollatzResearch.WordTrace tailWord_1869365 prefixEnd_1869365 7900269660017973946835 := by
  unfold tailWord_1869365
  simp only [CollatzResearch.WordTrace]
  refine ⟨68181342872617341969353549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45454228581744894646235699 68181342872617341969353549)
  ·
    refine ⟨25568003577231503238507581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68181342872617341969353549 25568003577231503238507581)
    ·
      refine ⟨9588001341461813714440343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25568003577231503238507581 9588001341461813714440343)
      ·
        refine ⟨14382002012192720571660515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9588001341461813714440343 14382002012192720571660515)
        ·
          refine ⟨21573003018289080857490773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14382002012192720571660515 21573003018289080857490773)
          ·
            refine ⟨7900269660017973946835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 21573003018289080857490773 7900269660017973946835)
            ·
              rfl

theorem cell22_1869365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 13].length) (baseStart_1869365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869365 prefixEnd_1869365 := by exact prefixLift 1869365
  have htrace : WordTrace (prefixWord ++ tailWord_1869365) baseStart_1869365 baseEnd_1869365 := by
    simpa [prefixWord, tailWord_1869365, baseEnd_1869365] using wordTrace_append hprefix tailTrace_1869365
  have hstable : (prefixWord ++ tailWord_1869365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869365).length < 2 ^ (prefixWord ++ tailWord_1869365).sum := by decide
  have hdescent : baseEnd_1869365 < baseStart_1869365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869367 : List Nat := [1, 1, 3, 1, 2, 4, 2, 2, 2, 4]
def baseStart_1869367 : Nat := 118140960795 + 1869367 * 2 ^ 59
def prefixEnd_1869367 : Nat := 4983230072969 + 3 ^ 40 * 1869367 * 2
def baseEnd_1869367 : Nat := 639922527102328551143629

theorem tailTrace_1869367 : CollatzResearch.WordTrace tailWord_1869367 prefixEnd_1869367 639922527102328551143629 := by
  unfold tailWord_1869367
  simp only [CollatzResearch.WordTrace]
  refine ⟨68181415818610096310926355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45454277212406730873950903 68181415818610096310926355)
  ·
    refine ⟨102272123727915144466389533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68181415818610096310926355 102272123727915144466389533)
    ·
      refine ⟨38352046397968179174896075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102272123727915144466389533 38352046397968179174896075)
      ·
        refine ⟨57528069596952268762344113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38352046397968179174896075 57528069596952268762344113)
        ·
          refine ⟨43146052197714201571758085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57528069596952268762344113 43146052197714201571758085)
          ·
            refine ⟨8089884787071412794704641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43146052197714201571758085 8089884787071412794704641)
            ·
              refine ⟨6067413590303559596028481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8089884787071412794704641 6067413590303559596028481)
              ·
                refine ⟨4550560192727669697021361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6067413590303559596028481 4550560192727669697021361)
                ·
                  refine ⟨3412920144545752272766021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4550560192727669697021361 3412920144545752272766021)
                  ·
                    refine ⟨639922527102328551143629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3412920144545752272766021 639922527102328551143629)
                    ·
                      rfl

theorem cell22_1869367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_1869367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869367 prefixEnd_1869367 := by exact prefixLift 1869367
  have htrace : WordTrace (prefixWord ++ tailWord_1869367) baseStart_1869367 baseEnd_1869367 := by
    simpa [prefixWord, tailWord_1869367, baseEnd_1869367] using wordTrace_append hprefix tailTrace_1869367
  have hstable : (prefixWord ++ tailWord_1869367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869367).length < 2 ^ (prefixWord ++ tailWord_1869367).sum := by decide
  have hdescent : baseEnd_1869367 < baseStart_1869367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869369 : List Nat := [1, 2, 1, 5, 1, 2, 1, 4, 2, 3]
def baseStart_1869369 : Nat := 118140960795 + 1869369 * 2 ^ 59
def prefixEnd_1869369 : Nat := 4983230072969 + 3 ^ 40 * 1869369 * 2
def baseEnd_1869369 : Nat := 639923211743201212593623

theorem tailTrace_1869369 : CollatzResearch.WordTrace tailWord_1869369 prefixEnd_1869369 639923211743201212593623 := by
  unfold tailWord_1869369
  simp only [CollatzResearch.WordTrace]
  refine ⟨68181488764602850652499161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45454325843068567101666107 68181488764602850652499161)
  ·
    refine ⟨51136116573452137989374371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68181488764602850652499161 51136116573452137989374371)
    ·
      refine ⟨76704174860178206984061557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51136116573452137989374371 76704174860178206984061557)
      ·
        refine ⟨7191016393141706904755771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76704174860178206984061557 7191016393141706904755771)
        ·
          refine ⟨10786524589712560357133657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7191016393141706904755771 10786524589712560357133657)
          ·
            refine ⟨8089893442284420267850243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10786524589712560357133657 8089893442284420267850243)
            ·
              refine ⟨12134840163426630401775365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8089893442284420267850243 12134840163426630401775365)
              ·
                refine ⟨2275282530642493200332881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12134840163426630401775365 2275282530642493200332881)
                ·
                  refine ⟨1706461897981869900249661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2275282530642493200332881 1706461897981869900249661)
                  ·
                    refine ⟨639923211743201212593623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1706461897981869900249661 639923211743201212593623)
                    ·
                      rfl

theorem cell22_1869369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 3].length) (baseStart_1869369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869369 prefixEnd_1869369 := by exact prefixLift 1869369
  have htrace : WordTrace (prefixWord ++ tailWord_1869369) baseStart_1869369 baseEnd_1869369 := by
    simpa [prefixWord, tailWord_1869369, baseEnd_1869369] using wordTrace_append hprefix tailTrace_1869369
  have hstable : (prefixWord ++ tailWord_1869369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869369).length < 2 ^ (prefixWord ++ tailWord_1869369).sum := by decide
  have hdescent : baseEnd_1869369 < baseStart_1869369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869547 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 2, 6]
def baseStart_1869547 : Nat := 118140960795 + 1869547 * 2 ^ 59
def prefixEnd_1869547 : Nat := 4983230072969 + 3 ^ 40 * 1869547 * 2
def baseEnd_1869547 : Nat := 639984144780868081643077

theorem tailTrace_1869547 : CollatzResearch.WordTrace tailWord_1869547 prefixEnd_1869547 639984144780868081643077 := by
  unfold tailWord_1869547
  simp only [CollatzResearch.WordTrace]
  refine ⟨68187980957957987052478895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45458653971971991368319263 68187980957957987052478895)
  ·
    refine ⟨102281971436936980578718343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68187980957957987052478895 102281971436936980578718343)
    ·
      refine ⟨153422957155405470868077515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102281971436936980578718343 153422957155405470868077515)
      ·
        refine ⟨230134435733108206302116273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153422957155405470868077515 230134435733108206302116273)
        ·
          refine ⟨172600826799831154726587205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230134435733108206302116273 172600826799831154726587205)
          ·
            refine ⟨32362655024968341511235101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172600826799831154726587205 32362655024968341511235101)
            ·
              refine ⟨12135995634363128066713163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32362655024968341511235101 12135995634363128066713163)
              ·
                refine ⟨18203993451544692100069745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12135995634363128066713163 18203993451544692100069745)
                ·
                  refine ⟨13652995088658519075052309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18203993451544692100069745 13652995088658519075052309)
                  ·
                    refine ⟨639984144780868081643077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13652995088658519075052309 639984144780868081643077)
                    ·
                      rfl

theorem cell22_1869547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 6].length) (baseStart_1869547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869547 prefixEnd_1869547 := by exact prefixLift 1869547
  have htrace : WordTrace (prefixWord ++ tailWord_1869547) baseStart_1869547 baseEnd_1869547 := by
    simpa [prefixWord, tailWord_1869547, baseEnd_1869547] using wordTrace_append hprefix tailTrace_1869547
  have hstable : (prefixWord ++ tailWord_1869547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869547).length < 2 ^ (prefixWord ++ tailWord_1869547).sum := by decide
  have hdescent : baseEnd_1869547 < baseStart_1869547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869562 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 9]
def baseStart_1869562 : Nat := 118140960795 + 1869562 * 2 ^ 59
def prefixEnd_1869562 : Nat := 4983230072969 + 3 ^ 40 * 1869562 * 2
def baseEnd_1869562 : Nat := 213329759862471014172677

theorem tailTrace_1869562 : CollatzResearch.WordTrace tailWord_1869562 prefixEnd_1869562 213329759862471014172677 := by
  unfold tailWord_1869562
  simp only [CollatzResearch.WordTrace]
  refine ⟨17047132013225911153568735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45459018701935763076183293 17047132013225911153568735)
  ·
    refine ⟨25570698019838866730353103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17047132013225911153568735 25570698019838866730353103)
    ·
      refine ⟨38356047029758300095529655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25570698019838866730353103 38356047029758300095529655)
      ·
        refine ⟨57534070544637450143294483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38356047029758300095529655 57534070544637450143294483)
        ·
          refine ⟨86301105816956175214941725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57534070544637450143294483 86301105816956175214941725)
          ·
            refine ⟨32362914681358565705603147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86301105816956175214941725 32362914681358565705603147)
            ·
              refine ⟨48544372022037848558404721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32362914681358565705603147 48544372022037848558404721)
              ·
                refine ⟨36408279016528386418803541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48544372022037848558404721 36408279016528386418803541)
                ·
                  refine ⟨213329759862471014172677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36408279016528386418803541 213329759862471014172677)
                  ·
                    rfl

theorem cell22_1869562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_1869562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869562 prefixEnd_1869562 := by exact prefixLift 1869562
  have htrace : WordTrace (prefixWord ++ tailWord_1869562) baseStart_1869562 baseEnd_1869562 := by
    simpa [prefixWord, tailWord_1869562, baseEnd_1869562] using wordTrace_append hprefix tailTrace_1869562
  have hstable : (prefixWord ++ tailWord_1869562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869562).length < 2 ^ (prefixWord ++ tailWord_1869562).sum := by decide
  have hdescent : baseEnd_1869562 < baseStart_1869562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869577 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 3, 7]
def baseStart_1869577 : Nat := 118140960795 + 1869577 * 2 ^ 59
def prefixEnd_1869577 : Nat := 4983230072969 + 3 ^ 40 * 1869577 * 2
def baseEnd_1869577 : Nat := 639994414393958003392985

theorem tailTrace_1869577 : CollatzResearch.WordTrace tailWord_1869577 prefixEnd_1869577 639994414393958003392985 := by
  unfold tailWord_1869577
  simp only [CollatzResearch.WordTrace]
  refine ⟨68189075147849302176070985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45459383431899534784047323 68189075147849302176070985)
  ·
    refine ⟨51141806360886976632053239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68189075147849302176070985 51141806360886976632053239)
    ·
      refine ⟨76712709541330464948079859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51141806360886976632053239 76712709541330464948079859)
      ·
        refine ⟨115069064311995697422119789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76712709541330464948079859 115069064311995697422119789)
        ·
          refine ⟨43150899116998386533294921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115069064311995697422119789 43150899116998386533294921)
          ·
            refine ⟨32363174337748789899971191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43150899116998386533294921 32363174337748789899971191)
            ·
              refine ⟨48544761506623184849956787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32363174337748789899971191 48544761506623184849956787)
              ·
                refine ⟨72817142259934777274935181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48544761506623184849956787 72817142259934777274935181)
                ·
                  refine ⟨27306428347475541478100693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72817142259934777274935181 27306428347475541478100693)
                  ·
                    refine ⟨639994414393958003392985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27306428347475541478100693 639994414393958003392985)
                    ·
                      rfl

theorem cell22_1869577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_1869577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869577 prefixEnd_1869577 := by exact prefixLift 1869577
  have htrace : WordTrace (prefixWord ++ tailWord_1869577) baseStart_1869577 baseEnd_1869577 := by
    simpa [prefixWord, tailWord_1869577, baseEnd_1869577] using wordTrace_append hprefix tailTrace_1869577
  have hstable : (prefixWord ++ tailWord_1869577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869577).length < 2 ^ (prefixWord ++ tailWord_1869577).sum := by decide
  have hdescent : baseEnd_1869577 < baseStart_1869577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869594 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 2, 5]
def baseStart_1869594 : Nat := 118140960795 + 1869594 * 2 ^ 59
def prefixEnd_1869594 : Nat := 4983230072969 + 3 ^ 40 * 1869594 * 2
def baseEnd_1869594 : Nat := 640000233841375625717933

theorem tailTrace_1869594 : CollatzResearch.WordTrace tailWord_1869594 prefixEnd_1869594 640000233841375625717933 := by
  unfold tailWord_1869594
  simp only [CollatzResearch.WordTrace]
  refine ⟨17047423797196928519859959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45459796792525142719626557 17047423797196928519859959)
  ·
    refine ⟨25571135695795392779789939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17047423797196928519859959 25571135695795392779789939)
    ·
      refine ⟨38356703543693089169684909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25571135695795392779789939 38356703543693089169684909)
      ·
        refine ⟨14383763828884908438631841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38356703543693089169684909 14383763828884908438631841)
        ·
          refine ⟨10787822871663681328973881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14383763828884908438631841 10787822871663681328973881)
          ·
            refine ⟨8090867153747760996730411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10787822871663681328973881 8090867153747760996730411)
            ·
              refine ⟨12136300730621641495095617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8090867153747760996730411 12136300730621641495095617)
              ·
                refine ⟨9102225547966231121321713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12136300730621641495095617 9102225547966231121321713)
                ·
                  refine ⟨6826669160974673340991285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9102225547966231121321713 6826669160974673340991285)
                  ·
                    refine ⟨640000233841375625717933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6826669160974673340991285 640000233841375625717933)
                    ·
                      rfl

theorem cell22_1869594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_1869594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869594 prefixEnd_1869594 := by exact prefixLift 1869594
  have htrace : WordTrace (prefixWord ++ tailWord_1869594) baseStart_1869594 baseEnd_1869594 := by
    simpa [prefixWord, tailWord_1869594, baseEnd_1869594] using wordTrace_append hprefix tailTrace_1869594
  have hstable : (prefixWord ++ tailWord_1869594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869594).length < 2 ^ (prefixWord ++ tailWord_1869594).sum := by decide
  have hdescent : baseEnd_1869594 < baseStart_1869594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869624 : List Nat := [2, 1, 2, 1, 3, 3, 2, 2, 6]
def baseStart_1869624 : Nat := 118140960795 + 1869624 * 2 ^ 59
def prefixEnd_1869624 : Nat := 4983230072969 + 3 ^ 40 * 1869624 * 2
def baseEnd_1869624 : Nat := 213336834484821849155947

theorem tailTrace_1869624 : CollatzResearch.WordTrace tailWord_1869624 prefixEnd_1869624 213336834484821849155947 := by
  unfold tailWord_1869624
  simp only [CollatzResearch.WordTrace]
  refine ⟨34095394689339514601515963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45460526252452686135354617 34095394689339514601515963)
  ·
    refine ⟨51143092034009271902273945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34095394689339514601515963 51143092034009271902273945)
    ·
      refine ⟨38357319025506953926705459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51143092034009271902273945 38357319025506953926705459)
      ·
        refine ⟨57535978538260430890058189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38357319025506953926705459 57535978538260430890058189)
        ·
          refine ⟨21575991951847661583771821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57535978538260430890058189 21575991951847661583771821)
          ·
            refine ⟨8090996981942873093914433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21575991951847661583771821 8090996981942873093914433)
            ·
              refine ⟨6068247736457154820435825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8090996981942873093914433 6068247736457154820435825)
              ·
                refine ⟨4551185802342866115326869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6068247736457154820435825 4551185802342866115326869)
                ·
                  refine ⟨213336834484821849155947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4551185802342866115326869 213336834484821849155947)
                  ·
                    rfl

theorem cell22_1869624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 6].length) (baseStart_1869624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869624 prefixEnd_1869624 := by exact prefixLift 1869624
  have htrace : WordTrace (prefixWord ++ tailWord_1869624) baseStart_1869624 baseEnd_1869624 := by
    simpa [prefixWord, tailWord_1869624, baseEnd_1869624] using wordTrace_append hprefix tailTrace_1869624
  have hstable : (prefixWord ++ tailWord_1869624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869624).length < 2 ^ (prefixWord ++ tailWord_1869624).sum := by decide
  have hdescent : baseEnd_1869624 < baseStart_1869624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869626 : List Nat := [3, 1, 1, 1, 5, 1, 1, 4, 1, 4]
def baseStart_1869626 : Nat := 118140960795 + 1869626 * 2 ^ 59
def prefixEnd_1869626 : Nat := 4983230072969 + 3 ^ 40 * 1869626 * 2
def baseEnd_1869626 : Nat := 640011188095338208917835

theorem tailTrace_1869626 : CollatzResearch.WordTrace tailWord_1869626 prefixEnd_1869626 640011188095338208917835 := by
  unfold tailWord_1869626
  simp only [CollatzResearch.WordTrace]
  refine ⟨17047715581167945886151183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45460574883114522363069821 17047715581167945886151183)
  ·
    refine ⟨25571573371751918829226775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17047715581167945886151183 25571573371751918829226775)
    ·
      refine ⟨38357360057627878243840163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25571573371751918829226775 38357360057627878243840163)
      ·
        refine ⟨57536040086441817365760245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38357360057627878243840163 57536040086441817365760245)
        ·
          refine ⟨5394003758103920378040023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57536040086441817365760245 5394003758103920378040023)
          ·
            refine ⟨8091005637155880567060035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5394003758103920378040023 8091005637155880567060035)
            ·
              refine ⟨12136508455733820850590053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8091005637155880567060035 12136508455733820850590053)
              ·
                refine ⟨2275595335450091409485635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12136508455733820850590053 2275595335450091409485635)
                ·
                  refine ⟨3413393003175137114228453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275595335450091409485635 3413393003175137114228453)
                  ·
                    refine ⟨640011188095338208917835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3413393003175137114228453 640011188095338208917835)
                    ·
                      rfl

theorem cell22_1869626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_1869626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869626 prefixEnd_1869626 := by exact prefixLift 1869626
  have htrace : WordTrace (prefixWord ++ tailWord_1869626) baseStart_1869626 baseEnd_1869626 := by
    simpa [prefixWord, tailWord_1869626, baseEnd_1869626] using wordTrace_append hprefix tailTrace_1869626
  have hstable : (prefixWord ++ tailWord_1869626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869626).length < 2 ^ (prefixWord ++ tailWord_1869626).sum := by decide
  have hdescent : baseEnd_1869626 < baseStart_1869626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869639 : List Nat := [1, 1, 4, 1, 2, 1, 2, 4, 1, 5]
def baseStart_1869639 : Nat := 118140960795 + 1869639 * 2 ^ 59
def prefixEnd_1869639 : Nat := 4983230072969 + 3 ^ 40 * 1869639 * 2
def baseEnd_1869639 : Nat := 640015638261010508342795

theorem tailTrace_1869639 : CollatzResearch.WordTrace tailWord_1869639 prefixEnd_1869639 640015638261010508342795 := by
  unfold tailWord_1869639
  simp only [CollatzResearch.WordTrace]
  refine ⟨68191336473624686764827971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45460890982416457843218647 68191336473624686764827971)
  ·
    refine ⟨102287004710437030147241957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68191336473624686764827971 102287004710437030147241957)
    ·
      refine ⟨19178813383206943152607867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102287004710437030147241957 19178813383206943152607867)
      ·
        refine ⟨28768220074810414728911801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19178813383206943152607867 28768220074810414728911801)
        ·
          refine ⟨21576165056107811046683851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28768220074810414728911801 21576165056107811046683851)
          ·
            refine ⟨32364247584161716570025777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21576165056107811046683851 32364247584161716570025777)
            ·
              refine ⟨24273185688121287427519333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32364247584161716570025777 24273185688121287427519333)
              ·
                refine ⟨4551222316522741392659875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24273185688121287427519333 4551222316522741392659875)
                ·
                  refine ⟨6826833474784112088989813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4551222316522741392659875 6826833474784112088989813)
                  ·
                    refine ⟨640015638261010508342795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6826833474784112088989813 640015638261010508342795)
                    ·
                      rfl

theorem cell22_1869639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_1869639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869639 prefixEnd_1869639 := by exact prefixLift 1869639
  have htrace : WordTrace (prefixWord ++ tailWord_1869639) baseStart_1869639 baseEnd_1869639 := by
    simpa [prefixWord, tailWord_1869639, baseEnd_1869639] using wordTrace_append hprefix tailTrace_1869639
  have hstable : (prefixWord ++ tailWord_1869639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869639).length < 2 ^ (prefixWord ++ tailWord_1869639).sum := by decide
  have hdescent : baseEnd_1869639 < baseStart_1869639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869658 : List Nat := [3, 1, 1, 2, 1, 3, 5, 2, 4]
def baseStart_1869658 : Nat := 118140960795 + 1869658 * 2 ^ 59
def prefixEnd_1869658 : Nat := 4983230072969 + 3 ^ 40 * 1869658 * 2
def baseEnd_1869658 : Nat := 213340714116433597372579

theorem tailTrace_1869658 : CollatzResearch.WordTrace tailWord_1869658 prefixEnd_1869658 213340714116433597372579 := by
  unfold tailWord_1869658
  simp only [CollatzResearch.WordTrace]
  refine ⟨17048007365138963252442407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45461352973703902006513085 17048007365138963252442407)
  ·
    refine ⟨25572011047708444878663611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17048007365138963252442407 25572011047708444878663611)
    ·
      refine ⟨38358016571562667317995417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25572011047708444878663611 38358016571562667317995417)
      ·
        refine ⟨28768512428672000488496563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38358016571562667317995417 28768512428672000488496563)
        ·
          refine ⟨43152768643008000732744845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28768512428672000488496563 43152768643008000732744845)
          ·
            refine ⟨16182288241128000274779317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43152768643008000732744845 16182288241128000274779317)
            ·
              refine ⟨1517089522605750025760561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16182288241128000274779317 1517089522605750025760561)
              ·
                refine ⟨1137817141954312519320421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1517089522605750025760561 1137817141954312519320421)
                ·
                  refine ⟨213340714116433597372579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1137817141954312519320421 213340714116433597372579)
                  ·
                    rfl

theorem cell22_1869658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_1869658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869658 prefixEnd_1869658 := by exact prefixLift 1869658
  have htrace : WordTrace (prefixWord ++ tailWord_1869658) baseStart_1869658 baseEnd_1869658 := by
    simpa [prefixWord, tailWord_1869658, baseEnd_1869658] using wordTrace_append hprefix tailTrace_1869658
  have hstable : (prefixWord ++ tailWord_1869658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869658).length < 2 ^ (prefixWord ++ tailWord_1869658).sum := by decide
  have hdescent : baseEnd_1869658 < baseStart_1869658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869716 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_1869716 : Nat := 118140960795 + 1869716 * 2 ^ 59
def prefixEnd_1869716 : Nat := 4983230072969 + 3 ^ 40 * 1869716 * 2
def baseEnd_1869716 : Nat := 640041996934607974167559

theorem tailTrace_1869716 : CollatzResearch.WordTrace tailWord_1869716 prefixEnd_1869716 640041996934607974167559 := by
  unfold tailWord_1869716
  simp only [CollatzResearch.WordTrace]
  refine ⟨34097072447172864457690501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45462763262897152610254001 34097072447172864457690501)
  ·
    refine ⟨6393201083844912085816969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34097072447172864457690501 6393201083844912085816969)
    ·
      refine ⟨4794900812883684064362727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6393201083844912085816969 4794900812883684064362727)
      ·
        refine ⟨7192351219325526096544091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4794900812883684064362727 7192351219325526096544091)
        ·
          refine ⟨10788526828988289144816137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7192351219325526096544091 10788526828988289144816137)
          ·
            refine ⟨8091395121741216858612103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10788526828988289144816137 8091395121741216858612103)
            ·
              refine ⟨12137092682611825287918155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8091395121741216858612103 12137092682611825287918155)
              ·
                refine ⟨18205639023917737931877233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12137092682611825287918155 18205639023917737931877233)
                ·
                  refine ⟨13654229267938303448907925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18205639023917737931877233 13654229267938303448907925)
                  ·
                    refine ⟨640041996934607974167559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13654229267938303448907925 640041996934607974167559)
                    ·
                      rfl

theorem cell22_1869716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_1869716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869716 prefixEnd_1869716 := by exact prefixLift 1869716
  have htrace : WordTrace (prefixWord ++ tailWord_1869716) baseStart_1869716 baseEnd_1869716 := by
    simpa [prefixWord, tailWord_1869716, baseEnd_1869716] using wordTrace_append hprefix tailTrace_1869716
  have hstable : (prefixWord ++ tailWord_1869716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869716).length < 2 ^ (prefixWord ++ tailWord_1869716).sum := by decide
  have hdescent : baseEnd_1869716 < baseStart_1869716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869720 : List Nat := [2, 1, 2, 6, 2, 1, 1, 7]
def baseStart_1869720 : Nat := 118140960795 + 1869720 * 2 ^ 59
def prefixEnd_1869720 : Nat := 4983230072969 + 3 ^ 40 * 1869720 * 2
def baseEnd_1869720 : Nat := 71115929579594810785283

theorem tailTrace_1869720 : CollatzResearch.WordTrace tailWord_1869720 prefixEnd_1869720 71115929579594810785283 := by
  unfold tailWord_1869720
  simp only [CollatzResearch.WordTrace]
  refine ⟨34097145393165618799263307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45462860524220825065684409 34097145393165618799263307)
  ·
    refine ⟨51145718089748428198894961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34097145393165618799263307 51145718089748428198894961)
    ·
      refine ⟨38359288567311321149171221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51145718089748428198894961 38359288567311321149171221)
      ·
        refine ⟨1798091651592718178867401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38359288567311321149171221 1798091651592718178867401)
        ·
          refine ⟨1348568738694538634150551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1798091651592718178867401 1348568738694538634150551)
          ·
            refine ⟨2022853108041807951225827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348568738694538634150551 2022853108041807951225827)
            ·
              refine ⟨3034279662062711926838741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2022853108041807951225827 3034279662062711926838741)
              ·
                refine ⟨71115929579594810785283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3034279662062711926838741 71115929579594810785283)
                ·
                  rfl

theorem cell22_1869720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 7].length) (baseStart_1869720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869720 prefixEnd_1869720 := by exact prefixLift 1869720
  have htrace : WordTrace (prefixWord ++ tailWord_1869720) baseStart_1869720 baseEnd_1869720 := by
    simpa [prefixWord, tailWord_1869720, baseEnd_1869720] using wordTrace_append hprefix tailTrace_1869720
  have hstable : (prefixWord ++ tailWord_1869720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869720).length < 2 ^ (prefixWord ++ tailWord_1869720).sum := by decide
  have hdescent : baseEnd_1869720 < baseStart_1869720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869759 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 8]
def baseStart_1869759 : Nat := 118140960795 + 1869759 * 2 ^ 59
def prefixEnd_1869759 : Nat := 4983230072969 + 3 ^ 40 * 1869759 * 2
def baseEnd_1869759 : Nat := 213352238904456731780809

theorem tailTrace_1869759 : CollatzResearch.WordTrace tailWord_1869759 prefixEnd_1869759 213352238904456731780809 := by
  unfold tailWord_1869759
  simp only [CollatzResearch.WordTrace]
  refine ⟨68195713233189947259196331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45463808822126631506130887 68195713233189947259196331)
  ·
    refine ⟨102293569849784920888794497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68195713233189947259196331 102293569849784920888794497)
    ·
      refine ⟨76720177387338690666595873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102293569849784920888794497 76720177387338690666595873)
      ·
        refine ⟨57540133040504017999946905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76720177387338690666595873 57540133040504017999946905)
        ·
          refine ⟨43155099780378013499960179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57540133040504017999946905 43155099780378013499960179)
          ·
            refine ⟨64732649670567020249940269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43155099780378013499960179 64732649670567020249940269)
            ·
              refine ⟨24274743626462632593727601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64732649670567020249940269 24274743626462632593727601)
              ·
                refine ⟨18206057719846974445295701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24274743626462632593727601 18206057719846974445295701)
                ·
                  refine ⟨213352238904456731780809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18206057719846974445295701 213352238904456731780809)
                  ·
                    rfl

theorem cell22_1869759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 8].length) (baseStart_1869759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869759 prefixEnd_1869759 := by exact prefixLift 1869759
  have htrace : WordTrace (prefixWord ++ tailWord_1869759) baseStart_1869759 baseEnd_1869759 := by
    simpa [prefixWord, tailWord_1869759, baseEnd_1869759] using wordTrace_append hprefix tailTrace_1869759
  have hstable : (prefixWord ++ tailWord_1869759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869759).length < 2 ^ (prefixWord ++ tailWord_1869759).sum := by decide
  have hdescent : baseEnd_1869759 < baseStart_1869759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869782 : List Nat := [5, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_1869782 : Nat := 118140960795 + 1869782 * 2 ^ 59
def prefixEnd_1869782 : Nat := 4983230072969 + 3 ^ 40 * 1869782 * 2
def baseEnd_1869782 : Nat := 213354863361135267339119

theorem tailTrace_1869782 : CollatzResearch.WordTrace tailWord_1869782 prefixEnd_1869782 213354863361135267339119 := by
  unfold tailWord_1869782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4262284507006663886705225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45464368074737748124855733 4262284507006663886705225)
  ·
    refine ⟨3196713380254997915028919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4262284507006663886705225 3196713380254997915028919)
    ·
      refine ⟨4795070070382496872543379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3196713380254997915028919 4795070070382496872543379)
      ·
        refine ⟨7192605105573745308815069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4795070070382496872543379 7192605105573745308815069)
        ·
          refine ⟨2697226914590154490805651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7192605105573745308815069 2697226914590154490805651)
          ·
            refine ⟨4045840371885231736208477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697226914590154490805651 4045840371885231736208477)
            ·
              refine ⟨1517190139456961901078179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4045840371885231736208477 1517190139456961901078179)
              ·
                refine ⟨2275785209185442851617269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1517190139456961901078179 2275785209185442851617269)
                ·
                  refine ⟨213354863361135267339119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2275785209185442851617269 213354863361135267339119)
                  ·
                    rfl

theorem cell22_1869782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_1869782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869782 prefixEnd_1869782 := by exact prefixLift 1869782
  have htrace : WordTrace (prefixWord ++ tailWord_1869782) baseStart_1869782 baseEnd_1869782 := by
    simpa [prefixWord, tailWord_1869782, baseEnd_1869782] using wordTrace_append hprefix tailTrace_1869782
  have hstable : (prefixWord ++ tailWord_1869782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869782).length < 2 ^ (prefixWord ++ tailWord_1869782).sum := by decide
  have hdescent : baseEnd_1869782 < baseStart_1869782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869887 : List Nat := [1, 1, 2, 2, 3, 1, 6, 2, 1, 3]
def baseStart_1869887 : Nat := 118140960795 + 1869887 * 2 ^ 59
def prefixEnd_1869887 : Nat := 4983230072969 + 3 ^ 40 * 1869887 * 2
def baseEnd_1869887 : Nat := 640100533729220528142035

theorem tailTrace_1869887 : CollatzResearch.WordTrace tailWord_1869887 prefixEnd_1869887 640100533729220528142035 := by
  unfold tailWord_1869887
  simp only [CollatzResearch.WordTrace]
  refine ⟨68200381776726225119855915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45466921184484150079903943 68200381776726225119855915)
  ·
    refine ⟨102300572665089337679783873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68200381776726225119855915 102300572665089337679783873)
    ·
      refine ⟨76725429498817003259837905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102300572665089337679783873 76725429498817003259837905)
      ·
        refine ⟨57544072124112752444878429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76725429498817003259837905 57544072124112752444878429)
        ·
          refine ⟨21579027046542282166829411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57544072124112752444878429 21579027046542282166829411)
          ·
            refine ⟨32368540569813423250244117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21579027046542282166829411 32368540569813423250244117)
            ·
              refine ⟨1517275339210004214855193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32368540569813423250244117 1517275339210004214855193)
              ·
                refine ⟨1137956504407503161141395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1517275339210004214855193 1137956504407503161141395)
                ·
                  refine ⟨1706934756611254741712093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137956504407503161141395 1706934756611254741712093)
                  ·
                    refine ⟨640100533729220528142035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1706934756611254741712093 640100533729220528142035)
                    ·
                      rfl

theorem cell22_1869887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 1, 3].length) (baseStart_1869887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869887 prefixEnd_1869887 := by exact prefixLift 1869887
  have htrace : WordTrace (prefixWord ++ tailWord_1869887) baseStart_1869887 baseEnd_1869887 := by
    simpa [prefixWord, tailWord_1869887, baseEnd_1869887] using wordTrace_append hprefix tailTrace_1869887
  have hstable : (prefixWord ++ tailWord_1869887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869887).length < 2 ^ (prefixWord ++ tailWord_1869887).sum := by decide
  have hdescent : baseEnd_1869887 < baseStart_1869887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869911 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 8]
def baseStart_1869911 : Nat := 118140960795 + 1869911 * 2 ^ 59
def prefixEnd_1869911 : Nat := 4983230072969 + 3 ^ 40 * 1869911 * 2
def baseEnd_1869911 : Nat := 213369583139897488513987

theorem tailTrace_1869911 : CollatzResearch.WordTrace tailWord_1869911 prefixEnd_1869911 213369583139897488513987 := by
  unfold tailWord_1869911
  simp only [CollatzResearch.WordTrace]
  refine ⟨68201257128639277218729587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45467504752426184812486391 68201257128639277218729587)
  ·
    refine ⟨102301885692958915828094381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68201257128639277218729587 102301885692958915828094381)
    ·
      refine ⟨38363207134859593435535393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102301885692958915828094381 38363207134859593435535393)
      ·
        refine ⟨28772405351144695076651545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38363207134859593435535393 28772405351144695076651545)
        ·
          refine ⟨21579304013358521307488659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28772405351144695076651545 21579304013358521307488659)
          ·
            refine ⟨32368956020037781961232989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21579304013358521307488659 32368956020037781961232989)
            ·
              refine ⟨12138358507514168235462371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32368956020037781961232989 12138358507514168235462371)
              ·
                refine ⟨18207537761271252353193557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12138358507514168235462371 18207537761271252353193557)
                ·
                  refine ⟨213369583139897488513987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18207537761271252353193557 213369583139897488513987)
                  ·
                    rfl

theorem cell22_1869911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 8].length) (baseStart_1869911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869911 prefixEnd_1869911 := by exact prefixLift 1869911
  have htrace : WordTrace (prefixWord ++ tailWord_1869911) baseStart_1869911 baseEnd_1869911 := by
    simpa [prefixWord, tailWord_1869911, baseEnd_1869911] using wordTrace_append hprefix tailTrace_1869911
  have hstable : (prefixWord ++ tailWord_1869911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869911).length < 2 ^ (prefixWord ++ tailWord_1869911).sum := by decide
  have hdescent : baseEnd_1869911 < baseStart_1869911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869913 : List Nat := [1, 2, 1, 2, 2, 1, 4, 4, 1, 4]
def baseStart_1869913 : Nat := 118140960795 + 1869913 * 2 ^ 59
def prefixEnd_1869913 : Nat := 4983230072969 + 3 ^ 40 * 1869913 * 2
def baseEnd_1869913 : Nat := 640109434060565126991955

theorem tailTrace_1869913 : CollatzResearch.WordTrace tailWord_1869913 prefixEnd_1869913 640109434060565126991955 := by
  unfold tailWord_1869913
  simp only [CollatzResearch.WordTrace]
  refine ⟨68201330074632031560302393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45467553383088021040201595 68201330074632031560302393)
  ·
    refine ⟨51150997555974023670226795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68201330074632031560302393 51150997555974023670226795)
    ·
      refine ⟨76726496333961035505340193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51150997555974023670226795 76726496333961035505340193)
      ·
        refine ⟨57544872250470776629005145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76726496333961035505340193 57544872250470776629005145)
        ·
          refine ⟨43158654187853082471753859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57544872250470776629005145 43158654187853082471753859)
          ·
            refine ⟨64737981281779623707630789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43158654187853082471753859 64737981281779623707630789)
            ·
              refine ⟨12138371490333679445180773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64737981281779623707630789 12138371490333679445180773)
              ·
                refine ⟨2275944654437564895971395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12138371490333679445180773 2275944654437564895971395)
                ·
                  refine ⟨3413916981656347343957093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275944654437564895971395 3413916981656347343957093)
                  ·
                    refine ⟨640109434060565126991955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3413916981656347343957093 640109434060565126991955)
                    ·
                      rfl

theorem cell22_1869913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 4].length) (baseStart_1869913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869913 prefixEnd_1869913 := by exact prefixLift 1869913
  have htrace : WordTrace (prefixWord ++ tailWord_1869913) baseStart_1869913 baseEnd_1869913 := by
    simpa [prefixWord, tailWord_1869913, baseEnd_1869913] using wordTrace_append hprefix tailTrace_1869913
  have hstable : (prefixWord ++ tailWord_1869913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869913).length < 2 ^ (prefixWord ++ tailWord_1869913).sum := by decide
  have hdescent : baseEnd_1869913 < baseStart_1869913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869945 : List Nat := [1, 2, 1, 3, 4, 1, 2, 4, 4]
def baseStart_1869945 : Nat := 118140960795 + 1869945 * 2 ^ 59
def prefixEnd_1869945 : Nat := 4983230072969 + 3 ^ 40 * 1869945 * 2
def baseEnd_1869945 : Nat := 213373462771509236730619

theorem tailTrace_1869945 : CollatzResearch.WordTrace tailWord_1869945 prefixEnd_1869945 213373462771509236730619 := by
  unfold tailWord_1869945
  simp only [CollatzResearch.WordTrace]
  refine ⟨68202497210516101025467289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45468331473677400683644859 68202497210516101025467289)
  ·
    refine ⟨51151872907887075769100467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68202497210516101025467289 51151872907887075769100467)
    ·
      refine ⟨76727809361830613653650701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51151872907887075769100467 76727809361830613653650701)
      ·
        refine ⟨28772928510686480120119013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76727809361830613653650701 28772928510686480120119013)
        ·
          refine ⟨5394924095753715022522315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28772928510686480120119013 5394924095753715022522315)
          ·
            refine ⟨8092386143630572533783473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5394924095753715022522315 8092386143630572533783473)
            ·
              refine ⟨6069289607722929400337605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8092386143630572533783473 6069289607722929400337605)
              ·
                refine ⟨1137991801448049262563301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6069289607722929400337605 1137991801448049262563301)
                ·
                  refine ⟨213373462771509236730619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1137991801448049262563301 213373462771509236730619)
                  ·
                    rfl

theorem cell22_1869945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 4].length) (baseStart_1869945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869945 prefixEnd_1869945 := by exact prefixLift 1869945
  have htrace : WordTrace (prefixWord ++ tailWord_1869945) baseStart_1869945 baseEnd_1869945 := by
    simpa [prefixWord, tailWord_1869945, baseEnd_1869945] using wordTrace_append hprefix tailTrace_1869945
  have hstable : (prefixWord ++ tailWord_1869945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869945).length < 2 ^ (prefixWord ++ tailWord_1869945).sum := by decide
  have hdescent : baseEnd_1869945 < baseStart_1869945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869960 : List Nat := [2, 1, 3, 4, 1, 1, 3, 1, 1, 5]
def baseStart_1869960 : Nat := 118140960795 + 1869960 * 2 ^ 59
def prefixEnd_1869960 : Nat := 4983230072969 + 3 ^ 40 * 1869960 * 2
def baseEnd_1869960 : Nat := 640125523121072671066811

theorem tailTrace_1869960 : CollatzResearch.WordTrace tailWord_1869960 prefixEnd_1869960 640125523121072671066811 := by
  unfold tailWord_1869960
  simp only [CollatzResearch.WordTrace]
  refine ⟨34101522152730879293631667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45468696203641172391508889 34101522152730879293631667)
  ·
    refine ⟨51152283229096318940447501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34101522152730879293631667 51152283229096318940447501)
    ·
      refine ⟨19182106210911119602667813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51152283229096318940447501 19182106210911119602667813)
      ·
        refine ⟨3596644914545834925500215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19182106210911119602667813 3596644914545834925500215)
        ·
          refine ⟨5394967371818752388250323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3596644914545834925500215 5394967371818752388250323)
          ·
            refine ⟨8092451057728128582375485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5394967371818752388250323 8092451057728128582375485)
            ·
              refine ⟨3034669146648048218390807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8092451057728128582375485 3034669146648048218390807)
              ·
                refine ⟨4552003719972072327586211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3034669146648048218390807 4552003719972072327586211)
                ·
                  refine ⟨6828005579958108491379317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4552003719972072327586211 6828005579958108491379317)
                  ·
                    refine ⟨640125523121072671066811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6828005579958108491379317 640125523121072671066811)
                    ·
                      rfl

theorem cell22_1869960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_1869960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869960 prefixEnd_1869960 := by exact prefixLift 1869960
  have htrace : WordTrace (prefixWord ++ tailWord_1869960) baseStart_1869960 baseEnd_1869960 := by
    simpa [prefixWord, tailWord_1869960, baseEnd_1869960] using wordTrace_append hprefix tailTrace_1869960
  have hstable : (prefixWord ++ tailWord_1869960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869960).length < 2 ^ (prefixWord ++ tailWord_1869960).sum := by decide
  have hdescent : baseEnd_1869960 < baseStart_1869960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869971 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 1, 9]
def baseStart_1869971 : Nat := 118140960795 + 1869971 * 2 ^ 59
def prefixEnd_1869971 : Nat := 4983230072969 + 3 ^ 40 * 1869971 * 2
def baseEnd_1869971 : Nat := 640129288645872309041777

theorem tailTrace_1869971 : CollatzResearch.WordTrace tailWord_1869971 prefixEnd_1869971 640129288645872309041777 := by
  unfold tailWord_1869971
  simp only [CollatzResearch.WordTrace]
  refine ⟨68203445508421907465913767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45468963672281271643942511 68203445508421907465913767)
  ·
    refine ⟨102305168262632861198870651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68203445508421907465913767 102305168262632861198870651)
    ·
      refine ⟨153457752393949291798305977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102305168262632861198870651 153457752393949291798305977)
      ·
        refine ⟨115093314295461968848729483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153457752393949291798305977 115093314295461968848729483)
        ·
          refine ⟨172639971443192953273094225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115093314295461968848729483 172639971443192953273094225)
          ·
            refine ⟨129479978582394714954820669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172639971443192953273094225 129479978582394714954820669)
            ·
              refine ⟨48554991968398018108057751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129479978582394714954820669 48554991968398018108057751)
              ·
                refine ⟨72832487952597027162086627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48554991968398018108057751 72832487952597027162086627)
                ·
                  refine ⟨109248731928895540743129941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72832487952597027162086627 109248731928895540743129941)
                  ·
                    refine ⟨640129288645872309041777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 109248731928895540743129941 640129288645872309041777)
                    ·
                      rfl

theorem cell22_1869971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 9].length) (baseStart_1869971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1869971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1869971 prefixEnd_1869971 := by exact prefixLift 1869971
  have htrace : WordTrace (prefixWord ++ tailWord_1869971) baseStart_1869971 baseEnd_1869971 := by
    simpa [prefixWord, tailWord_1869971, baseEnd_1869971] using wordTrace_append hprefix tailTrace_1869971
  have hstable : (prefixWord ++ tailWord_1869971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869971).length < 2 ^ (prefixWord ++ tailWord_1869971).sum := by decide
  have hdescent : baseEnd_1869971 < baseStart_1869971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870056 : List Nat := [2, 1, 4, 1, 2, 4, 2, 2, 1, 3]
def baseStart_1870056 : Nat := 118140960795 + 1870056 * 2 ^ 59
def prefixEnd_1870056 : Nat := 4983230072969 + 3 ^ 40 * 1870056 * 2
def baseEnd_1870056 : Nat := 640158385882960420666517

theorem tailTrace_1870056 : CollatzResearch.WordTrace tailWord_1870056 prefixEnd_1870056 640158385882960420666517 := by
  unfold tailWord_1870056
  simp only [CollatzResearch.WordTrace]
  refine ⟨34103272856556983491379011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45471030475409311321838681 34103272856556983491379011)
  ·
    refine ⟨51154909284835475237068517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34103272856556983491379011 51154909284835475237068517)
    ·
      refine ⟨9591545490906651606950347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51154909284835475237068517 9591545490906651606950347)
      ·
        refine ⟨14387318236359977410425521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9591545490906651606950347 14387318236359977410425521)
        ·
          refine ⟨10790488677269983057819141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14387318236359977410425521 10790488677269983057819141)
          ·
            refine ⟨2023216626988121823341089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10790488677269983057819141 2023216626988121823341089)
            ·
              refine ⟨1517412470241091367505817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2023216626988121823341089 1517412470241091367505817)
              ·
                refine ⟨1138059352680818525629363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1517412470241091367505817 1138059352680818525629363)
                ·
                  refine ⟨1707089029021227788444045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1138059352680818525629363 1707089029021227788444045)
                  ·
                    refine ⟨640158385882960420666517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1707089029021227788444045 640158385882960420666517)
                    ·
                      rfl

theorem cell22_1870056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_1870056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870056 prefixEnd_1870056 := by exact prefixLift 1870056
  have htrace : WordTrace (prefixWord ++ tailWord_1870056) baseStart_1870056 baseEnd_1870056 := by
    simpa [prefixWord, tailWord_1870056, baseEnd_1870056] using wordTrace_append hprefix tailTrace_1870056
  have hstable : (prefixWord ++ tailWord_1870056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870056).length < 2 ^ (prefixWord ++ tailWord_1870056).sum := by decide
  have hdescent : baseEnd_1870056 < baseStart_1870056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870082 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_1870082 : Nat := 118140960795 + 1870082 * 2 ^ 59
def prefixEnd_1870082 : Nat := 4983230072969 + 3 ^ 40 * 1870082 * 2
def baseEnd_1870082 : Nat := 640167286214305019516437

theorem tailTrace_1870082 : CollatzResearch.WordTrace tailWord_1870082 prefixEnd_1870082 640167286214305019516437 := by
  unfold tailWord_1870082
  simp only [CollatzResearch.WordTrace]
  refine ⟨17051873502754943355801125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45471662674013182282136333 17051873502754943355801125)
  ·
    refine ⟨3197226281766551879212711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17051873502754943355801125 3197226281766551879212711)
    ·
      refine ⟨4795839422649827818819067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3197226281766551879212711 4795839422649827818819067)
      ·
        refine ⟨7193759133974741728228601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4795839422649827818819067 7193759133974741728228601)
        ·
          refine ⟨5395319350481056296171451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7193759133974741728228601 5395319350481056296171451)
          ·
            refine ⟨8092979025721584444257177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5395319350481056296171451 8092979025721584444257177)
            ·
              refine ⟨6069734269291188333192883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8092979025721584444257177 6069734269291188333192883)
              ·
                refine ⟨9104601403936782499789325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6069734269291188333192883 9104601403936782499789325)
                ·
                  refine ⟨3414225526476293437420997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9104601403936782499789325 3414225526476293437420997)
                  ·
                    refine ⟨640167286214305019516437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3414225526476293437420997 640167286214305019516437)
                    ·
                      rfl

theorem cell22_1870082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_1870082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870082 prefixEnd_1870082 := by exact prefixLift 1870082
  have htrace : WordTrace (prefixWord ++ tailWord_1870082) baseStart_1870082 baseEnd_1870082 := by
    simpa [prefixWord, tailWord_1870082, baseEnd_1870082] using wordTrace_append hprefix tailTrace_1870082
  have hstable : (prefixWord ++ tailWord_1870082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870082).length < 2 ^ (prefixWord ++ tailWord_1870082).sum := by decide
  have hdescent : baseEnd_1870082 < baseStart_1870082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870097 : List Nat := [1, 2, 2, 1, 1, 6, 2, 3, 4]
def baseStart_1870097 : Nat := 118140960795 + 1870097 * 2 ^ 59
def prefixEnd_1870097 : Nat := 4983230072969 + 3 ^ 40 * 1870097 * 2
def baseEnd_1870097 : Nat := 213390807006949993463797

theorem tailTrace_1870097 : CollatzResearch.WordTrace tailWord_1870097 prefixEnd_1870097 213390807006949993463797 := by
  unfold tailWord_1870097
  simp only [CollatzResearch.WordTrace]
  refine ⟨68208041105965430985000545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45472027403976953990000363 68208041105965430985000545)
  ·
    refine ⟨51156030829474073238750409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68208041105965430985000545 51156030829474073238750409)
    ·
      refine ⟨38367023122105554929062807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51156030829474073238750409 38367023122105554929062807)
      ·
        refine ⟨57550534683158332393594211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38367023122105554929062807 57550534683158332393594211)
        ·
          refine ⟨86325802024737498590391317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57550534683158332393594211 86325802024737498590391317)
          ·
            refine ⟨4046521969909570246424593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86325802024737498590391317 4046521969909570246424593)
            ·
              refine ⟨3034891477432177684818445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4046521969909570246424593 3034891477432177684818445)
              ·
                refine ⟨1138084304037066631806917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3034891477432177684818445 1138084304037066631806917)
                ·
                  refine ⟨213390807006949993463797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1138084304037066631806917 213390807006949993463797)
                  ·
                    rfl

theorem cell22_1870097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 4].length) (baseStart_1870097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870097 prefixEnd_1870097 := by exact prefixLift 1870097
  have htrace : WordTrace (prefixWord ++ tailWord_1870097) baseStart_1870097 baseEnd_1870097 := by
    simpa [prefixWord, tailWord_1870097, baseEnd_1870097] using wordTrace_append hprefix tailTrace_1870097
  have hstable : (prefixWord ++ tailWord_1870097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870097).length < 2 ^ (prefixWord ++ tailWord_1870097).sum := by decide
  have hdescent : baseEnd_1870097 < baseStart_1870097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870112 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 4, 3]
def baseStart_1870112 : Nat := 118140960795 + 1870112 * 2 ^ 59
def prefixEnd_1870112 : Nat := 4983230072969 + 3 ^ 40 * 1870112 * 2
def baseEnd_1870112 : Nat := 640177555827394941266345

theorem tailTrace_1870112 : CollatzResearch.WordTrace tailWord_1870112 prefixEnd_1870112 640177555827394941266345 := by
  unfold tailWord_1870112
  simp only [CollatzResearch.WordTrace]
  refine ⟨34104294100455544273398295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45472392133940725697864393 34104294100455544273398295)
  ·
    refine ⟨51156441150683316410097443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34104294100455544273398295 51156441150683316410097443)
    ·
      refine ⟨76734661726024974615146165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51156441150683316410097443 76734661726024974615146165)
      ·
        refine ⟨7193874536814841370169953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76734661726024974615146165 7193874536814841370169953)
        ·
          refine ⟨5395405902611131027627465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7193874536814841370169953 5395405902611131027627465)
          ·
            refine ⟨4046554426958348270720599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5395405902611131027627465 4046554426958348270720599)
            ·
              refine ⟨6069831640437522406080899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4046554426958348270720599 6069831640437522406080899)
              ·
                refine ⟨9104747460656283609121349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6069831640437522406080899 9104747460656283609121349)
                ·
                  refine ⟨1707140148873053176710253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9104747460656283609121349 1707140148873053176710253)
                  ·
                    refine ⟨640177555827394941266345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1707140148873053176710253 640177555827394941266345)
                    ·
                      rfl

theorem cell22_1870112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 4, 3].length) (baseStart_1870112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870112 prefixEnd_1870112 := by exact prefixLift 1870112
  have htrace : WordTrace (prefixWord ++ tailWord_1870112) baseStart_1870112 baseEnd_1870112 := by
    simpa [prefixWord, tailWord_1870112, baseEnd_1870112] using wordTrace_append hprefix tailTrace_1870112
  have hstable : (prefixWord ++ tailWord_1870112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870112).length < 2 ^ (prefixWord ++ tailWord_1870112).sum := by decide
  have hdescent : baseEnd_1870112 < baseStart_1870112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870129 : List Nat := [1, 2, 2, 3, 5, 1, 1, 1, 1, 5]
def baseStart_1870129 : Nat := 118140960795 + 1870129 * 2 ^ 59
def prefixEnd_1870129 : Nat := 4983230072969 + 3 ^ 40 * 1870129 * 2
def baseEnd_1870129 : Nat := 640183375274812563591293

theorem tailTrace_1870129 : CollatzResearch.WordTrace tailWord_1870129 prefixEnd_1870129 640183375274812563591293 := by
  unfold tailWord_1870129
  simp only [CollatzResearch.WordTrace]
  refine ⟨68209208241849500450165441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45472805494566333633443627 68209208241849500450165441)
  ·
    refine ⟨51156906181387125337624081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68209208241849500450165441 51156906181387125337624081)
    ·
      refine ⟨38367679636040344003218061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51156906181387125337624081 38367679636040344003218061)
      ·
        refine ⟨14387879863515129001206773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38367679636040344003218061 14387879863515129001206773)
        ·
          refine ⟨1348863737204543343863135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14387879863515129001206773 1348863737204543343863135)
          ·
            refine ⟨2023295605806815015794703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348863737204543343863135 2023295605806815015794703)
            ·
              refine ⟨3034943408710222523692055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2023295605806815015794703 3034943408710222523692055)
              ·
                refine ⟨4552415113065333785538083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3034943408710222523692055 4552415113065333785538083)
                ·
                  refine ⟨6828622669598000678307125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4552415113065333785538083 6828622669598000678307125)
                  ·
                    refine ⟨640183375274812563591293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6828622669598000678307125 640183375274812563591293)
                    ·
                      rfl

theorem cell22_1870129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 1, 5].length) (baseStart_1870129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870129 prefixEnd_1870129 := by exact prefixLift 1870129
  have htrace : WordTrace (prefixWord ++ tailWord_1870129) baseStart_1870129 baseEnd_1870129 := by
    simpa [prefixWord, tailWord_1870129, baseEnd_1870129] using wordTrace_append hprefix tailTrace_1870129
  have hstable : (prefixWord ++ tailWord_1870129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870129).length < 2 ^ (prefixWord ++ tailWord_1870129).sum := by decide
  have hdescent : baseEnd_1870129 < baseStart_1870129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870142 : List Nat := [4, 2, 1, 2, 1, 2, 4, 6]
def baseStart_1870142 : Nat := 118140960795 + 1870142 * 2 ^ 59
def prefixEnd_1870142 : Nat := 4983230072969 + 3 ^ 40 * 1870142 * 2
def baseEnd_1870142 : Nat := 71131980604498318112917

theorem tailTrace_1870142 : CollatzResearch.WordTrace tailWord_1870142 prefixEnd_1870142 71131980604498318112917 := by
  unfold tailWord_1870142
  simp only [CollatzResearch.WordTrace]
  refine ⟨8526210298850300458798585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45473121593868269113592453 8526210298850300458798585)
  ·
    refine ⟨6394657724137725344098939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8526210298850300458798585 6394657724137725344098939)
    ·
      refine ⟨9591986586206588016148409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6394657724137725344098939 9591986586206588016148409)
      ·
        refine ⟨7193989939654941012111307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9591986586206588016148409 7193989939654941012111307)
        ·
          refine ⟨10790984909482411518166961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7193989939654941012111307 10790984909482411518166961)
          ·
            refine ⟨8093238682111808638625221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10790984909482411518166961 8093238682111808638625221)
            ·
              refine ⟨1517482252895964119742229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8093238682111808638625221 1517482252895964119742229)
              ·
                refine ⟨71131980604498318112917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1517482252895964119742229 71131980604498318112917)
                ·
                  rfl

theorem cell22_1870142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_1870142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870142 prefixEnd_1870142 := by exact prefixLift 1870142
  have htrace : WordTrace (prefixWord ++ tailWord_1870142) baseStart_1870142 baseEnd_1870142 := by
    simpa [prefixWord, tailWord_1870142, baseEnd_1870142] using wordTrace_append hprefix tailTrace_1870142
  have hstable : (prefixWord ++ tailWord_1870142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870142).length < 2 ^ (prefixWord ++ tailWord_1870142).sum := by decide
  have hdescent : baseEnd_1870142 < baseStart_1870142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870148 : List Nat := [2, 3, 4, 1, 3, 1, 1, 3, 4]
def baseStart_1870148 : Nat := 118140960795 + 1870148 * 2 ^ 59
def prefixEnd_1870148 : Nat := 4983230072969 + 3 ^ 40 * 1870148 * 2
def baseEnd_1870148 : Nat := 213396626454367615788745

theorem tailTrace_1870148 : CollatzResearch.WordTrace tailWord_1870148 prefixEnd_1870148 213396626454367615788745 := by
  unfold tailWord_1870148
  simp only [CollatzResearch.WordTrace]
  refine ⟨34104950614390333347553549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45473267485853777796738065 34104950614390333347553549)
  ·
    refine ⟨12789356480396375005332581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34104950614390333347553549 12789356480396375005332581)
    ·
      refine ⟨2398004340074320313499859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12789356480396375005332581 2398004340074320313499859)
      ·
        refine ⟨3597006510111480470249789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2398004340074320313499859 3597006510111480470249789)
        ·
          refine ⟨1348877441291805176343671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3597006510111480470249789 1348877441291805176343671)
          ·
            refine ⟨2023316161937707764515507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348877441291805176343671 2023316161937707764515507)
            ·
              refine ⟨3034974242906561646773261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2023316161937707764515507 3034974242906561646773261)
              ·
                refine ⟨1138115341089960617539973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3034974242906561646773261 1138115341089960617539973)
                ·
                  refine ⟨213396626454367615788745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1138115341089960617539973 213396626454367615788745)
                  ·
                    rfl

theorem cell22_1870148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_1870148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870148 prefixEnd_1870148 := by exact prefixLift 1870148
  have htrace : WordTrace (prefixWord ++ tailWord_1870148) baseStart_1870148 baseEnd_1870148 := by
    simpa [prefixWord, tailWord_1870148, baseEnd_1870148] using wordTrace_append hprefix tailTrace_1870148
  have hstable : (prefixWord ++ tailWord_1870148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870148).length < 2 ^ (prefixWord ++ tailWord_1870148).sum := by decide
  have hdescent : baseEnd_1870148 < baseStart_1870148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870170 : List Nat := [3, 1, 1, 2, 1, 2, 1, 6, 5]
def baseStart_1870170 : Nat := 118140960795 + 1870170 * 2 ^ 59
def prefixEnd_1870170 : Nat := 4983230072969 + 3 ^ 40 * 1870170 * 2
def baseEnd_1870170 : Nat := 213399136804234041105389

theorem tailTrace_1870170 : CollatzResearch.WordTrace tailWord_1870170 prefixEnd_1870170 213399136804234041105389 := by
  unfold tailWord_1870170
  simp only [CollatzResearch.WordTrace]
  refine ⟨17052675908675241113101991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45473802423133976301605309 17052675908675241113101991)
  ·
    refine ⟨25579013863012861669652987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17052675908675241113101991 25579013863012861669652987)
    ·
      refine ⟨38368520794519292504479481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25579013863012861669652987 38368520794519292504479481)
      ·
        refine ⟨28776390595889469378359611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38368520794519292504479481 28776390595889469378359611)
        ·
          refine ⟨43164585893834204067539417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28776390595889469378359611 43164585893834204067539417)
          ·
            refine ⟨32373439420375653050654563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43164585893834204067539417 32373439420375653050654563)
            ·
              refine ⟨48560159130563479575981845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32373439420375653050654563 48560159130563479575981845)
              ·
                refine ⟨2276257459245163105124149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48560159130563479575981845 2276257459245163105124149)
                ·
                  refine ⟨213399136804234041105389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2276257459245163105124149 213399136804234041105389)
                  ·
                    rfl

theorem cell22_1870170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_1870170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870170 prefixEnd_1870170 := by exact prefixLift 1870170
  have htrace : WordTrace (prefixWord ++ tailWord_1870170) baseStart_1870170 baseEnd_1870170 := by
    simpa [prefixWord, tailWord_1870170, baseEnd_1870170] using wordTrace_append hprefix tailTrace_1870170
  have hstable : (prefixWord ++ tailWord_1870170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870170).length < 2 ^ (prefixWord ++ tailWord_1870170).sum := by decide
  have hdescent : baseEnd_1870170 < baseStart_1870170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870245 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 1, 6]
def baseStart_1870245 : Nat := 118140960795 + 1870245 * 2 ^ 59
def prefixEnd_1870245 : Nat := 4983230072969 + 3 ^ 40 * 1870245 * 2
def baseEnd_1870245 : Nat := 640223084445426927690937

theorem tailTrace_1870245 : CollatzResearch.WordTrace tailWord_1870245 prefixEnd_1870245 640223084445426927690937 := by
  unfold tailWord_1870245
  simp only [CollatzResearch.WordTrace]
  refine ⟨68213439109429252261388189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45475626072952834840925459 68213439109429252261388189)
  ·
    refine ⟨25580039666035969598020571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68213439109429252261388189 25580039666035969598020571)
    ·
      refine ⟨38370059499053954397030857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25580039666035969598020571 38370059499053954397030857)
      ·
        refine ⟨28777544624290465797773143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38370059499053954397030857 28777544624290465797773143)
        ·
          refine ⟨43166316936435698696659715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28777544624290465797773143 43166316936435698696659715)
          ·
            refine ⟨64749475404653548044989573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43166316936435698696659715 64749475404653548044989573)
            ·
              refine ⟨12140526638372540258435545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64749475404653548044989573 12140526638372540258435545)
              ·
                refine ⟨9105394978779405193826659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12140526638372540258435545 9105394978779405193826659)
                ·
                  refine ⟨13658092468169107790739989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9105394978779405193826659 13658092468169107790739989)
                  ·
                    refine ⟨640223084445426927690937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13658092468169107790739989 640223084445426927690937)
                    ·
                      rfl

theorem cell22_1870245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_1870245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870245 prefixEnd_1870245 := by exact prefixLift 1870245
  have htrace : WordTrace (prefixWord ++ tailWord_1870245) baseStart_1870245 baseEnd_1870245 := by
    simpa [prefixWord, tailWord_1870245, baseEnd_1870245] using wordTrace_append hprefix tailTrace_1870245
  have hstable : (prefixWord ++ tailWord_1870245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870245).length < 2 ^ (prefixWord ++ tailWord_1870245).sum := by decide
  have hdescent : baseEnd_1870245 < baseStart_1870245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870247 : List Nat := [1, 1, 6, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1870247 : Nat := 118140960795 + 1870247 * 2 ^ 59
def prefixEnd_1870247 : Nat := 4983230072969 + 3 ^ 40 * 1870247 * 2
def baseEnd_1870247 : Nat := 640223769086299589140931

theorem tailTrace_1870247 : CollatzResearch.WordTrace tailWord_1870247 prefixEnd_1870247 640223769086299589140931 := by
  unfold tailWord_1870247
  simp only [CollatzResearch.WordTrace]
  refine ⟨68213512055422006602960995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45475674703614671068640663 68213512055422006602960995)
  ·
    refine ⟨102320268083133009904441493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68213512055422006602960995 102320268083133009904441493)
    ·
      refine ⟨4796262566396859839270695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102320268083133009904441493 4796262566396859839270695)
      ·
        refine ⟨7194393849595289758906043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4796262566396859839270695 7194393849595289758906043)
        ·
          refine ⟨10791590774392934638359065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7194393849595289758906043 10791590774392934638359065)
          ·
            refine ⟨8093693080794700978769299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10791590774392934638359065 8093693080794700978769299)
            ·
              refine ⟨12140539621192051468153949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8093693080794700978769299 12140539621192051468153949)
              ·
                refine ⟨4552702357947019300557731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12140539621192051468153949 4552702357947019300557731)
                ·
                  refine ⟨6829053536920528950836597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4552702357947019300557731 6829053536920528950836597)
                  ·
                    refine ⟨640223769086299589140931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6829053536920528950836597 640223769086299589140931)
                    ·
                      rfl

theorem cell22_1870247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1870247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870247 prefixEnd_1870247 := by exact prefixLift 1870247
  have htrace : WordTrace (prefixWord ++ tailWord_1870247) baseStart_1870247 baseEnd_1870247 := by
    simpa [prefixWord, tailWord_1870247, baseEnd_1870247] using wordTrace_append hprefix tailTrace_1870247
  have hstable : (prefixWord ++ tailWord_1870247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870247).length < 2 ^ (prefixWord ++ tailWord_1870247).sum := by decide
  have hdescent : baseEnd_1870247 < baseStart_1870247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870343 : List Nat := [1, 1, 4, 3, 4, 1, 1, 1, 3, 3]
def baseStart_1870343 : Nat := 118140960795 + 1870343 * 2 ^ 59
def prefixEnd_1870343 : Nat := 4983230072969 + 3 ^ 40 * 1870343 * 2
def baseEnd_1870343 : Nat := 640256631848187338740637

theorem tailTrace_1870343 : CollatzResearch.WordTrace tailWord_1870343 prefixEnd_1870343 640256631848187338740637 := by
  unfold tailWord_1870343
  simp only [CollatzResearch.WordTrace]
  refine ⟨68217013463074214998455683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45478008975382809998970455 68217013463074214998455683)
  ·
    refine ⟨102325520194611322497683525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68217013463074214998455683 102325520194611322497683525)
    ·
      refine ⟨19186035036489622968315661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102325520194611322497683525 19186035036489622968315661)
      ·
        refine ⟨7194763138683608613118373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19186035036489622968315661 7194763138683608613118373)
        ·
          refine ⟨1349018088503176614959695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7194763138683608613118373 1349018088503176614959695)
          ·
            refine ⟨2023527132754764922439543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349018088503176614959695 2023527132754764922439543)
            ·
              refine ⟨3035290699132147383659315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2023527132754764922439543 3035290699132147383659315)
              ·
                refine ⟨4552936048698221075488973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3035290699132147383659315 4552936048698221075488973)
                ·
                  refine ⟨1707351018261832903308365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4552936048698221075488973 1707351018261832903308365)
                  ·
                    refine ⟨640256631848187338740637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1707351018261832903308365 640256631848187338740637)
                    ·
                      rfl

theorem cell22_1870343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_1870343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870343 prefixEnd_1870343 := by exact prefixLift 1870343
  have htrace : WordTrace (prefixWord ++ tailWord_1870343) baseStart_1870343 baseEnd_1870343 := by
    simpa [prefixWord, tailWord_1870343, baseEnd_1870343] using wordTrace_append hprefix tailTrace_1870343
  have hstable : (prefixWord ++ tailWord_1870343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870343).length < 2 ^ (prefixWord ++ tailWord_1870343).sum := by decide
  have hdescent : baseEnd_1870343 < baseStart_1870343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870356 : List Nat := [2, 4, 3, 1, 1, 2, 1, 3, 5]
def baseStart_1870356 : Nat := 118140960795 + 1870356 * 2 ^ 59
def prefixEnd_1870356 : Nat := 4983230072969 + 3 ^ 40 * 1870356 * 2
def baseEnd_1870356 : Nat := 213420360671286546055199

theorem tailTrace_1870356 : CollatzResearch.WordTrace tailWord_1870356 prefixEnd_1870356 213420360671286546055199 := by
  unfold tailWord_1870356
  simp only [CollatzResearch.WordTrace]
  refine ⟨34108743806013559109339461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45478325074684745479119281 34108743806013559109339461)
  ·
    refine ⟨6395389463627542333001149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34108743806013559109339461 6395389463627542333001149)
    ·
      refine ⟨2398271048860328374875431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6395389463627542333001149 2398271048860328374875431)
      ·
        refine ⟨3597406573290492562313147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2398271048860328374875431 3597406573290492562313147)
        ·
          refine ⟨5396109859935738843469721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3597406573290492562313147 5396109859935738843469721)
          ·
            refine ⟨4047082394951804132602291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5396109859935738843469721 4047082394951804132602291)
            ·
              refine ⟨6070623592427706198903437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4047082394951804132602291 6070623592427706198903437)
              ·
                refine ⟨2276483847160389824588789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6070623592427706198903437 2276483847160389824588789)
                ·
                  refine ⟨213420360671286546055199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2276483847160389824588789 213420360671286546055199)
                  ·
                    rfl

theorem cell22_1870356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_1870356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870356 prefixEnd_1870356 := by exact prefixLift 1870356
  have htrace : WordTrace (prefixWord ++ tailWord_1870356) baseStart_1870356 baseEnd_1870356 := by
    simpa [prefixWord, tailWord_1870356, baseEnd_1870356] using wordTrace_append hprefix tailTrace_1870356
  have hstable : (prefixWord ++ tailWord_1870356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870356).length < 2 ^ (prefixWord ++ tailWord_1870356).sum := by decide
  have hdescent : baseEnd_1870356 < baseStart_1870356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870401 : List Nat := [1, 2, 5, 1, 1, 3, 1, 4, 4]
def baseStart_1870401 : Nat := 118140960795 + 1870401 * 2 ^ 59
def prefixEnd_1870401 : Nat := 4983230072969 + 3 ^ 40 * 1870401 * 2
def baseEnd_1870401 : Nat := 213425495477831506930153

theorem tailTrace_1870401 : CollatzResearch.WordTrace tailWord_1870401 prefixEnd_1870401 213425495477831506930153 := by
  unfold tailWord_1870401
  simp only [CollatzResearch.WordTrace]
  refine ⟨68219128896864090904067057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45479419264576060602711371 68219128896864090904067057)
  ·
    refine ⟨51164346672648068178050293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68219128896864090904067057 51164346672648068178050293)
    ·
      refine ⟨4796657500560756391692215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51164346672648068178050293 4796657500560756391692215)
      ·
        refine ⟨7194986250841134587538323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4796657500560756391692215 7194986250841134587538323)
        ·
          refine ⟨10792479376261701881307485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7194986250841134587538323 10792479376261701881307485)
          ·
            refine ⟨4047179766098138205490307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10792479376261701881307485 4047179766098138205490307)
            ·
              refine ⟨6070769649147207308235461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4047179766098138205490307 6070769649147207308235461)
              ·
                refine ⟨1138269309215101370294149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6070769649147207308235461 1138269309215101370294149)
                ·
                  refine ⟨213425495477831506930153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1138269309215101370294149 213425495477831506930153)
                  ·
                    rfl

theorem cell22_1870401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 4].length) (baseStart_1870401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870401 prefixEnd_1870401 := by exact prefixLift 1870401
  have htrace : WordTrace (prefixWord ++ tailWord_1870401) baseStart_1870401 baseEnd_1870401 := by
    simpa [prefixWord, tailWord_1870401, baseEnd_1870401] using wordTrace_append hprefix tailTrace_1870401
  have hstable : (prefixWord ++ tailWord_1870401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870401).length < 2 ^ (prefixWord ++ tailWord_1870401).sum := by decide
  have hdescent : baseEnd_1870401 < baseStart_1870401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870450 : List Nat := [3, 2, 1, 2, 5, 1, 1, 2, 2, 3]
def baseStart_1870450 : Nat := 118140960795 + 1870450 * 2 ^ 59
def prefixEnd_1870450 : Nat := 4983230072969 + 3 ^ 40 * 1870450 * 2
def baseEnd_1870450 : Nat := 640293260134874726315309

theorem tailTrace_1870450 : CollatzResearch.WordTrace tailWord_1870450 prefixEnd_1870450 640293260134874726315309 := by
  unfold tailWord_1870450
  simp only [CollatzResearch.WordTrace]
  refine ⟨17055229018421643068150201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45480610715791048181733869 17055229018421643068150201)
  ·
    refine ⟨12791421763816232301112651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17055229018421643068150201 12791421763816232301112651)
    ·
      refine ⟨19187132645724348451668977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12791421763816232301112651 19187132645724348451668977)
      ·
        refine ⟨14390349484293261338751733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19187132645724348451668977 14390349484293261338751733)
        ·
          refine ⟨1349095264152493250507975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14390349484293261338751733 1349095264152493250507975)
          ·
            refine ⟨2023642896228739875761963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349095264152493250507975 2023642896228739875761963)
            ·
              refine ⟨3035464344343109813642945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2023642896228739875761963 3035464344343109813642945)
              ·
                refine ⟨2276598258257332360232209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3035464344343109813642945 2276598258257332360232209)
                ·
                  refine ⟨1707448693692999270174157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2276598258257332360232209 1707448693692999270174157)
                  ·
                    refine ⟨640293260134874726315309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1707448693692999270174157 640293260134874726315309)
                    ·
                      rfl

theorem cell22_1870450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_1870450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870450 prefixEnd_1870450 := by exact prefixLift 1870450
  have htrace : WordTrace (prefixWord ++ tailWord_1870450) baseStart_1870450 baseEnd_1870450 := by
    simpa [prefixWord, tailWord_1870450, baseEnd_1870450] using wordTrace_append hprefix tailTrace_1870450
  have hstable : (prefixWord ++ tailWord_1870450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870450).length < 2 ^ (prefixWord ++ tailWord_1870450).sum := by decide
  have hdescent : baseEnd_1870450 < baseStart_1870450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870538 : List Nat := [3, 1, 2, 1, 4, 3, 1, 2, 1, 4]
def baseStart_1870538 : Nat := 118140960795 + 1870538 * 2 ^ 59
def prefixEnd_1870538 : Nat := 4983230072969 + 3 ^ 40 * 1870538 * 2
def baseEnd_1870538 : Nat := 640323384333271830115039

theorem tailTrace_1870538 : CollatzResearch.WordTrace tailWord_1870538 prefixEnd_1870538 640323384333271830115039 := by
  unfold tailWord_1870538
  simp only [CollatzResearch.WordTrace]
  refine ⟨17056031424341940825451067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45482750464911842201202845 17056031424341940825451067)
  ·
    refine ⟨25584047136512911238176601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17056031424341940825451067 25584047136512911238176601)
    ·
      refine ⟨19188035352384683428632451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25584047136512911238176601 19188035352384683428632451)
      ·
        refine ⟨28782053028577025142948677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19188035352384683428632451 28782053028577025142948677)
        ·
          refine ⟨5396634942858192214302877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28782053028577025142948677 5396634942858192214302877)
          ·
            refine ⟨2023738103571822080363579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5396634942858192214302877 2023738103571822080363579)
            ·
              refine ⟨3035607155357733120545369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2023738103571822080363579 3035607155357733120545369)
              ·
                refine ⟨2276705366518299840409027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3035607155357733120545369 2276705366518299840409027)
                ·
                  refine ⟨3415058049777449760613541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2276705366518299840409027 3415058049777449760613541)
                  ·
                    refine ⟨640323384333271830115039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3415058049777449760613541 640323384333271830115039)
                    ·
                      rfl

theorem cell22_1870538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_1870538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870538 prefixEnd_1870538 := by exact prefixLift 1870538
  have htrace : WordTrace (prefixWord ++ tailWord_1870538) baseStart_1870538 baseEnd_1870538 := by
    simpa [prefixWord, tailWord_1870538, baseEnd_1870538] using wordTrace_append hprefix tailTrace_1870538
  have hstable : (prefixWord ++ tailWord_1870538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870538).length < 2 ^ (prefixWord ++ tailWord_1870538).sum := by decide
  have hdescent : baseEnd_1870538 < baseStart_1870538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870626 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 7]
def baseStart_1870626 : Nat := 118140960795 + 1870626 * 2 ^ 59
def prefixEnd_1870626 : Nat := 4983230072969 + 3 ^ 40 * 1870626 * 2
def baseEnd_1870626 : Nat := 213451169510556311304923

theorem tailTrace_1870626 : CollatzResearch.WordTrace tailWord_1870626 prefixEnd_1870626 213451169510556311304923 := by
  unfold tailWord_1870626
  simp only [CollatzResearch.WordTrace]
  refine ⟨17056833830262238582751933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45484890214032636220671821 17056833830262238582751933)
  ·
    refine ⟨6396312686348339468531975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17056833830262238582751933 6396312686348339468531975)
    ·
      refine ⟨9594469029522509202797963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6396312686348339468531975 9594469029522509202797963)
      ·
        refine ⟨14391703544283763804196945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9594469029522509202797963 14391703544283763804196945)
        ·
          refine ⟨10793777658212822853147709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14391703544283763804196945 10793777658212822853147709)
          ·
            refine ⟨4047666621829808569930391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10793777658212822853147709 4047666621829808569930391)
            ·
              refine ⟨6071499932744712854895587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4047666621829808569930391 6071499932744712854895587)
              ·
                refine ⟨9107249899117069282343381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6071499932744712854895587 9107249899117069282343381)
                ·
                  refine ⟨213451169510556311304923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9107249899117069282343381 213451169510556311304923)
                  ·
                    rfl

theorem cell22_1870626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_1870626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870626 prefixEnd_1870626 := by exact prefixLift 1870626
  have htrace : WordTrace (prefixWord ++ tailWord_1870626) baseStart_1870626 baseEnd_1870626 := by
    simpa [prefixWord, tailWord_1870626, baseEnd_1870626] using wordTrace_append hprefix tailTrace_1870626
  have hstable : (prefixWord ++ tailWord_1870626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870626).length < 2 ^ (prefixWord ++ tailWord_1870626).sum := by decide
  have hdescent : baseEnd_1870626 < baseStart_1870626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870643 : List Nat := [1, 1, 1, 2, 6, 2, 3, 1, 5]
def baseStart_1870643 : Nat := 118140960795 + 1870643 * 2 ^ 59
def prefixEnd_1870643 : Nat := 4983230072969 + 3 ^ 40 * 1870643 * 2
def baseEnd_1870643 : Nat := 213453109326362185413239

theorem tailTrace_1870643 : CollatzResearch.WordTrace tailWord_1870643 prefixEnd_1870643 213453109326362185413239 := by
  unfold tailWord_1870643
  simp only [CollatzResearch.WordTrace]
  refine ⟨68227955361987366234376583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45485303574658244156251055 68227955361987366234376583)
  ·
    refine ⟨102341933042981049351564875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68227955361987366234376583 102341933042981049351564875)
    ·
      refine ⟨153512899564471574027347313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102341933042981049351564875 153512899564471574027347313)
      ·
        refine ⟨115134674673353680520510485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153512899564471574027347313 115134674673353680520510485)
        ·
          refine ⟨5396937875313453774398929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115134674673353680520510485 5396937875313453774398929)
          ·
            refine ⟨4047703406485090330799197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5396937875313453774398929 4047703406485090330799197)
            ·
              refine ⟨1517888777431908874049699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4047703406485090330799197 1517888777431908874049699)
              ·
                refine ⟨2276833166147863311074549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1517888777431908874049699 2276833166147863311074549)
                ·
                  refine ⟨213453109326362185413239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2276833166147863311074549 213453109326362185413239)
                  ·
                    rfl

theorem cell22_1870643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 5].length) (baseStart_1870643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870643 prefixEnd_1870643 := by exact prefixLift 1870643
  have htrace : WordTrace (prefixWord ++ tailWord_1870643) baseStart_1870643 baseEnd_1870643 := by
    simpa [prefixWord, tailWord_1870643, baseEnd_1870643] using wordTrace_append hprefix tailTrace_1870643
  have hstable : (prefixWord ++ tailWord_1870643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870643).length < 2 ^ (prefixWord ++ tailWord_1870643).sum := by decide
  have hdescent : baseEnd_1870643 < baseStart_1870643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870699 : List Nat := [1, 1, 1, 1, 2, 2, 5, 9]
def baseStart_1870699 : Nat := 118140960795 + 1870699 * 2 ^ 59
def prefixEnd_1870699 : Nat := 4983230072969 + 3 ^ 40 * 1870699 * 2
def baseEnd_1870699 : Nat := 71153166435946786315505

theorem tailTrace_1870699 : CollatzResearch.WordTrace tailWord_1870699 prefixEnd_1870699 71153166435946786315505 := by
  unfold tailWord_1870699
  simp only [CollatzResearch.WordTrace]
  refine ⟨68229997849784487798415151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45486665233189658532276767 68229997849784487798415151)
  ·
    refine ⟨102344996774676731697622727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68229997849784487798415151 102344996774676731697622727)
    ·
      refine ⟨153517495162015097546434091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102344996774676731697622727 153517495162015097546434091)
      ·
        refine ⟨230276242743022646319651137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153517495162015097546434091 230276242743022646319651137)
        ·
          refine ⟨172707182057266984739738353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230276242743022646319651137 172707182057266984739738353)
          ·
            refine ⟨129530386542950238554803765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172707182057266984739738353 129530386542950238554803765)
            ·
              refine ⟨12143473738401584864512853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129530386542950238554803765 12143473738401584864512853)
              ·
                refine ⟨71153166435946786315505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12143473738401584864512853 71153166435946786315505)
                ·
                  rfl

theorem cell22_1870699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 9].length) (baseStart_1870699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870699 prefixEnd_1870699 := by exact prefixLift 1870699
  have htrace : WordTrace (prefixWord ++ tailWord_1870699) baseStart_1870699 baseEnd_1870699 := by
    simpa [prefixWord, tailWord_1870699, baseEnd_1870699] using wordTrace_append hprefix tailTrace_1870699
  have hstable : (prefixWord ++ tailWord_1870699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870699).length < 2 ^ (prefixWord ++ tailWord_1870699).sum := by decide
  have hdescent : baseEnd_1870699 < baseStart_1870699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870701 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_1870701 : Nat := 118140960795 + 1870701 * 2 ^ 59
def prefixEnd_1870701 : Nat := 4983230072969 + 3 ^ 40 * 1870701 * 2
def baseEnd_1870701 : Nat := 640379182564393738289539

theorem tailTrace_1870701 : CollatzResearch.WordTrace tailWord_1870701 prefixEnd_1870701 640379182564393738289539 := by
  unfold tailWord_1870701
  simp only [CollatzResearch.WordTrace]
  refine ⟨68230070795777242139987957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45486713863851494759991971 68230070795777242139987957)
  ·
    refine ⟨6396569137104116450623871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68230070795777242139987957 6396569137104116450623871)
    ·
      refine ⟨9594853705656174675935807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6396569137104116450623871 9594853705656174675935807)
      ·
        refine ⟨14392280558484262013903711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9594853705656174675935807 14392280558484262013903711)
        ·
          refine ⟨21588420837726393020855567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14392280558484262013903711 21588420837726393020855567)
          ·
            refine ⟨32382631256589589531283351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21588420837726393020855567 32382631256589589531283351)
            ·
              refine ⟨48573946884884384296925027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32382631256589589531283351 48573946884884384296925027)
              ·
                refine ⟨72860920327326576445387541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48573946884884384296925027 72860920327326576445387541)
                ·
                  refine ⟨3415355640343433270877541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72860920327326576445387541 3415355640343433270877541)
                  ·
                    refine ⟨640379182564393738289539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3415355640343433270877541 640379182564393738289539)
                    ·
                      rfl

theorem cell22_1870701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_1870701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870701 prefixEnd_1870701 := by exact prefixLift 1870701
  have htrace : WordTrace (prefixWord ++ tailWord_1870701) baseStart_1870701 baseEnd_1870701 := by
    simpa [prefixWord, tailWord_1870701, baseEnd_1870701] using wordTrace_append hprefix tailTrace_1870701
  have hstable : (prefixWord ++ tailWord_1870701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870701).length < 2 ^ (prefixWord ++ tailWord_1870701).sum := by decide
  have hdescent : baseEnd_1870701 < baseStart_1870701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870761 : List Nat := [1, 2, 1, 1, 1, 1, 5, 5, 5]
def baseStart_1870761 : Nat := 118140960795 + 1870761 * 2 ^ 59
def prefixEnd_1870761 : Nat := 4983230072969 + 3 ^ 40 * 1870761 * 2
def baseEnd_1870761 : Nat := 213466573930191193929785

theorem tailTrace_1870761 : CollatzResearch.WordTrace tailWord_1870761 prefixEnd_1870761 213466573930191193929785 := by
  unfold tailWord_1870761
  simp only [CollatzResearch.WordTrace]
  refine ⟨68232259175559872387172137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45488172783706581591448091 68232259175559872387172137)
  ·
    refine ⟨51174194381669904290379103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68232259175559872387172137 51174194381669904290379103)
    ·
      refine ⟨76761291572504856435568655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51174194381669904290379103 76761291572504856435568655)
      ·
        refine ⟨115141937358757284653352983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76761291572504856435568655 115141937358757284653352983)
        ·
          refine ⟨172712906038135926980029475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115141937358757284653352983 172712906038135926980029475)
          ·
            refine ⟨259069359057203890470044213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172712906038135926980029475 259069359057203890470044213)
            ·
              refine ⟨24287752411612864731566645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 259069359057203890470044213 24287752411612864731566645)
              ·
                refine ⟨2276976788588706068584373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24287752411612864731566645 2276976788588706068584373)
                ·
                  refine ⟨213466573930191193929785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2276976788588706068584373 213466573930191193929785)
                  ·
                    rfl

theorem cell22_1870761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 5].length) (baseStart_1870761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870761 prefixEnd_1870761 := by exact prefixLift 1870761
  have htrace : WordTrace (prefixWord ++ tailWord_1870761) baseStart_1870761 baseEnd_1870761 := by
    simpa [prefixWord, tailWord_1870761, baseEnd_1870761] using wordTrace_append hprefix tailTrace_1870761
  have hstable : (prefixWord ++ tailWord_1870761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870761).length < 2 ^ (prefixWord ++ tailWord_1870761).sum := by decide
  have hdescent : baseEnd_1870761 < baseStart_1870761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870782 : List Nat := [4, 2, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_1870782 : Nat := 118140960795 + 1870782 * 2 ^ 59
def prefixEnd_1870782 : Nat := 4983230072969 + 3 ^ 40 * 1870782 * 2
def baseEnd_1870782 : Nat := 640406910519736527014291

theorem tailTrace_1870782 : CollatzResearch.WordTrace tailWord_1870782 prefixEnd_1870782 640406910519736527014291 := by
  unfold tailWord_1870782
  simp only [CollatzResearch.WordTrace]
  refine ⟨8529128138560474121710825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45488683405655861982457733 8529128138560474121710825)
  ·
    refine ⟨6396846103920355591283119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8529128138560474121710825 6396846103920355591283119)
    ·
      refine ⟨9595269155880533386924679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6396846103920355591283119 9595269155880533386924679)
      ·
        refine ⟨14392903733820800080387019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9595269155880533386924679 14392903733820800080387019)
        ·
          refine ⟨21589355600731200120580529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14392903733820800080387019 21589355600731200120580529)
          ·
            refine ⟨16192016700548400090435397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21589355600731200120580529 16192016700548400090435397)
            ·
              refine ⟨3036003131352825016956637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16192016700548400090435397 3036003131352825016956637)
              ·
                refine ⟨1138501174257309381358739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3036003131352825016956637 1138501174257309381358739)
                ·
                  refine ⟨1707751761385964072038109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1138501174257309381358739 1707751761385964072038109)
                  ·
                    refine ⟨640406910519736527014291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1707751761385964072038109 640406910519736527014291)
                    ·
                      rfl

theorem cell22_1870782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_1870782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870782 prefixEnd_1870782 := by exact prefixLift 1870782
  have htrace : WordTrace (prefixWord ++ tailWord_1870782) baseStart_1870782 baseEnd_1870782 := by
    simpa [prefixWord, tailWord_1870782, baseEnd_1870782] using wordTrace_append hprefix tailTrace_1870782
  have hstable : (prefixWord ++ tailWord_1870782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870782).length < 2 ^ (prefixWord ++ tailWord_1870782).sum := by decide
  have hdescent : baseEnd_1870782 < baseStart_1870782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870823 : List Nat := [1, 1, 5, 2, 2, 1, 2, 2, 6]
def baseStart_1870823 : Nat := 118140960795 + 1870823 * 2 ^ 59
def prefixEnd_1870823 : Nat := 4983230072969 + 3 ^ 40 * 1870823 * 2
def baseEnd_1870823 : Nat := 213473648552542028913055

theorem tailTrace_1870823 : CollatzResearch.WordTrace tailWord_1870823 prefixEnd_1870823 213473648552542028913055 := by
  unfold tailWord_1870823
  simp only [CollatzResearch.WordTrace]
  refine ⟨68234520501335256975929123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45489680334223504650619415 68234520501335256975929123)
  ·
    refine ⟨102351780752002885463893685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68234520501335256975929123 102351780752002885463893685)
    ·
      refine ⟨9595479445500270512240033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102351780752002885463893685 9595479445500270512240033)
      ·
        refine ⟨7196609584125202884180025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9595479445500270512240033 7196609584125202884180025)
        ·
          refine ⟨5397457188093902163135019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7196609584125202884180025 5397457188093902163135019)
          ·
            refine ⟨8096185782140853244702529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5397457188093902163135019 8096185782140853244702529)
            ·
              refine ⟨6072139336605639933526897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8096185782140853244702529 6072139336605639933526897)
              ·
                refine ⟨4554104502454229950145173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6072139336605639933526897 4554104502454229950145173)
                ·
                  refine ⟨213473648552542028913055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4554104502454229950145173 213473648552542028913055)
                  ·
                    rfl

theorem cell22_1870823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 6].length) (baseStart_1870823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870823 prefixEnd_1870823 := by exact prefixLift 1870823
  have htrace : WordTrace (prefixWord ++ tailWord_1870823) baseStart_1870823 baseEnd_1870823 := by
    simpa [prefixWord, tailWord_1870823, baseEnd_1870823] using wordTrace_append hprefix tailTrace_1870823
  have hstable : (prefixWord ++ tailWord_1870823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870823).length < 2 ^ (prefixWord ++ tailWord_1870823).sum := by decide
  have hdescent : baseEnd_1870823 < baseStart_1870823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870853 : List Nat := [1, 3, 1, 1, 2, 3, 3, 2, 2, 4]
def baseStart_1870853 : Nat := 118140960795 + 1870853 * 2 ^ 59
def prefixEnd_1870853 : Nat := 4983230072969 + 3 ^ 40 * 1870853 * 2
def baseEnd_1870853 : Nat := 640431215270716008489073

theorem tailTrace_1870853 : CollatzResearch.WordTrace tailWord_1870853 prefixEnd_1870853 640431215270716008489073 := by
  unfold tailWord_1870853
  simp only [CollatzResearch.WordTrace]
  refine ⟨68235614691226572099521213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45490409794151048066347475 68235614691226572099521213)
  ·
    refine ⟨25588355509209964537320455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68235614691226572099521213 25588355509209964537320455)
    ·
      refine ⟨38382533263814946805980683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25588355509209964537320455 38382533263814946805980683)
      ·
        refine ⟨57573799895722420208971025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38382533263814946805980683 57573799895722420208971025)
        ·
          refine ⟨43180349921791815156728269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57573799895722420208971025 43180349921791815156728269)
          ·
            refine ⟨16192631220671930683773101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43180349921791815156728269 16192631220671930683773101)
            ·
              refine ⟨6072236707751974006414913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16192631220671930683773101 6072236707751974006414913)
              ·
                refine ⟨4554177530813980504811185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6072236707751974006414913 4554177530813980504811185)
                ·
                  refine ⟨3415633148110485378608389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4554177530813980504811185 3415633148110485378608389)
                  ·
                    refine ⟨640431215270716008489073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3415633148110485378608389 640431215270716008489073)
                    ·
                      rfl

theorem cell22_1870853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_1870853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870853 prefixEnd_1870853 := by exact prefixLift 1870853
  have htrace : WordTrace (prefixWord ++ tailWord_1870853) baseStart_1870853 baseEnd_1870853 := by
    simpa [prefixWord, tailWord_1870853, baseEnd_1870853] using wordTrace_append hprefix tailTrace_1870853
  have hstable : (prefixWord ++ tailWord_1870853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870853).length < 2 ^ (prefixWord ++ tailWord_1870853).sum := by decide
  have hdescent : baseEnd_1870853 < baseStart_1870853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870855 : List Nat := [1, 1, 4, 3, 1, 1, 2, 4, 2, 3]
def baseStart_1870855 : Nat := 118140960795 + 1870855 * 2 ^ 59
def prefixEnd_1870855 : Nat := 4983230072969 + 3 ^ 40 * 1870855 * 2
def baseEnd_1870855 : Nat := 640431899911588669939067

theorem tailTrace_1870855 : CollatzResearch.WordTrace tailWord_1870855 prefixEnd_1870855 640431899911588669939067 := by
  unfold tailWord_1870855
  simp only [CollatzResearch.WordTrace]
  refine ⟨68235687637219326441094019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45490458424812884294062679 68235687637219326441094019)
  ·
    refine ⟨102353531455828989661641029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68235687637219326441094019 102353531455828989661641029)
    ·
      refine ⟨19191287147967935561557693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102353531455828989661641029 19191287147967935561557693)
      ·
        refine ⟨7196732680487975835584135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19191287147967935561557693 7196732680487975835584135)
        ·
          refine ⟨10795099020731963753376203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7196732680487975835584135 10795099020731963753376203)
          ·
            refine ⟨16192648531097945630064305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10795099020731963753376203 16192648531097945630064305)
            ·
              refine ⟨12144486398323459222548229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16192648531097945630064305 12144486398323459222548229)
              ·
                refine ⟨2277091199685648604227793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12144486398323459222548229 2277091199685648604227793)
                ·
                  refine ⟨1707818399764236453170845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2277091199685648604227793 1707818399764236453170845)
                  ·
                    refine ⟨640431899911588669939067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1707818399764236453170845 640431899911588669939067)
                    ·
                      rfl

theorem cell22_1870855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_1870855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870855 prefixEnd_1870855 := by exact prefixLift 1870855
  have htrace : WordTrace (prefixWord ++ tailWord_1870855) baseStart_1870855 baseEnd_1870855 := by
    simpa [prefixWord, tailWord_1870855, baseEnd_1870855] using wordTrace_append hprefix tailTrace_1870855
  have hstable : (prefixWord ++ tailWord_1870855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870855).length < 2 ^ (prefixWord ++ tailWord_1870855).sum := by decide
  have hdescent : baseEnd_1870855 < baseStart_1870855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870872 : List Nat := [2, 1, 2, 3, 2, 2, 4, 1, 2, 3]
def baseStart_1870872 : Nat := 118140960795 + 1870872 * 2 ^ 59
def prefixEnd_1870872 : Nat := 4983230072969 + 3 ^ 40 * 1870872 * 2
def baseEnd_1870872 : Nat := 640437719359006292264015

theorem tailTrace_1870872 : CollatzResearch.WordTrace tailWord_1870872 prefixEnd_1870872 640437719359006292264015 := by
  unfold tailWord_1870872
  simp only [CollatzResearch.WordTrace]
  refine ⟨34118153839078869172231435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45490871785438492229641913 34118153839078869172231435)
  ·
    refine ⟨51177230758618303758347153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34118153839078869172231435 51177230758618303758347153)
    ·
      refine ⟨38382923068963727818760365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51177230758618303758347153 38382923068963727818760365)
      ·
        refine ⟨14393596150861397932035137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38382923068963727818760365 14393596150861397932035137)
        ·
          refine ⟨10795197113146048449026353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14393596150861397932035137 10795197113146048449026353)
          ·
            refine ⟨8096397834859536336769765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10795197113146048449026353 8096397834859536336769765)
            ·
              refine ⟨1518074594036163063144331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8096397834859536336769765 1518074594036163063144331)
              ·
                refine ⟨2277111891054244594716497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1518074594036163063144331 2277111891054244594716497)
                ·
                  refine ⟨1707833918290683446037373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2277111891054244594716497 1707833918290683446037373)
                  ·
                    refine ⟨640437719359006292264015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1707833918290683446037373 640437719359006292264015)
                    ·
                      rfl

theorem cell22_1870872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 2, 3].length) (baseStart_1870872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870872 prefixEnd_1870872 := by exact prefixLift 1870872
  have htrace : WordTrace (prefixWord ++ tailWord_1870872) baseStart_1870872 baseEnd_1870872 := by
    simpa [prefixWord, tailWord_1870872, baseEnd_1870872] using wordTrace_append hprefix tailTrace_1870872
  have hstable : (prefixWord ++ tailWord_1870872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870872).length < 2 ^ (prefixWord ++ tailWord_1870872).sum := by decide
  have hdescent : baseEnd_1870872 < baseStart_1870872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870887 : List Nat := [1, 1, 7, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1870887 : Nat := 118140960795 + 1870887 * 2 ^ 59
def prefixEnd_1870887 : Nat := 4983230072969 + 3 ^ 40 * 1870887 * 2
def baseEnd_1870887 : Nat := 640442854165551253138969

theorem tailTrace_1870887 : CollatzResearch.WordTrace tailWord_1870887 prefixEnd_1870887 640442854165551253138969 := by
  unfold tailWord_1870887
  simp only [CollatzResearch.WordTrace]
  refine ⟨68236854773103395906258915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45491236515402263937505943 68236854773103395906258915)
  ·
    refine ⟨102355282159655093859388373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68236854773103395906258915 102355282159655093859388373)
    ·
      refine ⟨2398951925616916262329415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 102355282159655093859388373 2398951925616916262329415)
      ·
        refine ⟨3598427888425374393494123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2398951925616916262329415 3598427888425374393494123)
        ·
          refine ⟨5397641832638061590241185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3598427888425374393494123 5397641832638061590241185)
          ·
            refine ⟨4048231374478546192680889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5397641832638061590241185 4048231374478546192680889)
            ·
              refine ⟨3036173530858909644510667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4048231374478546192680889 3036173530858909644510667)
              ·
                refine ⟨4554260296288364466766001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3036173530858909644510667 4554260296288364466766001)
                ·
                  refine ⟨3415695222216273350074501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4554260296288364466766001 3415695222216273350074501)
                  ·
                    refine ⟨640442854165551253138969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3415695222216273350074501 640442854165551253138969)
                    ·
                      rfl

theorem cell22_1870887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1870887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870887 prefixEnd_1870887 := by exact prefixLift 1870887
  have htrace : WordTrace (prefixWord ++ tailWord_1870887) baseStart_1870887 baseEnd_1870887 := by
    simpa [prefixWord, tailWord_1870887, baseEnd_1870887] using wordTrace_append hprefix tailTrace_1870887
  have hstable : (prefixWord ++ tailWord_1870887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870887).length < 2 ^ (prefixWord ++ tailWord_1870887).sum := by decide
  have hdescent : baseEnd_1870887 < baseStart_1870887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870930 : List Nat := [3, 2, 2, 1, 3, 1, 2, 3, 5]
def baseStart_1870930 : Nat := 118140960795 + 1870930 * 2 ^ 59
def prefixEnd_1870930 : Nat := 4983230072969 + 3 ^ 40 * 1870930 * 2
def baseEnd_1870930 : Nat := 213485857981437824771279

theorem tailTrace_1870930 : CollatzResearch.WordTrace tailWord_1870930 prefixEnd_1870930 213485857981437824771279 := by
  unfold tailWord_1870930
  simp only [CollatzResearch.WordTrace]
  refine ⟨17059605777986903562518561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45492282074631742833382829 17059605777986903562518561)
  ·
    refine ⟨12794704333490177671888921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17059605777986903562518561 12794704333490177671888921)
    ·
      refine ⟨9596028250117633253916691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12794704333490177671888921 9596028250117633253916691)
      ·
        refine ⟨14394042375176449880875037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9596028250117633253916691 14394042375176449880875037)
        ·
          refine ⟨5397765890691168705328139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14394042375176449880875037 5397765890691168705328139)
          ·
            refine ⟨8096648836036753057992209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5397765890691168705328139 8096648836036753057992209)
            ·
              refine ⟨6072486627027564793494157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8096648836036753057992209 6072486627027564793494157)
              ·
                refine ⟨2277182485135336797560309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6072486627027564793494157 2277182485135336797560309)
                ·
                  refine ⟨213485857981437824771279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2277182485135336797560309 213485857981437824771279)
                  ·
                    rfl

theorem cell22_1870930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_1870930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870930 prefixEnd_1870930 := by exact prefixLift 1870930
  have htrace : WordTrace (prefixWord ++ tailWord_1870930) baseStart_1870930 baseEnd_1870930 := by
    simpa [prefixWord, tailWord_1870930, baseEnd_1870930] using wordTrace_append hprefix tailTrace_1870930
  have hstable : (prefixWord ++ tailWord_1870930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870930).length < 2 ^ (prefixWord ++ tailWord_1870930).sum := by decide
  have hdescent : baseEnd_1870930 < baseStart_1870930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870943 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 3, 4]
def baseStart_1870943 : Nat := 118140960795 + 1870943 * 2 ^ 59
def prefixEnd_1870943 : Nat := 4983230072969 + 3 ^ 40 * 1870943 * 2
def baseEnd_1870943 : Nat := 640462024109985773738797

theorem tailTrace_1870943 : CollatzResearch.WordTrace tailWord_1870943 prefixEnd_1870943 640462024109985773738797 := by
  unfold tailWord_1870943
  simp only [CollatzResearch.WordTrace]
  refine ⟨68238897260900517470297483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45492598173933678313531655 68238897260900517470297483)
  ·
    refine ⟨102358345891350776205446225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68238897260900517470297483 102358345891350776205446225)
    ·
      refine ⟨76768759418513082154084669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102358345891350776205446225 76768759418513082154084669)
      ·
        refine ⟨28788284781942405807781751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76768759418513082154084669 28788284781942405807781751)
        ·
          refine ⟨43182427172913608711672627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28788284781942405807781751 43182427172913608711672627)
          ·
            refine ⟨64773640759370413067508941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43182427172913608711672627 64773640759370413067508941)
            ·
              refine ⟨24290115284763904900315853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64773640759370413067508941 24290115284763904900315853)
              ·
                refine ⟨9108793231786464337618445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24290115284763904900315853 9108793231786464337618445)
                ·
                  refine ⟨3415797461919924126606917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9108793231786464337618445 3415797461919924126606917)
                  ·
                    refine ⟨640462024109985773738797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3415797461919924126606917 640462024109985773738797)
                    ·
                      rfl

theorem cell22_1870943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_1870943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870943 prefixEnd_1870943 := by exact prefixLift 1870943
  have htrace : WordTrace (prefixWord ++ tailWord_1870943) baseStart_1870943 baseEnd_1870943 := by
    simpa [prefixWord, tailWord_1870943, baseEnd_1870943] using wordTrace_append hprefix tailTrace_1870943
  have hstable : (prefixWord ++ tailWord_1870943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870943).length < 2 ^ (prefixWord ++ tailWord_1870943).sum := by decide
  have hdescent : baseEnd_1870943 < baseStart_1870943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870960 : List Nat := [2, 1, 1, 1, 5, 1, 3, 3, 1, 4]
def baseStart_1870960 : Nat := 118140960795 + 1870960 * 2 ^ 59
def prefixEnd_1870960 : Nat := 4983230072969 + 3 ^ 40 * 1870960 * 2
def baseEnd_1870960 : Nat := 640467843557403396063745

theorem tailTrace_1870960 : CollatzResearch.WordTrace tailWord_1870960 prefixEnd_1870960 640467843557403396063745 := by
  unfold tailWord_1870960
  simp only [CollatzResearch.WordTrace]
  refine ⟨34119758650919464686833167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45493011534559286249110889 34119758650919464686833167)
  ·
    refine ⟨51179637976379197030249751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34119758650919464686833167 51179637976379197030249751)
    ·
      refine ⟨76769456964568795545374627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51179637976379197030249751 76769456964568795545374627)
      ·
        refine ⟨115154185446853193318061941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76769456964568795545374627 115154185446853193318061941)
        ·
          refine ⟨10795704885642486873568307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115154185446853193318061941 10795704885642486873568307)
          ·
            refine ⟨16193557328463730310352461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10795704885642486873568307 16193557328463730310352461)
            ·
              refine ⟨6072583998173898866382173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16193557328463730310352461 6072583998173898866382173)
              ·
                refine ⟨2277218999315212074893315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6072583998173898866382173 2277218999315212074893315)
                ·
                  refine ⟨3415828498972818112339973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2277218999315212074893315 3415828498972818112339973)
                  ·
                    refine ⟨640467843557403396063745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3415828498972818112339973 640467843557403396063745)
                    ·
                      rfl

theorem cell22_1870960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 1, 4].length) (baseStart_1870960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1870960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1870960 prefixEnd_1870960 := by exact prefixLift 1870960
  have htrace : WordTrace (prefixWord ++ tailWord_1870960) baseStart_1870960 baseEnd_1870960 := by
    simpa [prefixWord, tailWord_1870960, baseEnd_1870960] using wordTrace_append hprefix tailTrace_1870960
  have hstable : (prefixWord ++ tailWord_1870960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870960).length < 2 ^ (prefixWord ++ tailWord_1870960).sum := by decide
  have hdescent : baseEnd_1870960 < baseStart_1870960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871005 : List Nat := [1, 4, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_1871005 : Nat := 118140960795 + 1871005 * 2 ^ 59
def prefixEnd_1871005 : Nat := 4983230072969 + 3 ^ 40 * 1871005 * 2
def baseEnd_1871005 : Nat := 640483247977038278688607

theorem tailTrace_1871005 : CollatzResearch.WordTrace tailWord_1871005 prefixEnd_1871005 640483247977038278688607 := by
  unfold tailWord_1871005
  simp only [CollatzResearch.WordTrace]
  refine ⟨68241158586675902059054469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45494105724450601372702979 68241158586675902059054469)
  ·
    refine ⟨12795217235001731636072713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68241158586675902059054469 12795217235001731636072713)
    ·
      refine ⟨9596412926251298727054535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12795217235001731636072713 9596412926251298727054535)
      ·
        refine ⟨14394619389376948090581803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9596412926251298727054535 14394619389376948090581803)
        ·
          refine ⟨21591929084065422135872705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14394619389376948090581803 21591929084065422135872705)
          ·
            refine ⟨16193946813049066601904529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21591929084065422135872705 16193946813049066601904529)
            ·
              refine ⟨12145460109786799951428397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16193946813049066601904529 12145460109786799951428397)
              ·
                refine ⟨4554547541170049981785649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12145460109786799951428397 4554547541170049981785649)
                ·
                  refine ⟨3415910655877537486339237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4554547541170049981785649 3415910655877537486339237)
                  ·
                    refine ⟨640483247977038278688607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3415910655877537486339237 640483247977038278688607)
                    ·
                      rfl

theorem cell22_1871005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_1871005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871005 prefixEnd_1871005 := by exact prefixLift 1871005
  have htrace : WordTrace (prefixWord ++ tailWord_1871005) baseStart_1871005 baseEnd_1871005 := by
    simpa [prefixWord, tailWord_1871005, baseEnd_1871005] using wordTrace_append hprefix tailTrace_1871005
  have hstable : (prefixWord ++ tailWord_1871005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871005).length < 2 ^ (prefixWord ++ tailWord_1871005).sum := by decide
  have hdescent : baseEnd_1871005 < baseStart_1871005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871035 : List Nat := [1, 1, 1, 1, 1, 2, 4, 5, 3, 3]
def baseStart_1871035 : Nat := 118140960795 + 1871035 * 2 ^ 59
def prefixEnd_1871035 : Nat := 4983230072969 + 3 ^ 40 * 1871035 * 2
def baseEnd_1871035 : Nat := 640493517590128200438515

theorem tailTrace_1871035 : CollatzResearch.WordTrace tailWord_1871035 prefixEnd_1871035 640493517590128200438515 := by
  unfold tailWord_1871035
  simp only [CollatzResearch.WordTrace]
  refine ⟨68242252776567217182646559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45494835184378144788431039 68242252776567217182646559)
  ·
    refine ⟨102363379164850825773969839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68242252776567217182646559 102363379164850825773969839)
    ·
      refine ⟨153545068747276238660954759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102363379164850825773969839 153545068747276238660954759)
      ·
        refine ⟨230317603120914357991432139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153545068747276238660954759 230317603120914357991432139)
        ·
          refine ⟨345476404681371536987148209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230317603120914357991432139 345476404681371536987148209)
          ·
            refine ⟨259107303511028652740361157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345476404681371536987148209 259107303511028652740361157)
            ·
              refine ⟨48582619408317872388817717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259107303511028652740361157 48582619408317872388817717)
              ·
                refine ⟨4554620569529800536451661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48582619408317872388817717 4554620569529800536451661)
                ·
                  refine ⟨1707982713573675201169373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4554620569529800536451661 1707982713573675201169373)
                  ·
                    refine ⟨640493517590128200438515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1707982713573675201169373 640493517590128200438515)
                    ·
                      rfl

theorem cell22_1871035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 3].length) (baseStart_1871035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871035 prefixEnd_1871035 := by exact prefixLift 1871035
  have htrace : WordTrace (prefixWord ++ tailWord_1871035) baseStart_1871035 baseEnd_1871035 := by
    simpa [prefixWord, tailWord_1871035, baseEnd_1871035] using wordTrace_append hprefix tailTrace_1871035
  have hstable : (prefixWord ++ tailWord_1871035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871035).length < 2 ^ (prefixWord ++ tailWord_1871035).sum := by decide
  have hdescent : baseEnd_1871035 < baseStart_1871035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871041 : List Nat := [1, 2, 6, 1, 1, 1, 4, 1, 2, 3]
def baseStart_1871041 : Nat := 118140960795 + 1871041 * 2 ^ 59
def prefixEnd_1871041 : Nat := 4983230072969 + 3 ^ 40 * 1871041 * 2
def baseEnd_1871041 : Nat := 640495571512746184788497

theorem tailTrace_1871041 : CollatzResearch.WordTrace tailWord_1871041 prefixEnd_1871041 640495571512746184788497 := by
  unfold tailWord_1871041
  simp only [CollatzResearch.WordTrace]
  refine ⟨68242471614545480207364977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45494981076363653471576651 68242471614545480207364977)
  ·
    refine ⟨51181853710909110155523733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68242471614545480207364977 51181853710909110155523733)
    ·
      refine ⟨2399149392698864538540175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51181853710909110155523733 2399149392698864538540175)
      ·
        refine ⟨3598724089048296807810263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2399149392698864538540175 3598724089048296807810263)
        ·
          refine ⟨5398086133572445211715395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3598724089048296807810263 5398086133572445211715395)
          ·
            refine ⟨8097129200358667817573093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5398086133572445211715395 8097129200358667817573093)
            ·
              refine ⟨1518211725067250215794955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8097129200358667817573093 1518211725067250215794955)
              ·
                refine ⟨2277317587600875323692433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1518211725067250215794955 2277317587600875323692433)
                ·
                  refine ⟨1707988190700656492769325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2277317587600875323692433 1707988190700656492769325)
                  ·
                    refine ⟨640495571512746184788497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1707988190700656492769325 640495571512746184788497)
                    ·
                      rfl

theorem cell22_1871041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_1871041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871041 prefixEnd_1871041 := by exact prefixLift 1871041
  have htrace : WordTrace (prefixWord ++ tailWord_1871041) baseStart_1871041 baseEnd_1871041 := by
    simpa [prefixWord, tailWord_1871041, baseEnd_1871041] using wordTrace_append hprefix tailTrace_1871041
  have hstable : (prefixWord ++ tailWord_1871041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871041).length < 2 ^ (prefixWord ++ tailWord_1871041).sum := by decide
  have hdescent : baseEnd_1871041 < baseStart_1871041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871080 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 2, 5]
def baseStart_1871080 : Nat := 118140960795 + 1871080 * 2 ^ 59
def prefixEnd_1871080 : Nat := 4983230072969 + 3 ^ 40 * 1871080 * 2
def baseEnd_1871080 : Nat := 640508922009763083063377

theorem tailTrace_1871080 : CollatzResearch.WordTrace tailWord_1871080 prefixEnd_1871080 640508922009763083063377 := by
  unfold tailWord_1871080
  simp only [CollatzResearch.WordTrace]
  refine ⟨34121947030702094934017347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45495929374269459912023129 34121947030702094934017347)
  ·
    refine ⟨51182920546053142401026021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34121947030702094934017347 51182920546053142401026021)
    ·
      refine ⟨9596797602384964200192379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51182920546053142401026021 9596797602384964200192379)
      ·
        refine ⟨14395196403577446300288569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9596797602384964200192379 14395196403577446300288569)
        ·
          refine ⟨10796397302683084725216427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14395196403577446300288569 10796397302683084725216427)
          ·
            refine ⟨16194595954024627087824641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10796397302683084725216427 16194595954024627087824641)
            ·
              refine ⟨12145946965518470315868481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16194595954024627087824641 12145946965518470315868481)
              ·
                refine ⟨9109460224138852736901361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12145946965518470315868481 9109460224138852736901361)
                ·
                  refine ⟨6832095168104139552676021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9109460224138852736901361 6832095168104139552676021)
                  ·
                    refine ⟨640508922009763083063377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6832095168104139552676021 640508922009763083063377)
                    ·
                      rfl

theorem cell22_1871080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_1871080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871080 prefixEnd_1871080 := by exact prefixLift 1871080
  have htrace : WordTrace (prefixWord ++ tailWord_1871080) baseStart_1871080 baseEnd_1871080 := by
    simpa [prefixWord, tailWord_1871080, baseEnd_1871080] using wordTrace_append hprefix tailTrace_1871080
  have hstable : (prefixWord ++ tailWord_1871080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871080).length < 2 ^ (prefixWord ++ tailWord_1871080).sum := by decide
  have hdescent : baseEnd_1871080 < baseStart_1871080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871082 : List Nat := [3, 1, 3, 1, 1, 4, 2, 2, 5]
def baseStart_1871082 : Nat := 118140960795 + 1871082 * 2 ^ 59
def prefixEnd_1871082 : Nat := 4983230072969 + 3 ^ 40 * 1871082 * 2
def baseEnd_1871082 : Nat := 213503202216878581504457

theorem tailTrace_1871082 : CollatzResearch.WordTrace tailWord_1871082 prefixEnd_1871082 213503202216878581504457 := by
  unfold tailWord_1871082
  simp only [CollatzResearch.WordTrace]
  refine ⟨17060991751849236052401875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45495978004931296139738333 17060991751849236052401875)
  ·
    refine ⟨25591487627773854078602813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17060991751849236052401875 25591487627773854078602813)
    ·
      refine ⟨9596807860415195279476055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25591487627773854078602813 9596807860415195279476055)
      ·
        refine ⟨14395211790622792919214083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9596807860415195279476055 14395211790622792919214083)
        ·
          refine ⟨21592817685934189378821125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14395211790622792919214083 21592817685934189378821125)
          ·
            refine ⟨4048653316112660508528961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21592817685934189378821125 4048653316112660508528961)
            ·
              refine ⟨3036489987084495381396721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4048653316112660508528961 3036489987084495381396721)
              ·
                refine ⟨2277367490313371536047541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3036489987084495381396721 2277367490313371536047541)
                ·
                  refine ⟨213503202216878581504457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2277367490313371536047541 213503202216878581504457)
                  ·
                    rfl

theorem cell22_1871082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_1871082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871082 prefixEnd_1871082 := by exact prefixLift 1871082
  have htrace : WordTrace (prefixWord ++ tailWord_1871082) baseStart_1871082 baseEnd_1871082 := by
    simpa [prefixWord, tailWord_1871082, baseEnd_1871082] using wordTrace_append hprefix tailTrace_1871082
  have hstable : (prefixWord ++ tailWord_1871082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871082).length < 2 ^ (prefixWord ++ tailWord_1871082).sum := by decide
  have hdescent : baseEnd_1871082 < baseStart_1871082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871086 : List Nat := [4, 1, 2, 1, 1, 1, 6, 2, 1, 3]
def baseStart_1871086 : Nat := 118140960795 + 1871086 * 2 ^ 59
def prefixEnd_1871086 : Nat := 4983230072969 + 3 ^ 40 * 1871086 * 2
def baseEnd_1871086 : Nat := 640510975932381067413359

theorem tailTrace_1871086 : CollatzResearch.WordTrace tailWord_1871086 prefixEnd_1871086 640510975932381067413359 := by
  unfold tailWord_1871086
  simp only [CollatzResearch.WordTrace]
  refine ⟨8530514112422806611594139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45496075266254968595168741 8530514112422806611594139)
  ·
    refine ⟨12795771168634209917391209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8530514112422806611594139 12795771168634209917391209)
    ·
      refine ⟨9596828376475657438043407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12795771168634209917391209 9596828376475657438043407)
      ·
        refine ⟨14395242564713486157065111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9596828376475657438043407 14395242564713486157065111)
        ·
          refine ⟨21592863847070229235597667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14395242564713486157065111 21592863847070229235597667)
          ·
            refine ⟨32389295770605343853396501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21592863847070229235597667 32389295770605343853396501)
            ·
              refine ⟨1518248239247125493127961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32389295770605343853396501 1518248239247125493127961)
              ·
                refine ⟨1138686179435344119845971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1518248239247125493127961 1138686179435344119845971)
                ·
                  refine ⟨1708029269153016179768957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1138686179435344119845971 1708029269153016179768957)
                  ·
                    refine ⟨640510975932381067413359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1708029269153016179768957 640510975932381067413359)
                    ·
                      rfl

theorem cell22_1871086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_1871086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871086 prefixEnd_1871086 := by exact prefixLift 1871086
  have htrace : WordTrace (prefixWord ++ tailWord_1871086) baseStart_1871086 baseEnd_1871086 := by
    simpa [prefixWord, tailWord_1871086, baseEnd_1871086] using wordTrace_append hprefix tailTrace_1871086
  have hstable : (prefixWord ++ tailWord_1871086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871086).length < 2 ^ (prefixWord ++ tailWord_1871086).sum := by decide
  have hdescent : baseEnd_1871086 < baseStart_1871086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871144 : List Nat := [2, 1, 5, 1, 2, 1, 2, 4, 4]
def baseStart_1871144 : Nat := 118140960795 + 1871144 * 2 ^ 59
def prefixEnd_1871144 : Nat := 4983230072969 + 3 ^ 40 * 1871144 * 2
def baseEnd_1871144 : Nat := 213510276839229416487727

theorem tailTrace_1871144 : CollatzResearch.WordTrace tailWord_1871144 prefixEnd_1871144 213510276839229416487727 := by
  unfold tailWord_1871144
  simp only [CollatzResearch.WordTrace]
  refine ⟨34123114166586164399182243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45497485555448219198909657 34123114166586164399182243)
  ·
    refine ⟨51184671249879246598773365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34123114166586164399182243 51184671249879246598773365)
    ·
      refine ⟨4798562929676179368635003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51184671249879246598773365 4798562929676179368635003)
      ·
        refine ⟨7197844394514269052952505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4798562929676179368635003 7197844394514269052952505)
        ·
          refine ⟨5398383295885701789714379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7197844394514269052952505 5398383295885701789714379)
          ·
            refine ⟨8097574943828552684571569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5398383295885701789714379 8097574943828552684571569)
            ·
              refine ⟨6073181207871414513428677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8097574943828552684571569 6073181207871414513428677)
              ·
                refine ⟨1138721476475890221267877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6073181207871414513428677 1138721476475890221267877)
                ·
                  refine ⟨213510276839229416487727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1138721476475890221267877 213510276839229416487727)
                  ·
                    rfl

theorem cell22_1871144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 4].length) (baseStart_1871144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871144 prefixEnd_1871144 := by exact prefixLift 1871144
  have htrace : WordTrace (prefixWord ++ tailWord_1871144) baseStart_1871144 baseEnd_1871144 := by
    simpa [prefixWord, tailWord_1871144, baseEnd_1871144] using wordTrace_append hprefix tailTrace_1871144
  have hstable : (prefixWord ++ tailWord_1871144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871144).length < 2 ^ (prefixWord ++ tailWord_1871144).sum := by decide
  have hdescent : baseEnd_1871144 < baseStart_1871144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871202 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1871202 : Nat := 118140960795 + 1871202 * 2 ^ 59
def prefixEnd_1871202 : Nat := 4983230072969 + 3 ^ 40 * 1871202 * 2
def baseEnd_1871202 : Nat := 640550685102995431513003

theorem tailTrace_1871202 : CollatzResearch.WordTrace tailWord_1871202 prefixEnd_1871202 640550685102995431513003 := by
  unfold tailWord_1871202
  simp only [CollatzResearch.WordTrace]
  refine ⟨17062085941740551175993965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45498895844641469802650573 17062085941740551175993965)
  ·
    refine ⟨6398282228152706690997737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17062085941740551175993965 6398282228152706690997737)
    ·
      refine ⟨4798711671114530018248303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6398282228152706690997737 4798711671114530018248303)
      ·
        refine ⟨7198067506671795027372455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4798711671114530018248303 7198067506671795027372455)
        ·
          refine ⟨10797101260007692541058683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7198067506671795027372455 10797101260007692541058683)
          ·
            refine ⟨16195651890011538811588025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10797101260007692541058683 16195651890011538811588025)
            ·
              refine ⟨12146738917508654108691019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16195651890011538811588025 12146738917508654108691019)
              ·
                refine ⟨18220108376262981163036529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12146738917508654108691019 18220108376262981163036529)
                ·
                  refine ⟨13665081282197235872277397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18220108376262981163036529 13665081282197235872277397)
                  ·
                    refine ⟨640550685102995431513003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13665081282197235872277397 640550685102995431513003)
                    ·
                      rfl

theorem cell22_1871202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1871202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871202 prefixEnd_1871202 := by exact prefixLift 1871202
  have htrace : WordTrace (prefixWord ++ tailWord_1871202) baseStart_1871202 baseEnd_1871202 := by
    simpa [prefixWord, tailWord_1871202, baseEnd_1871202] using wordTrace_append hprefix tailTrace_1871202
  have hstable : (prefixWord ++ tailWord_1871202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871202).length < 2 ^ (prefixWord ++ tailWord_1871202).sum := by decide
  have hdescent : baseEnd_1871202 < baseStart_1871202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871204 : List Nat := [2, 3, 1, 1, 3, 2, 3, 1, 3, 3]
def baseStart_1871204 : Nat := 118140960795 + 1871204 * 2 ^ 59
def prefixEnd_1871204 : Nat := 4983230072969 + 3 ^ 40 * 1871204 * 2
def baseEnd_1871204 : Nat := 640551369743868092962997

theorem tailTrace_1871204 : CollatzResearch.WordTrace tailWord_1871204 prefixEnd_1871204 640551369743868092962997 := by
  unfold tailWord_1871204
  simp only [CollatzResearch.WordTrace]
  refine ⟨34124208356477479522774333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45498944475303306030365777 34124208356477479522774333)
  ·
    refine ⟨12796578133679054821040375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34124208356477479522774333 12796578133679054821040375)
    ·
      refine ⟨19194867200518582231560563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12796578133679054821040375 19194867200518582231560563)
      ·
        refine ⟨28792300800777873347340845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19194867200518582231560563 28792300800777873347340845)
        ·
          refine ⟨10797112800291702505252817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28792300800777873347340845 10797112800291702505252817)
          ·
            refine ⟨8097834600218776878939613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10797112800291702505252817 8097834600218776878939613)
            ·
              refine ⟨3036687975082041329602355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8097834600218776878939613 3036687975082041329602355)
              ·
                refine ⟨4555031962623061994403533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3036687975082041329602355 4555031962623061994403533)
                ·
                  refine ⟨1708136985983648247901325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4555031962623061994403533 1708136985983648247901325)
                  ·
                    refine ⟨640551369743868092962997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1708136985983648247901325 640551369743868092962997)
                    ·
                      rfl

theorem cell22_1871204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_1871204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871204 prefixEnd_1871204 := by exact prefixLift 1871204
  have htrace : WordTrace (prefixWord ++ tailWord_1871204) baseStart_1871204 baseEnd_1871204 := by
    simpa [prefixWord, tailWord_1871204, baseEnd_1871204] using wordTrace_append hprefix tailTrace_1871204
  have hstable : (prefixWord ++ tailWord_1871204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871204).length < 2 ^ (prefixWord ++ tailWord_1871204).sum := by decide
  have hdescent : baseEnd_1871204 < baseStart_1871204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871210 : List Nat := [3, 1, 3, 3, 3, 1, 2, 1, 2, 3]
def baseStart_1871210 : Nat := 118140960795 + 1871210 * 2 ^ 59
def prefixEnd_1871210 : Nat := 4983230072969 + 3 ^ 40 * 1871210 * 2
def baseEnd_1871210 : Nat := 640553423666486077312979

theorem tailTrace_1871210 : CollatzResearch.WordTrace tailWord_1871210 prefixEnd_1871210 640553423666486077312979 := by
  unfold tailWord_1871210
  simp only [CollatzResearch.WordTrace]
  refine ⟨17062158887733305517566771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45499090367288814713511389 17062158887733305517566771)
  ·
    refine ⟨25593238331599958276350157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17062158887733305517566771 25593238331599958276350157)
    ·
      refine ⟨9597464374349984353631309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25593238331599958276350157 9597464374349984353631309)
      ·
        refine ⟨3599049140381244132611741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9597464374349984353631309 3599049140381244132611741)
        ·
          refine ⟨1349643427642966549729403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3599049140381244132611741 1349643427642966549729403)
          ·
            refine ⟨2024465141464449824594105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349643427642966549729403 2024465141464449824594105)
            ·
              refine ⟨1518348856098337368445579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2024465141464449824594105 1518348856098337368445579)
              ·
                refine ⟨2277523284147506052668369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1518348856098337368445579 2277523284147506052668369)
                ·
                  refine ⟨1708142463110629539501277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2277523284147506052668369 1708142463110629539501277)
                  ·
                    refine ⟨640553423666486077312979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1708142463110629539501277 640553423666486077312979)
                    ·
                      rfl

theorem cell22_1871210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_1871210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871210 prefixEnd_1871210 := by exact prefixLift 1871210
  have htrace : WordTrace (prefixWord ++ tailWord_1871210) baseStart_1871210 baseEnd_1871210 := by
    simpa [prefixWord, tailWord_1871210, baseEnd_1871210] using wordTrace_append hprefix tailTrace_1871210
  have hstable : (prefixWord ++ tailWord_1871210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871210).length < 2 ^ (prefixWord ++ tailWord_1871210).sum := by decide
  have hdescent : baseEnd_1871210 < baseStart_1871210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871215 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 1, 7]
def baseStart_1871215 : Nat := 118140960795 + 1871215 * 2 ^ 59
def prefixEnd_1871215 : Nat := 4983230072969 + 3 ^ 40 * 1871215 * 2
def baseEnd_1871215 : Nat := 640555135268667730937963

theorem tailTrace_1871215 : CollatzResearch.WordTrace tailWord_1871215 prefixEnd_1871215 640555135268667730937963 := by
  unfold tailWord_1871215
  simp only [CollatzResearch.WordTrace]
  refine ⟨68248817915915107924199099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45499211943943405282799399 68248817915915107924199099)
  ·
    refine ⟨102373226873872661886298649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68248817915915107924199099 102373226873872661886298649)
    ·
      refine ⟨76779920155404496414723987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102373226873872661886298649 76779920155404496414723987)
      ·
        refine ⟨115169880233106744622085981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76779920155404496414723987 115169880233106744622085981)
        ·
          refine ⟨43188705087415029233282243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115169880233106744622085981 43188705087415029233282243)
          ·
            refine ⟨64783057631122543849923365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43188705087415029233282243 64783057631122543849923365)
            ·
              refine ⟨12146823305835476971860631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64783057631122543849923365 12146823305835476971860631)
              ·
                refine ⟨18220234958753215457790947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12146823305835476971860631 18220234958753215457790947)
                ·
                  refine ⟨27330352438129823186686421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18220234958753215457790947 27330352438129823186686421)
                  ·
                    refine ⟨640555135268667730937963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27330352438129823186686421 640555135268667730937963)
                    ·
                      rfl

theorem cell22_1871215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_1871215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871215 prefixEnd_1871215 := by exact prefixLift 1871215
  have htrace : WordTrace (prefixWord ++ tailWord_1871215) baseStart_1871215 baseEnd_1871215 := by
    simpa [prefixWord, tailWord_1871215, baseEnd_1871215] using wordTrace_append hprefix tailTrace_1871215
  have hstable : (prefixWord ++ tailWord_1871215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871215).length < 2 ^ (prefixWord ++ tailWord_1871215).sum := by decide
  have hdescent : baseEnd_1871215 < baseStart_1871215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871275 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 2, 10]
def baseStart_1871275 : Nat := 118140960795 + 1871275 * 2 ^ 59
def prefixEnd_1871275 : Nat := 4983230072969 + 3 ^ 40 * 1871275 * 2
def baseEnd_1871275 : Nat := 640575674494847574437779

theorem tailTrace_1871275 : CollatzResearch.WordTrace tailWord_1871275 prefixEnd_1871275 640575674494847574437779 := by
  unfold tailWord_1871275
  simp only [CollatzResearch.WordTrace]
  refine ⟨68251006295697738171383279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45500670863798492114255519 68251006295697738171383279)
  ·
    refine ⟨102376509443546607257074919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68251006295697738171383279 102376509443546607257074919)
    ·
      refine ⟨153564764165319910885612379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102376509443546607257074919 153564764165319910885612379)
      ·
        refine ⟨230347146247979866328418569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153564764165319910885612379 230347146247979866328418569)
        ·
          refine ⟨172760359685984899746313927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230347146247979866328418569 172760359685984899746313927)
          ·
            refine ⟨259140539528977349619470891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172760359685984899746313927 259140539528977349619470891)
            ·
              refine ⟨388710809293466024429206337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259140539528977349619470891 388710809293466024429206337)
              ·
                refine ⟨291533106970099518321904753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388710809293466024429206337 291533106970099518321904753)
                ·
                  refine ⟨218649830227574638741428565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291533106970099518321904753 218649830227574638741428565)
                  ·
                    refine ⟨640575674494847574437779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 218649830227574638741428565 640575674494847574437779)
                    ·
                      rfl

theorem cell22_1871275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 10].length) (baseStart_1871275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871275 prefixEnd_1871275 := by exact prefixLift 1871275
  have htrace : WordTrace (prefixWord ++ tailWord_1871275) baseStart_1871275 baseEnd_1871275 := by
    simpa [prefixWord, tailWord_1871275, baseEnd_1871275] using wordTrace_append hprefix tailTrace_1871275
  have hstable : (prefixWord ++ tailWord_1871275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871275).length < 2 ^ (prefixWord ++ tailWord_1871275).sum := by decide
  have hdescent : baseEnd_1871275 < baseStart_1871275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871294 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_1871294 : Nat := 118140960795 + 1871294 * 2 ^ 59
def prefixEnd_1871294 : Nat := 4983230072969 + 3 ^ 40 * 1871294 * 2
def baseEnd_1871294 : Nat := 640582178583137858212721

theorem tailTrace_1871294 : CollatzResearch.WordTrace tailWord_1871294 prefixEnd_1871294 640582178583137858212721 := by
  unfold tailWord_1871294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8531462410328613052040617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45501132855085936277549957 8531462410328613052040617)
  ·
    refine ⟨6398596807746459789030463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8531462410328613052040617 6398596807746459789030463)
    ·
      refine ⟨9597895211619689683545695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6398596807746459789030463 9597895211619689683545695)
      ·
        refine ⟨14396842817429534525318543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9597895211619689683545695 14396842817429534525318543)
        ·
          refine ⟨21595264226144301787977815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14396842817429534525318543 21595264226144301787977815)
          ·
            refine ⟨32392896339216452681966723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21595264226144301787977815 32392896339216452681966723)
            ·
              refine ⟨48589344508824679022950085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32392896339216452681966723 48589344508824679022950085)
              ·
                refine ⟨9110502095404627316803141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48589344508824679022950085 9110502095404627316803141)
                ·
                  refine ⟨1708219142888367621900589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9110502095404627316803141 1708219142888367621900589)
                  ·
                    refine ⟨640582178583137858212721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1708219142888367621900589 640582178583137858212721)
                    ·
                      rfl

theorem cell22_1871294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_1871294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871294 prefixEnd_1871294 := by exact prefixLift 1871294
  have htrace : WordTrace (prefixWord ++ tailWord_1871294) baseStart_1871294 baseEnd_1871294 := by
    simpa [prefixWord, tailWord_1871294, baseEnd_1871294] using wordTrace_append hprefix tailTrace_1871294
  have hstable : (prefixWord ++ tailWord_1871294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871294).length < 2 ^ (prefixWord ++ tailWord_1871294).sum := by decide
  have hdescent : baseEnd_1871294 < baseStart_1871294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871352 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 7]
def baseStart_1871352 : Nat := 118140960795 + 1871352 * 2 ^ 59
def prefixEnd_1871352 : Nat := 4983230072969 + 3 ^ 40 * 1871352 * 2
def baseEnd_1871352 : Nat := 213534011056148346754181

theorem tailTrace_1871352 : CollatzResearch.WordTrace tailWord_1871352 prefixEnd_1871352 213534011056148346754181 := by
  unfold tailWord_1871352
  simp only [CollatzResearch.WordTrace]
  refine ⟨34126907358209390160968155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45502543144279186881290873 34126907358209390160968155)
  ·
    refine ⟨51190361037314085241452233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34126907358209390160968155 51190361037314085241452233)
    ·
      refine ⟨38392770777985563931089175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51190361037314085241452233 38392770777985563931089175)
      ·
        refine ⟨57589156166978345896633763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38392770777985563931089175 57589156166978345896633763)
        ·
          refine ⟨86383734250467518844950645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57589156166978345896633763 86383734250467518844950645)
          ·
            refine ⟨8098475085981329891714123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86383734250467518844950645 8098475085981329891714123)
            ·
              refine ⟨12147712628971994837571185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8098475085981329891714123 12147712628971994837571185)
              ·
                refine ⟨9110784471728996128178389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12147712628971994837571185 9110784471728996128178389)
                ·
                  refine ⟨213534011056148346754181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9110784471728996128178389 213534011056148346754181)
                  ·
                    rfl

theorem cell22_1871352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 7].length) (baseStart_1871352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871352 prefixEnd_1871352 := by exact prefixLift 1871352
  have htrace : WordTrace (prefixWord ++ tailWord_1871352) baseStart_1871352 baseEnd_1871352 := by
    simpa [prefixWord, tailWord_1871352, baseEnd_1871352] using wordTrace_append hprefix tailTrace_1871352
  have hstable : (prefixWord ++ tailWord_1871352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871352).length < 2 ^ (prefixWord ++ tailWord_1871352).sum := by decide
  have hdescent : baseEnd_1871352 < baseStart_1871352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871358 : List Nat := [4, 2, 2, 3, 2, 1, 8]
def baseStart_1871358 : Nat := 118140960795 + 1871358 * 2 ^ 59
def prefixEnd_1871358 : Nat := 4983230072969 + 3 ^ 40 * 1871358 * 2
def baseEnd_1871358 : Nat := 23726077299669000911575

theorem tailTrace_1871358 : CollatzResearch.WordTrace tailWord_1871358 prefixEnd_1871358 23726077299669000911575 := by
  unfold tailWord_1871358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8531754194299630418331841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45502689036264695564436485 8531754194299630418331841)
  ·
    refine ⟨6398815645724722813748881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8531754194299630418331841 6398815645724722813748881)
    ·
      refine ⟨4799111734293542110311661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6398815645724722813748881 4799111734293542110311661)
      ·
        refine ⟨1799666900360078291366873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4799111734293542110311661 1799666900360078291366873)
        ·
          refine ⟨1349750175270058718525155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1799666900360078291366873 1349750175270058718525155)
          ·
            refine ⟨2024625262905088077787733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349750175270058718525155 2024625262905088077787733)
            ·
              refine ⟨23726077299669000911575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2024625262905088077787733 23726077299669000911575)
              ·
                rfl

theorem cell22_1871358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 8].length) (baseStart_1871358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871358 prefixEnd_1871358 := by exact prefixLift 1871358
  have htrace : WordTrace (prefixWord ++ tailWord_1871358) baseStart_1871358 baseEnd_1871358 := by
    simpa [prefixWord, tailWord_1871358, baseEnd_1871358] using wordTrace_append hprefix tailTrace_1871358
  have hstable : (prefixWord ++ tailWord_1871358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871358).length < 2 ^ (prefixWord ++ tailWord_1871358).sum := by decide
  have hdescent : baseEnd_1871358 < baseStart_1871358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871397 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 8]
def baseStart_1871397 : Nat := 118140960795 + 1871397 * 2 ^ 59
def prefixEnd_1871397 : Nat := 4983230072969 + 3 ^ 40 * 1871397 * 2
def baseEnd_1871397 : Nat := 213539145862693307629135

theorem tailTrace_1871397 : CollatzResearch.WordTrace tailWord_1871397 prefixEnd_1871397 213539145862693307629135 := by
  unfold tailWord_1871397
  simp only [CollatzResearch.WordTrace]
  refine ⟨68255456001255753007324445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45503637334170502004882963 68255456001255753007324445)
  ·
    refine ⟨25595796000470907377746667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68255456001255753007324445 25595796000470907377746667)
    ·
      refine ⟨38393694000706361066620001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25595796000470907377746667 38393694000706361066620001)
      ·
        refine ⟨28795270500529770799965001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38393694000706361066620001 28795270500529770799965001)
        ·
          refine ⟨21596452875397328099973751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28795270500529770799965001 21596452875397328099973751)
          ·
            refine ⟨32394679313095992149960627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21596452875397328099973751 32394679313095992149960627)
            ·
              refine ⟨48592018969643988224940941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32394679313095992149960627 48592018969643988224940941)
              ·
                refine ⟨18222007113616495584352853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48592018969643988224940941 18222007113616495584352853)
                ·
                  refine ⟨213539145862693307629135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18222007113616495584352853 213539145862693307629135)
                  ·
                    rfl

theorem cell22_1871397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_1871397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871397 prefixEnd_1871397 := by exact prefixLift 1871397
  have htrace : WordTrace (prefixWord ++ tailWord_1871397) baseStart_1871397 baseEnd_1871397 := by
    simpa [prefixWord, tailWord_1871397, baseEnd_1871397] using wordTrace_append hprefix tailTrace_1871397
  have hstable : (prefixWord ++ tailWord_1871397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871397).length < 2 ^ (prefixWord ++ tailWord_1871397).sum := by decide
  have hdescent : baseEnd_1871397 < baseStart_1871397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871427 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 5, 6]
def baseStart_1871427 : Nat := 118140960795 + 1871427 * 2 ^ 59
def prefixEnd_1871427 : Nat := 4983230072969 + 3 ^ 40 * 1871427 * 2
def baseEnd_1871427 : Nat := 640627707201169844637313

theorem tailTrace_1871427 : CollatzResearch.WordTrace tailWord_1871427 prefixEnd_1871427 640627707201169844637313 := by
  unfold tailWord_1871427
  simp only [CollatzResearch.WordTrace]
  refine ⟨68256550191147068130916535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45504366794098045420611023 68256550191147068130916535)
  ·
    refine ⟨102384825286720602196374803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68256550191147068130916535 102384825286720602196374803)
    ·
      refine ⟨153577237930080903294562205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102384825286720602196374803 153577237930080903294562205)
      ·
        refine ⟨57591464223780338735460827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153577237930080903294562205 57591464223780338735460827)
        ·
          refine ⟨86387196335670508103191241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57591464223780338735460827 86387196335670508103191241)
          ·
            refine ⟨64790397251752881077393431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86387196335670508103191241 64790397251752881077393431)
            ·
              refine ⟨97185595877629321616090147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64790397251752881077393431 97185595877629321616090147)
              ·
                refine ⟨145778393816443982424135221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97185595877629321616090147 145778393816443982424135221)
                ·
                  refine ⟨13666724420291623352262677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145778393816443982424135221 13666724420291623352262677)
                  ·
                    refine ⟨640627707201169844637313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13666724420291623352262677 640627707201169844637313)
                    ·
                      rfl

theorem cell22_1871427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 6].length) (baseStart_1871427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871427 prefixEnd_1871427 := by exact prefixLift 1871427
  have htrace : WordTrace (prefixWord ++ tailWord_1871427) baseStart_1871427 baseEnd_1871427 := by
    simpa [prefixWord, tailWord_1871427, baseEnd_1871427] using wordTrace_append hprefix tailTrace_1871427
  have hstable : (prefixWord ++ tailWord_1871427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871427).length < 2 ^ (prefixWord ++ tailWord_1871427).sum := by decide
  have hdescent : baseEnd_1871427 < baseStart_1871427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871444 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_1871444 : Nat := 118140960795 + 1871444 * 2 ^ 59
def prefixEnd_1871444 : Nat := 4983230072969 + 3 ^ 40 * 1871444 * 2
def baseEnd_1871444 : Nat := 640633526648587466962261

theorem tailTrace_1871444 : CollatzResearch.WordTrace tailWord_1871444 prefixEnd_1871444 640633526648587466962261 := by
  unfold tailWord_1871444
  simp only [CollatzResearch.WordTrace]
  refine ⟨34128585116042740017142693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45504780154723653356190257 34128585116042740017142693)
  ·
    refine ⟨6399109709258013753214255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34128585116042740017142693 6399109709258013753214255)
    ·
      refine ⟨9598664563887020629821383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6399109709258013753214255 9598664563887020629821383)
      ·
        refine ⟨14397996845830530944732075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9598664563887020629821383 14397996845830530944732075)
        ·
          refine ⟨21596995268745796417098113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14397996845830530944732075 21596995268745796417098113)
          ·
            refine ⟨16197746451559347312823585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21596995268745796417098113 16197746451559347312823585)
            ·
              refine ⟨12148309838669510484617689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16197746451559347312823585 12148309838669510484617689)
              ·
                refine ⟨9111232379002132863463267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12148309838669510484617689 9111232379002132863463267)
                ·
                  refine ⟨13666848568503199295194901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9111232379002132863463267 13666848568503199295194901)
                  ·
                    refine ⟨640633526648587466962261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13666848568503199295194901 640633526648587466962261)
                    ·
                      rfl

theorem cell22_1871444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_1871444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871444 prefixEnd_1871444 := by exact prefixLift 1871444
  have htrace : WordTrace (prefixWord ++ tailWord_1871444) baseStart_1871444 baseEnd_1871444 := by
    simpa [prefixWord, tailWord_1871444, baseEnd_1871444] using wordTrace_append hprefix tailTrace_1871444
  have hstable : (prefixWord ++ tailWord_1871444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871444).length < 2 ^ (prefixWord ++ tailWord_1871444).sum := by decide
  have hdescent : baseEnd_1871444 < baseStart_1871444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871461 : List Nat := [1, 3, 1, 3, 3, 1, 3, 1, 2, 4]
def baseStart_1871461 : Nat := 118140960795 + 1871461 * 2 ^ 59
def prefixEnd_1871461 : Nat := 4983230072969 + 3 ^ 40 * 1871461 * 2
def baseEnd_1871461 : Nat := 640639346096005089287209

theorem tailTrace_1871461 : CollatzResearch.WordTrace tailWord_1871461 prefixEnd_1871461 640639346096005089287209 := by
  unfold tailWord_1871461
  simp only [CollatzResearch.WordTrace]
  refine ⟨68257790273023891937654237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45505193515349261291769491 68257790273023891937654237)
  ·
    refine ⟨25596671352383959476620339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68257790273023891937654237 25596671352383959476620339)
    ·
      refine ⟨38395007028575939214930509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25596671352383959476620339 38395007028575939214930509)
      ·
        refine ⟨14398127635715977205598941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38395007028575939214930509 14398127635715977205598941)
        ·
          refine ⟨5399297863393491452099603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14398127635715977205598941 5399297863393491452099603)
          ·
            refine ⟨8098946795090237178149405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5399297863393491452099603 8098946795090237178149405)
            ·
              refine ⟨3037105048158838941806027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8098946795090237178149405 3037105048158838941806027)
              ·
                refine ⟨4555657572238258412709041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037105048158838941806027 4555657572238258412709041)
                ·
                  refine ⟨3416743179178693809531781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4555657572238258412709041 3416743179178693809531781)
                  ·
                    refine ⟨640639346096005089287209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3416743179178693809531781 640639346096005089287209)
                    ·
                      rfl

theorem cell22_1871461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_1871461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871461 prefixEnd_1871461 := by exact prefixLift 1871461
  have htrace : WordTrace (prefixWord ++ tailWord_1871461) baseStart_1871461 baseEnd_1871461 := by
    simpa [prefixWord, tailWord_1871461, baseEnd_1871461] using wordTrace_append hprefix tailTrace_1871461
  have hstable : (prefixWord ++ tailWord_1871461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871461).length < 2 ^ (prefixWord ++ tailWord_1871461).sum := by decide
  have hdescent : baseEnd_1871461 < baseStart_1871461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871504 : List Nat := [2, 1, 1, 1, 1, 1, 3, 7, 5]
def baseStart_1871504 : Nat := 118140960795 + 1871504 * 2 ^ 59
def prefixEnd_1871504 : Nat := 4983230072969 + 3 ^ 40 * 1871504 * 2
def baseEnd_1871504 : Nat := 213551355291589103487359

theorem tailTrace_1871504 : CollatzResearch.WordTrace tailWord_1871504 prefixEnd_1871504 213551355291589103487359 := by
  unfold tailWord_1871504
  simp only [CollatzResearch.WordTrace]
  refine ⟨34129679305934055140734783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45506239074578740187646377 34129679305934055140734783)
  ·
    refine ⟨51194518958901082711102175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34129679305934055140734783 51194518958901082711102175)
    ·
      refine ⟨76791778438351624066653263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51194518958901082711102175 76791778438351624066653263)
      ·
        refine ⟨115187667657527436099979895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76791778438351624066653263 115187667657527436099979895)
        ·
          refine ⟨172781501486291154149969843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115187667657527436099979895 172781501486291154149969843)
          ·
            refine ⟨259172252229436731224954765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172781501486291154149969843 259172252229436731224954765)
            ·
              refine ⟨97189594586038774209358037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259172252229436731224954765 97189594586038774209358037)
              ·
                refine ⟨2277881123110283770531829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 97189594586038774209358037 2277881123110283770531829)
                ·
                  refine ⟨213551355291589103487359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2277881123110283770531829 213551355291589103487359)
                  ·
                    rfl

theorem cell22_1871504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 5].length) (baseStart_1871504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871504 prefixEnd_1871504 := by exact prefixLift 1871504
  have htrace : WordTrace (prefixWord ++ tailWord_1871504) baseStart_1871504 baseEnd_1871504 := by
    simpa [prefixWord, tailWord_1871504, baseEnd_1871504] using wordTrace_append hprefix tailTrace_1871504
  have hstable : (prefixWord ++ tailWord_1871504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871504).length < 2 ^ (prefixWord ++ tailWord_1871504).sum := by decide
  have hdescent : baseEnd_1871504 < baseStart_1871504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871542 : List Nat := [5, 1, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_1871542 : Nat := 118140960795 + 1871542 * 2 ^ 59
def prefixEnd_1871542 : Nat := 4983230072969 + 3 ^ 40 * 1871542 * 2
def baseEnd_1871542 : Nat := 640667074051347878011961

theorem tailTrace_1871542 : CollatzResearch.WordTrace tailWord_1871542 prefixEnd_1871542 640667074051347878011961 := by
  unfold tailWord_1871542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4266296536608152673209555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45507163057153628514235253 4266296536608152673209555)
  ·
    refine ⟨6399444804912229009814333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4266296536608152673209555 6399444804912229009814333)
    ·
      refine ⟨2399791801842085878680375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6399444804912229009814333 2399791801842085878680375)
      ·
        refine ⟨3599687702763128818020563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2399791801842085878680375 3599687702763128818020563)
        ·
          refine ⟨5399531554144693227030845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3599687702763128818020563 5399531554144693227030845)
          ·
            refine ⟨2024824332804259960136567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5399531554144693227030845 2024824332804259960136567)
            ·
              refine ⟨3037236499206389940204851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2024824332804259960136567 3037236499206389940204851)
              ·
                refine ⟨4555854748809584910307277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037236499206389940204851 4555854748809584910307277)
                ·
                  refine ⟨1708445530803594341365229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4555854748809584910307277 1708445530803594341365229)
                  ·
                    refine ⟨640667074051347878011961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1708445530803594341365229 640667074051347878011961)
                    ·
                      rfl

theorem cell22_1871542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_1871542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871542 prefixEnd_1871542 := by exact prefixLift 1871542
  have htrace : WordTrace (prefixWord ++ tailWord_1871542) baseStart_1871542 baseEnd_1871542 := by
    simpa [prefixWord, tailWord_1871542, baseEnd_1871542] using wordTrace_append hprefix tailTrace_1871542
  have hstable : (prefixWord ++ tailWord_1871542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871542).length < 2 ^ (prefixWord ++ tailWord_1871542).sum := by decide
  have hdescent : baseEnd_1871542 < baseStart_1871542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871585 : List Nat := [1, 2, 3, 1, 5, 1, 3, 1, 1, 4]
def baseStart_1871585 : Nat := 118140960795 + 1871585 * 2 ^ 59
def prefixEnd_1871585 : Nat := 4983230072969 + 3 ^ 40 * 1871585 * 2
def baseEnd_1871585 : Nat := 640681793830110099186829

theorem tailTrace_1871585 : CollatzResearch.WordTrace tailWord_1871585 prefixEnd_1871585 640681793830110099186829 := by
  unfold tailWord_1871585
  simp only [CollatzResearch.WordTrace]
  refine ⟨68262312924574661115168209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45508208616383107410112139 68262312924574661115168209)
  ·
    refine ⟨51196734693430995836376157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68262312924574661115168209 51196734693430995836376157)
    ·
      refine ⟨19198775510036623438641059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51196734693430995836376157 19198775510036623438641059)
      ·
        refine ⟨28798163265054935157961589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19198775510036623438641059 28798163265054935157961589)
        ·
          refine ⟨2699827806098900171058899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28798163265054935157961589 2699827806098900171058899)
          ·
            refine ⟨4049741709148350256588349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2699827806098900171058899 4049741709148350256588349)
            ·
              refine ⟨1518653140930631346220631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4049741709148350256588349 1518653140930631346220631)
              ·
                refine ⟨2277979711395947019330947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1518653140930631346220631 2277979711395947019330947)
                ·
                  refine ⟨3416969567093920528996421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2277979711395947019330947 3416969567093920528996421)
                  ·
                    refine ⟨640681793830110099186829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3416969567093920528996421 640681793830110099186829)
                    ·
                      rfl

theorem cell22_1871585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_1871585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871585 prefixEnd_1871585 := by exact prefixLift 1871585
  have htrace : WordTrace (prefixWord ++ tailWord_1871585) baseStart_1871585 baseEnd_1871585 := by
    simpa [prefixWord, tailWord_1871585, baseEnd_1871585] using wordTrace_append hprefix tailTrace_1871585
  have hstable : (prefixWord ++ tailWord_1871585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871585).length < 2 ^ (prefixWord ++ tailWord_1871585).sum := by decide
  have hdescent : baseEnd_1871585 < baseStart_1871585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871596 : List Nat := [2, 2, 1, 1, 2, 2, 4, 2, 2, 4]
def baseStart_1871596 : Nat := 118140960795 + 1871596 * 2 ^ 59
def prefixEnd_1871596 : Nat := 4983230072969 + 3 ^ 40 * 1871596 * 2
def baseEnd_1871596 : Nat := 640685559354909737161795

theorem tailTrace_1871596 : CollatzResearch.WordTrace tailWord_1871596 prefixEnd_1871596 640685559354909737161795 := by
  unfold tailWord_1871596
  simp only [CollatzResearch.WordTrace]
  refine ⟨34131357063767404996909321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45508476085023206662545761 34131357063767404996909321)
  ·
    refine ⟨25598517797825553747681991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34131357063767404996909321 25598517797825553747681991)
    ·
      refine ⟨38397776696738330621522987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25598517797825553747681991 38397776696738330621522987)
      ·
        refine ⟨57596665045107495932284481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38397776696738330621522987 57596665045107495932284481)
        ·
          refine ⟨43197498783830621949213361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57596665045107495932284481 43197498783830621949213361)
          ·
            refine ⟨32398124087872966461910021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43197498783830621949213361 32398124087872966461910021)
            ·
              refine ⟨6074648266476181211608129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32398124087872966461910021 6074648266476181211608129)
              ·
                refine ⟨4555986199857135908706097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6074648266476181211608129 4555986199857135908706097)
                ·
                  refine ⟨3416989649892851931529573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4555986199857135908706097 3416989649892851931529573)
                  ·
                    refine ⟨640685559354909737161795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3416989649892851931529573 640685559354909737161795)
                    ·
                      rfl

theorem cell22_1871596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_1871596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871596 prefixEnd_1871596 := by exact prefixLift 1871596
  have htrace : WordTrace (prefixWord ++ tailWord_1871596) baseStart_1871596 baseEnd_1871596 := by
    simpa [prefixWord, tailWord_1871596, baseEnd_1871596] using wordTrace_append hprefix tailTrace_1871596
  have hstable : (prefixWord ++ tailWord_1871596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871596).length < 2 ^ (prefixWord ++ tailWord_1871596).sum := by decide
  have hdescent : baseEnd_1871596 < baseStart_1871596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871609 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 4, 7]
def baseStart_1871609 : Nat := 118140960795 + 1871609 * 2 ^ 59
def prefixEnd_1871609 : Nat := 4983230072969 + 3 ^ 40 * 1871609 * 2
def baseEnd_1871609 : Nat := 640690009520582036586755

theorem tailTrace_1871609 : CollatzResearch.WordTrace tailWord_1871609 prefixEnd_1871609 640690009520582036586755 := by
  unfold tailWord_1871609
  simp only [CollatzResearch.WordTrace]
  refine ⟨68263188276487713214041881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45508792184325142142694587 68263188276487713214041881)
  ·
    refine ⟨51197391207365784910531411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68263188276487713214041881 51197391207365784910531411)
    ·
      refine ⟨76796086811048677365797117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51197391207365784910531411 76796086811048677365797117)
      ·
        refine ⟨28798532554143254012173919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76796086811048677365797117 28798532554143254012173919)
        ·
          refine ⟨43197798831214881018260879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28798532554143254012173919 43197798831214881018260879)
          ·
            refine ⟨64796698246822321527391319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43197798831214881018260879 64796698246822321527391319)
            ·
              refine ⟨97195047370233482291086979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64796698246822321527391319 97195047370233482291086979)
              ·
                refine ⟨145792571055350223436630469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97195047370233482291086979 145792571055350223436630469)
                ·
                  refine ⟨27336107072878166894368213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145792571055350223436630469 27336107072878166894368213)
                  ·
                    refine ⟨640690009520582036586755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27336107072878166894368213 640690009520582036586755)
                    ·
                      rfl

theorem cell22_1871609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_1871609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871609 prefixEnd_1871609 := by exact prefixLift 1871609
  have htrace : WordTrace (prefixWord ++ tailWord_1871609) baseStart_1871609 baseEnd_1871609 := by
    simpa [prefixWord, tailWord_1871609, baseEnd_1871609] using wordTrace_append hprefix tailTrace_1871609
  have hstable : (prefixWord ++ tailWord_1871609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871609).length < 2 ^ (prefixWord ++ tailWord_1871609).sum := by decide
  have hdescent : baseEnd_1871609 < baseStart_1871609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871636 : List Nat := [2, 4, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_1871636 : Nat := 118140960795 + 1871636 * 2 ^ 59
def prefixEnd_1871636 : Nat := 4983230072969 + 3 ^ 40 * 1871636 * 2
def baseEnd_1871636 : Nat := 640699252172362966161673

theorem tailTrace_1871636 : CollatzResearch.WordTrace tailWord_1871636 prefixEnd_1871636 640699252172362966161673 := by
  unfold tailWord_1871636
  simp only [CollatzResearch.WordTrace]
  refine ⟨34132086523694948412637381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45509448698259931216849841 34132086523694948412637381)
  ·
    refine ⟨6399766223192802827369509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34132086523694948412637381 6399766223192802827369509)
    ·
      refine ⟨1199956166848650530131783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6399766223192802827369509 1199956166848650530131783)
      ·
        refine ⟨1799934250272975795197675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1199956166848650530131783 1799934250272975795197675)
        ·
          refine ⟨2699901375409463692796513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1799934250272975795197675 2699901375409463692796513)
          ·
            refine ⟨2024926031557097769597385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2699901375409463692796513 2024926031557097769597385)
            ·
              refine ⟨1518694523667823327198039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2024926031557097769597385 1518694523667823327198039)
              ·
                refine ⟨2278041785501734990797059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1518694523667823327198039 2278041785501734990797059)
                ·
                  refine ⟨3417062678252602486195589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2278041785501734990797059 3417062678252602486195589)
                  ·
                    refine ⟨640699252172362966161673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3417062678252602486195589 640699252172362966161673)
                    ·
                      rfl

theorem cell22_1871636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_1871636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871636 prefixEnd_1871636 := by exact prefixLift 1871636
  have htrace : WordTrace (prefixWord ++ tailWord_1871636) baseStart_1871636 baseEnd_1871636 := by
    simpa [prefixWord, tailWord_1871636, baseEnd_1871636] using wordTrace_append hprefix tailTrace_1871636
  have hstable : (prefixWord ++ tailWord_1871636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871636).length < 2 ^ (prefixWord ++ tailWord_1871636).sum := by decide
  have hdescent : baseEnd_1871636 < baseStart_1871636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871660 : List Nat := [2, 2, 1, 1, 1, 5, 2, 4, 1, 3]
def baseStart_1871660 : Nat := 118140960795 + 1871660 * 2 ^ 59
def prefixEnd_1871660 : Nat := 4983230072969 + 3 ^ 40 * 1871660 * 2
def baseEnd_1871660 : Nat := 640707467862834903561599

theorem tailTrace_1871660 : CollatzResearch.WordTrace tailWord_1871660 prefixEnd_1871660 640707467862834903561599 := by
  unfold tailWord_1871660
  simp only [CollatzResearch.WordTrace]
  refine ⟨34132524199651474462074217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45510032266201965949432289 34132524199651474462074217)
  ·
    refine ⟨25599393149738605846555663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34132524199651474462074217 25599393149738605846555663)
    ·
      refine ⟨38399089724607908769833495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25599393149738605846555663 38399089724607908769833495)
      ·
        refine ⟨57598634586911863154750243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38399089724607908769833495 57598634586911863154750243)
        ·
          refine ⟨86397951880367794732125365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57598634586911863154750243 86397951880367794732125365)
          ·
            refine ⟨8099807988784480756136753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86397951880367794732125365 8099807988784480756136753)
            ·
              refine ⟨6074855991588360567102565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8099807988784480756136753 6074855991588360567102565)
              ·
                refine ⟨1139035498422817606331731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6074855991588360567102565 1139035498422817606331731)
                ·
                  refine ⟨1708553247634226409497597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139035498422817606331731 1708553247634226409497597)
                  ·
                    refine ⟨640707467862834903561599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1708553247634226409497597 640707467862834903561599)
                    ·
                      rfl

theorem cell22_1871660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 1, 3].length) (baseStart_1871660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871660 prefixEnd_1871660 := by exact prefixLift 1871660
  have htrace : WordTrace (prefixWord ++ tailWord_1871660) baseStart_1871660 baseEnd_1871660 := by
    simpa [prefixWord, tailWord_1871660, baseEnd_1871660] using wordTrace_append hprefix tailTrace_1871660
  have hstable : (prefixWord ++ tailWord_1871660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871660).length < 2 ^ (prefixWord ++ tailWord_1871660).sum := by decide
  have hdescent : baseEnd_1871660 < baseStart_1871660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871731 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 6, 4]
def baseStart_1871731 : Nat := 118140960795 + 1871731 * 2 ^ 59
def prefixEnd_1871731 : Nat := 4983230072969 + 3 ^ 40 * 1871731 * 2
def baseEnd_1871731 : Nat := 640731772613814385036381

theorem tailTrace_1871731 : CollatzResearch.WordTrace tailWord_1871731 prefixEnd_1871731 640731772613814385036381 := by
  unfold tailWord_1871731
  simp only [CollatzResearch.WordTrace]
  refine ⟨68267637982045728049983047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45511758654697152033322031 68267637982045728049983047)
  ·
    refine ⟨102401456973068592074974571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68267637982045728049983047 102401456973068592074974571)
    ·
      refine ⟨153602185459602888112461857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102401456973068592074974571 153602185459602888112461857)
      ·
        refine ⟨115201639094702166084346393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153602185459602888112461857 115201639094702166084346393)
        ·
          refine ⟨86401229321026624563259795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115201639094702166084346393 86401229321026624563259795)
          ·
            refine ⟨129601843981539936844889693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86401229321026624563259795 129601843981539936844889693)
            ·
              refine ⟨48600691493077476316833635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129601843981539936844889693 48600691493077476316833635)
              ·
                refine ⟨72901037239616214475250453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48600691493077476316833635 72901037239616214475250453)
                ·
                  refine ⟨3417236120607010053527365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72901037239616214475250453 3417236120607010053527365)
                  ·
                    refine ⟨640731772613814385036381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3417236120607010053527365 640731772613814385036381)
                    ·
                      rfl

theorem cell22_1871731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 4].length) (baseStart_1871731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871731 prefixEnd_1871731 := by exact prefixLift 1871731
  have htrace : WordTrace (prefixWord ++ tailWord_1871731) baseStart_1871731 baseEnd_1871731 := by
    simpa [prefixWord, tailWord_1871731, baseEnd_1871731] using wordTrace_append hprefix tailTrace_1871731
  have hstable : (prefixWord ++ tailWord_1871731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871731).length < 2 ^ (prefixWord ++ tailWord_1871731).sum := by decide
  have hdescent : baseEnd_1871731 < baseStart_1871731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871733 : List Nat := [1, 3, 4, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1871733 : Nat := 118140960795 + 1871733 * 2 ^ 59
def prefixEnd_1871733 : Nat := 4983230072969 + 3 ^ 40 * 1871733 * 2
def baseEnd_1871733 : Nat := 640732457254687046486375

theorem tailTrace_1871733 : CollatzResearch.WordTrace tailWord_1871733 prefixEnd_1871733 640732457254687046486375 := by
  unfold tailWord_1871733
  simp only [CollatzResearch.WordTrace]
  refine ⟨68267710928038482391555853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45511807285358988261037235 68267710928038482391555853)
  ·
    refine ⟨25600391598014430896833445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68267710928038482391555853 25600391598014430896833445)
    ·
      refine ⟨4800073424627705793156271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25600391598014430896833445 4800073424627705793156271)
      ·
        refine ⟨7200110136941558689734407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4800073424627705793156271 7200110136941558689734407)
        ·
          refine ⟨10800165205412338034601611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7200110136941558689734407 10800165205412338034601611)
          ·
            refine ⟨16200247808118507051902417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10800165205412338034601611 16200247808118507051902417)
            ·
              refine ⟨12150185856088880288926813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16200247808118507051902417 12150185856088880288926813)
              ·
                refine ⟨4556319696033330108347555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12150185856088880288926813 4556319696033330108347555)
                ·
                  refine ⟨6834479544049995162521333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4556319696033330108347555 6834479544049995162521333)
                  ·
                    refine ⟨640732457254687046486375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6834479544049995162521333 640732457254687046486375)
                    ·
                      rfl

theorem cell22_1871733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1871733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871733 prefixEnd_1871733 := by exact prefixLift 1871733
  have htrace : WordTrace (prefixWord ++ tailWord_1871733) baseStart_1871733 baseEnd_1871733 := by
    simpa [prefixWord, tailWord_1871733, baseEnd_1871733] using wordTrace_append hprefix tailTrace_1871733
  have hstable : (prefixWord ++ tailWord_1871733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871733).length < 2 ^ (prefixWord ++ tailWord_1871733).sum := by decide
  have hdescent : baseEnd_1871733 < baseStart_1871733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871748 : List Nat := [2, 3, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_1871748 : Nat := 118140960795 + 1871748 * 2 ^ 59
def prefixEnd_1871748 : Nat := 4983230072969 + 3 ^ 40 * 1871748 * 2
def baseEnd_1871748 : Nat := 640737592061232007361329

theorem tailTrace_1871748 : CollatzResearch.WordTrace tailWord_1871748 prefixEnd_1871748 640737592061232007361329 := by
  unfold tailWord_1871748
  simp only [CollatzResearch.WordTrace]
  refine ⟨34134129011492069976675949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45512172015322759968901265 34134129011492069976675949)
  ·
    refine ⟨12800298379309526241253481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34134129011492069976675949 12800298379309526241253481)
    ·
      refine ⟨9600223784482144680940111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12800298379309526241253481 9600223784482144680940111)
      ·
        refine ⟨14400335676723217021410167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9600223784482144680940111 14400335676723217021410167)
        ·
          refine ⟨21600503515084825532115251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14400335676723217021410167 21600503515084825532115251)
          ·
            refine ⟨32400755272627238298172877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21600503515084825532115251 32400755272627238298172877)
            ·
              refine ⟨12150283227235214361814829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32400755272627238298172877 12150283227235214361814829)
              ·
                refine ⟨4556356210213205385680561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12150283227235214361814829 4556356210213205385680561)
                ·
                  refine ⟨3417267157659904039260421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4556356210213205385680561 3417267157659904039260421)
                  ·
                    refine ⟨640737592061232007361329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3417267157659904039260421 640737592061232007361329)
                    ·
                      rfl

theorem cell22_1871748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_1871748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871748 prefixEnd_1871748 := by exact prefixLift 1871748
  have htrace : WordTrace (prefixWord ++ tailWord_1871748) baseStart_1871748 baseEnd_1871748 := by
    simpa [prefixWord, tailWord_1871748, baseEnd_1871748] using wordTrace_append hprefix tailTrace_1871748
  have hstable : (prefixWord ++ tailWord_1871748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871748).length < 2 ^ (prefixWord ++ tailWord_1871748).sum := by decide
  have hdescent : baseEnd_1871748 < baseStart_1871748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871855 : List Nat := [1, 1, 2, 1, 4, 2, 4, 2, 1, 4]
def baseStart_1871855 : Nat := 118140960795 + 1871855 * 2 ^ 59
def prefixEnd_1871855 : Nat := 4983230072969 + 3 ^ 40 * 1871855 * 2
def baseEnd_1871855 : Nat := 640774220347919394936001

theorem tailTrace_1871855 : CollatzResearch.WordTrace tailWord_1871855 prefixEnd_1871855 640774220347919394936001 := by
  unfold tailWord_1871855
  simp only [CollatzResearch.WordTrace]
  refine ⟨68272160633596497227497019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45514773755730998151664679 68272160633596497227497019)
  ·
    refine ⟨102408240950394745841245529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68272160633596497227497019 102408240950394745841245529)
    ·
      refine ⟨76806180712796059380934147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102408240950394745841245529 76806180712796059380934147)
      ·
        refine ⟨115209271069194089071401221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76806180712796059380934147 115209271069194089071401221)
        ·
          refine ⟨21601738325473891700887729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115209271069194089071401221 21601738325473891700887729)
          ·
            refine ⟨16201303744105418775665797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21601738325473891700887729 16201303744105418775665797)
            ·
              refine ⟨3037744452019766020437337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16201303744105418775665797 3037744452019766020437337)
              ·
                refine ⟨2278308339014824515328003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3037744452019766020437337 2278308339014824515328003)
                ·
                  refine ⟨3417462508522236772992005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2278308339014824515328003 3417462508522236772992005)
                  ·
                    refine ⟨640774220347919394936001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3417462508522236772992005 640774220347919394936001)
                    ·
                      rfl

theorem cell22_1871855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 4].length) (baseStart_1871855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871855 prefixEnd_1871855 := by exact prefixLift 1871855
  have htrace : WordTrace (prefixWord ++ tailWord_1871855) baseStart_1871855 baseEnd_1871855 := by
    simpa [prefixWord, tailWord_1871855, baseEnd_1871855] using wordTrace_append hprefix tailTrace_1871855
  have hstable : (prefixWord ++ tailWord_1871855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871855).length < 2 ^ (prefixWord ++ tailWord_1871855).sum := by decide
  have hdescent : baseEnd_1871855 < baseStart_1871855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871868 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 3, 5]
def baseStart_1871868 : Nat := 118140960795 + 1871868 * 2 ^ 59
def prefixEnd_1871868 : Nat := 4983230072969 + 3 ^ 40 * 1871868 * 2
def baseEnd_1871868 : Nat := 640778670513591694360961

theorem tailTrace_1871868 : CollatzResearch.WordTrace tailWord_1871868 prefixEnd_1871868 640778670513591694360961 := by
  unfold tailWord_1871868
  simp only [CollatzResearch.WordTrace]
  refine ⟨34136317391274700223860129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45515089855032933631813505 34136317391274700223860129)
  ·
    refine ⟨25602238043456025167895097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34136317391274700223860129 25602238043456025167895097)
    ·
      refine ⟨19201678532592018875921323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25602238043456025167895097 19201678532592018875921323)
      ·
        refine ⟨28802517798888028313881985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19201678532592018875921323 28802517798888028313881985)
        ·
          refine ⟨21601888349166021235411489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28802517798888028313881985 21601888349166021235411489)
          ·
            refine ⟨16201416261874515926558617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21601888349166021235411489 16201416261874515926558617)
            ·
              refine ⟨12151062196405886944918963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16201416261874515926558617 12151062196405886944918963)
              ·
                refine ⟨18226593294608830417378445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12151062196405886944918963 18226593294608830417378445)
                ·
                  refine ⟨6834972485478311406516917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18226593294608830417378445 6834972485478311406516917)
                  ·
                    refine ⟨640778670513591694360961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6834972485478311406516917 640778670513591694360961)
                    ·
                      rfl

theorem cell22_1871868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_1871868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871868 prefixEnd_1871868 := by exact prefixLift 1871868
  have htrace : WordTrace (prefixWord ++ tailWord_1871868) baseStart_1871868 baseEnd_1871868 := by
    simpa [prefixWord, tailWord_1871868, baseEnd_1871868] using wordTrace_append hprefix tailTrace_1871868
  have hstable : (prefixWord ++ tailWord_1871868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871868).length < 2 ^ (prefixWord ++ tailWord_1871868).sum := by decide
  have hdescent : baseEnd_1871868 < baseStart_1871868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871898 : List Nat := [3, 1, 1, 3, 1, 3, 1, 9]
def baseStart_1871898 : Nat := 118140960795 + 1871898 * 2 ^ 59
def prefixEnd_1871898 : Nat := 4983230072969 + 3 ^ 40 * 1871898 * 2
def baseEnd_1871898 : Nat := 71198771125186846234541

theorem tailTrace_1871898 : CollatzResearch.WordTrace tailWord_1871898 prefixEnd_1871898 71198771125186846234541 := by
  unfold tailWord_1871898
  simp only [CollatzResearch.WordTrace]
  refine ⟨17068432243110178892828087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45515819314960477047541565 17068432243110178892828087)
  ·
    refine ⟨25602648364665268339242131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17068432243110178892828087 25602648364665268339242131)
    ·
      refine ⟨38403972546997902508863197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25602648364665268339242131 38403972546997902508863197)
      ·
        refine ⟨14401489705124213440823699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38403972546997902508863197 14401489705124213440823699)
        ·
          refine ⟨21602234557686320161235549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14401489705124213440823699 21602234557686320161235549)
          ·
            refine ⟨8100837959132370060463331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21602234557686320161235549 8100837959132370060463331)
            ·
              refine ⟨12151256938698555090694997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8100837959132370060463331 12151256938698555090694997)
              ·
                refine ⟨71198771125186846234541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12151256938698555090694997 71198771125186846234541)
                ·
                  rfl

theorem cell22_1871898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 9].length) (baseStart_1871898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871898 prefixEnd_1871898 := by exact prefixLift 1871898
  have htrace : WordTrace (prefixWord ++ tailWord_1871898) baseStart_1871898 baseEnd_1871898 := by
    simpa [prefixWord, tailWord_1871898, baseEnd_1871898] using wordTrace_append hprefix tailTrace_1871898
  have hstable : (prefixWord ++ tailWord_1871898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871898).length < 2 ^ (prefixWord ++ tailWord_1871898).sum := by decide
  have hdescent : baseEnd_1871898 < baseStart_1871898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871947 : List Nat := [1, 1, 1, 1, 3, 1, 2, 8, 1, 3]
def baseStart_1871947 : Nat := 118140960795 + 1871947 * 2 ^ 59
def prefixEnd_1871947 : Nat := 4983230072969 + 3 ^ 40 * 1871947 * 2
def baseEnd_1871947 : Nat := 640805713828061821635719

theorem tailTrace_1871947 : CollatzResearch.WordTrace tailWord_1871947 prefixEnd_1871947 640805713828061821635719 := by
  unfold tailWord_1871947
  simp only [CollatzResearch.WordTrace]
  refine ⟨68275516149263196939846095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45517010766175464626564063 68275516149263196939846095)
  ·
    refine ⟨102413274223894795409769143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68275516149263196939846095 102413274223894795409769143)
    ·
      refine ⟨153619911335842193114653715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102413274223894795409769143 153619911335842193114653715)
      ·
        refine ⟨230429867003763289671980573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153619911335842193114653715 230429867003763289671980573)
        ·
          refine ⟨86411200126411233626992715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230429867003763289671980573 86411200126411233626992715)
          ·
            refine ⟨129616800189616850440489073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86411200126411233626992715 129616800189616850440489073)
            ·
              refine ⟨97212600142212637830366805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129616800189616850440489073 97212600142212637830366805)
              ·
                refine ⟨1139210157916554349574611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 97212600142212637830366805 1139210157916554349574611)
                ·
                  refine ⟨1708815236874831524361917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139210157916554349574611 1708815236874831524361917)
                  ·
                    refine ⟨640805713828061821635719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1708815236874831524361917 640805713828061821635719)
                    ·
                      rfl

theorem cell22_1871947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 1, 3].length) (baseStart_1871947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871947 prefixEnd_1871947 := by exact prefixLift 1871947
  have htrace : WordTrace (prefixWord ++ tailWord_1871947) baseStart_1871947 baseEnd_1871947 := by
    simpa [prefixWord, tailWord_1871947, baseEnd_1871947] using wordTrace_append hprefix tailTrace_1871947
  have hstable : (prefixWord ++ tailWord_1871947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871947).length < 2 ^ (prefixWord ++ tailWord_1871947).sum := by decide
  have hdescent : baseEnd_1871947 < baseStart_1871947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871960 : List Nat := [2, 1, 2, 2, 1, 4, 2, 3, 5]
def baseStart_1871960 : Nat := 118140960795 + 1871960 * 2 ^ 59
def prefixEnd_1871960 : Nat := 4983230072969 + 3 ^ 40 * 1871960 * 2
def baseEnd_1871960 : Nat := 213603387997911373686893

theorem tailTrace_1871960 : CollatzResearch.WordTrace tailWord_1871960 prefixEnd_1871960 213603387997911373686893 := by
  unfold tailWord_1871960
  simp only [CollatzResearch.WordTrace]
  refine ⟨34137995149108050080034667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45517326865477400106712889 34137995149108050080034667)
  ·
    refine ⟨51206992723662075120052001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34137995149108050080034667 51206992723662075120052001)
    ·
      refine ⟨38405244542746556340039001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51206992723662075120052001 38405244542746556340039001)
      ·
        refine ⟨28803933407059917255029251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38405244542746556340039001 28803933407059917255029251)
        ·
          refine ⟨43205900110589875882543877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28803933407059917255029251 43205900110589875882543877)
          ·
            refine ⟨8101106270735601727976977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43205900110589875882543877 8101106270735601727976977)
            ·
              refine ⟨6075829703051701295982733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8101106270735601727976977 6075829703051701295982733)
              ·
                refine ⟨2278436138644387985993525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6075829703051701295982733 2278436138644387985993525)
                ·
                  refine ⟨213603387997911373686893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2278436138644387985993525 213603387997911373686893)
                  ·
                    rfl

theorem cell22_1871960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 5].length) (baseStart_1871960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871960 prefixEnd_1871960 := by exact prefixLift 1871960
  have htrace : WordTrace (prefixWord ++ tailWord_1871960) baseStart_1871960 baseEnd_1871960 := by
    simpa [prefixWord, tailWord_1871960, baseEnd_1871960] using wordTrace_append hprefix tailTrace_1871960
  have hstable : (prefixWord ++ tailWord_1871960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871960).length < 2 ^ (prefixWord ++ tailWord_1871960).sum := by decide
  have hdescent : baseEnd_1871960 < baseStart_1871960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871966 : List Nat := [4, 4, 1, 1, 2, 1, 3, 6]
def baseStart_1871966 : Nat := 118140960795 + 1871966 * 2 ^ 59
def prefixEnd_1871966 : Nat := 4983230072969 + 3 ^ 40 * 1871966 * 2
def baseEnd_1871966 : Nat := 71201357546261345045629

theorem tailTrace_1871966 : CollatzResearch.WordTrace tailWord_1871966 prefixEnd_1871966 71201357546261345045629 := by
  unfold tailWord_1871966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8534526142024295398098469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45517472757462908789858501 8534526142024295398098469)
  ·
    refine ⟨1600223651629555387143463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8534526142024295398098469 1600223651629555387143463)
    ·
      refine ⟨2400335477444333080715195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1600223651629555387143463 2400335477444333080715195)
      ·
        refine ⟨3600503216166499621072793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2400335477444333080715195 3600503216166499621072793)
        ·
          refine ⟨2700377412124874715804595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3600503216166499621072793 2700377412124874715804595)
          ·
            refine ⟨4050566118187312073706893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2700377412124874715804595 4050566118187312073706893)
            ·
              refine ⟨1518962294320242027640085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4050566118187312073706893 1518962294320242027640085)
              ·
                refine ⟨71201357546261345045629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1518962294320242027640085 71201357546261345045629)
                ·
                  rfl

theorem cell22_1871966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_1871966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1871966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1871966 prefixEnd_1871966 := by exact prefixLift 1871966
  have htrace : WordTrace (prefixWord ++ tailWord_1871966) baseStart_1871966 baseEnd_1871966 := by
    simpa [prefixWord, tailWord_1871966, baseEnd_1871966] using wordTrace_append hprefix tailTrace_1871966
  have hstable : (prefixWord ++ tailWord_1871966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871966).length < 2 ^ (prefixWord ++ tailWord_1871966).sum := by decide
  have hdescent : baseEnd_1871966 < baseStart_1871966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872005 : List Nat := [1, 3, 1, 1, 5, 1, 1, 3, 6]
def baseStart_1872005 : Nat := 118140960795 + 1872005 * 2 ^ 59
def prefixEnd_1872005 : Nat := 4983230072969 + 3 ^ 40 * 1872005 * 2
def baseEnd_1872005 : Nat := 213608522804456334561847

theorem tailTrace_1872005 : CollatzResearch.WordTrace tailWord_1872005 prefixEnd_1872005 213608522804456334561847 := by
  unfold tailWord_1872005
  simp only [CollatzResearch.WordTrace]
  refine ⟨68277631583053072845457469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45518421055368715230304979 68277631583053072845457469)
  ·
    refine ⟨25604111843644902317046551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68277631583053072845457469 25604111843644902317046551)
    ·
      refine ⟨38406167765467353475569827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25604111843644902317046551 38406167765467353475569827)
      ·
        refine ⟨57609251648201030213354741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38406167765467353475569827 57609251648201030213354741)
        ·
          refine ⟨5400867342018846582502007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57609251648201030213354741 5400867342018846582502007)
          ·
            refine ⟨8101301013028269873753011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5400867342018846582502007 8101301013028269873753011)
            ·
              refine ⟨12151951519542404810629517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8101301013028269873753011 12151951519542404810629517)
              ·
                refine ⟨4556981819828401803986069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12151951519542404810629517 4556981819828401803986069)
                ·
                  refine ⟨213608522804456334561847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4556981819828401803986069 213608522804456334561847)
                  ·
                    rfl

theorem cell22_1872005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_1872005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872005 prefixEnd_1872005 := by exact prefixLift 1872005
  have htrace : WordTrace (prefixWord ++ tailWord_1872005) baseStart_1872005 baseEnd_1872005 := by
    simpa [prefixWord, tailWord_1872005, baseEnd_1872005] using wordTrace_append hprefix tailTrace_1872005
  have hstable : (prefixWord ++ tailWord_1872005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872005).length < 2 ^ (prefixWord ++ tailWord_1872005).sum := by decide
  have hdescent : baseEnd_1872005 < baseStart_1872005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872024 : List Nat := [2, 1, 2, 4, 3, 1, 2, 2, 1, 4]
def baseStart_1872024 : Nat := 118140960795 + 1872024 * 2 ^ 59
def prefixEnd_1872024 : Nat := 4983230072969 + 3 ^ 40 * 1872024 * 2
def baseEnd_1872024 : Nat := 640832072501659287460483

theorem tailTrace_1872024 : CollatzResearch.WordTrace tailWord_1872024 prefixEnd_1872024 640832072501659287460483 := by
  unfold tailWord_1872024
  simp only [CollatzResearch.WordTrace]
  refine ⟨34139162284992119545199563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45518883046656159393599417 34139162284992119545199563)
  ·
    refine ⟨51208743427488179317799345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34139162284992119545199563 51208743427488179317799345)
    ·
      refine ⟨38406557570616134488349509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51208743427488179317799345 38406557570616134488349509)
      ·
        refine ⟨7201229544490525216565533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38406557570616134488349509 7201229544490525216565533)
        ·
          refine ⟨2700461079183946956212075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7201229544490525216565533 2700461079183946956212075)
          ·
            refine ⟨4050691618775920434318113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2700461079183946956212075 4050691618775920434318113)
            ·
              refine ⟨3038018714081940325738585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4050691618775920434318113 3038018714081940325738585)
              ·
                refine ⟨2278514035561455244303939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3038018714081940325738585 2278514035561455244303939)
                ·
                  refine ⟨3417771053342182866455909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2278514035561455244303939 3417771053342182866455909)
                  ·
                    refine ⟨640832072501659287460483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3417771053342182866455909 640832072501659287460483)
                    ·
                      rfl

theorem cell22_1872024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_1872024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872024 prefixEnd_1872024 := by exact prefixLift 1872024
  have htrace : WordTrace (prefixWord ++ tailWord_1872024) baseStart_1872024 baseEnd_1872024 := by
    simpa [prefixWord, tailWord_1872024, baseEnd_1872024] using wordTrace_append hprefix tailTrace_1872024
  have hstable : (prefixWord ++ tailWord_1872024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872024).length < 2 ^ (prefixWord ++ tailWord_1872024).sum := by decide
  have hdescent : baseEnd_1872024 < baseStart_1872024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872086 : List Nat := [5, 2, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_1872086 : Nat := 118140960795 + 1872086 * 2 ^ 59
def prefixEnd_1872086 : Nat := 4983230072969 + 3 ^ 40 * 1872086 * 2
def baseEnd_1872086 : Nat := 640853296368711792410293

theorem tailTrace_1872086 : CollatzResearch.WordTrace tailWord_1872086 prefixEnd_1872086 640853296368711792410293 := by
  unfold tailWord_1872086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4267536618484976479947257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45520390597173082452770741 4267536618484976479947257)
  ·
    refine ⟨3200652463863732359960443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4267536618484976479947257 3200652463863732359960443)
    ·
      refine ⟨4800978695795598539940665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3200652463863732359960443 4800978695795598539940665)
      ·
        refine ⟨3600734021846698904955499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4800978695795598539940665 3600734021846698904955499)
        ·
          refine ⟨5401101032770048357433249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3600734021846698904955499 5401101032770048357433249)
          ·
            refine ⟨4050825774577536268074937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5401101032770048357433249 4050825774577536268074937)
            ·
              refine ⟨3038119330933152201056203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4050825774577536268074937 3038119330933152201056203)
              ·
                refine ⟨4557178996399728301584305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3038119330933152201056203 4557178996399728301584305)
                ·
                  refine ⟨3417884247299796226188229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4557178996399728301584305 3417884247299796226188229)
                  ·
                    refine ⟨640853296368711792410293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3417884247299796226188229 640853296368711792410293)
                    ·
                      rfl

theorem cell22_1872086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_1872086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872086 prefixEnd_1872086 := by exact prefixLift 1872086
  have htrace : WordTrace (prefixWord ++ tailWord_1872086) baseStart_1872086 baseEnd_1872086 := by
    simpa [prefixWord, tailWord_1872086, baseEnd_1872086] using wordTrace_append hprefix tailTrace_1872086
  have hstable : (prefixWord ++ tailWord_1872086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872086).length < 2 ^ (prefixWord ++ tailWord_1872086).sum := by decide
  have hdescent : baseEnd_1872086 < baseStart_1872086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872142 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_1872142 : Nat := 118140960795 + 1872142 * 2 ^ 59
def prefixEnd_1872142 : Nat := 4983230072969 + 3 ^ 40 * 1872142 * 2
def baseEnd_1872142 : Nat := 640872466313146313010121

theorem tailTrace_1872142 : CollatzResearch.WordTrace tailWord_1872142 prefixEnd_1872142 640872466313146313010121 := by
  unfold tailWord_1872142
  simp only [CollatzResearch.WordTrace]
  refine ⟨8535328547944593155399335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45521752255704496828796453 8535328547944593155399335)
  ·
    refine ⟨12802992821916889733099003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8535328547944593155399335 12802992821916889733099003)
    ·
      refine ⟨19204489232875334599648505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12802992821916889733099003 19204489232875334599648505)
      ·
        refine ⟨14403366924656500949736379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19204489232875334599648505 14403366924656500949736379)
        ·
          refine ⟨21605050386984751424604569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14403366924656500949736379 21605050386984751424604569)
          ·
            refine ⟨16203787790238563568453427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21605050386984751424604569 16203787790238563568453427)
            ·
              refine ⟨24305681685357845352680141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16203787790238563568453427 24305681685357845352680141)
              ·
                refine ⟨9114630632009192007255053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24305681685357845352680141 9114630632009192007255053)
                ·
                  refine ⟨3417986487003447002720645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9114630632009192007255053 3417986487003447002720645)
                  ·
                    refine ⟨640872466313146313010121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3417986487003447002720645 640872466313146313010121)
                    ·
                      rfl

theorem cell22_1872142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_1872142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872142 prefixEnd_1872142 := by exact prefixLift 1872142
  have htrace : WordTrace (prefixWord ++ tailWord_1872142) baseStart_1872142 baseEnd_1872142 := by
    simpa [prefixWord, tailWord_1872142, baseEnd_1872142] using wordTrace_append hprefix tailTrace_1872142
  have hstable : (prefixWord ++ tailWord_1872142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872142).length < 2 ^ (prefixWord ++ tailWord_1872142).sum := by decide
  have hdescent : baseEnd_1872142 < baseStart_1872142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872159 : List Nat := [1, 1, 2, 4, 3, 2, 1, 3, 1, 4]
def baseStart_1872159 : Nat := 118140960795 + 1872159 * 2 ^ 59
def prefixEnd_1872159 : Nat := 4983230072969 + 3 ^ 40 * 1872159 * 2
def baseEnd_1872159 : Nat := 640878285760563935335069

theorem tailTrace_1872159 : CollatzResearch.WordTrace tailWord_1872159 prefixEnd_1872159 640878285760563935335069 := by
  unfold tailWord_1872159
  simp only [CollatzResearch.WordTrace]
  refine ⟨68283248424495157146563531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45522165616330104764375687 68283248424495157146563531)
  ·
    refine ⟨102424872636742735719845297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68283248424495157146563531 102424872636742735719845297)
    ·
      refine ⟨76818654477557051789883973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102424872636742735719845297 76818654477557051789883973)
      ·
        refine ⟨14403497714541947210603245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76818654477557051789883973 14403497714541947210603245)
        ·
          refine ⟨5401311642953230203976217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14403497714541947210603245 5401311642953230203976217)
          ·
            refine ⟨4050983732214922652982163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5401311642953230203976217 4050983732214922652982163)
            ·
              refine ⟨6076475598322383979473245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4050983732214922652982163 6076475598322383979473245)
              ·
                refine ⟨2278678349370893992302467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6076475598322383979473245 2278678349370893992302467)
                ·
                  refine ⟨3418017524056340988453701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2278678349370893992302467 3418017524056340988453701)
                  ·
                    refine ⟨640878285760563935335069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3418017524056340988453701 640878285760563935335069)
                    ·
                      rfl

theorem cell22_1872159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 4].length) (baseStart_1872159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872159 prefixEnd_1872159 := by exact prefixLift 1872159
  have htrace : WordTrace (prefixWord ++ tailWord_1872159) baseStart_1872159 baseEnd_1872159 := by
    simpa [prefixWord, tailWord_1872159, baseEnd_1872159] using wordTrace_append hprefix tailTrace_1872159
  have hstable : (prefixWord ++ tailWord_1872159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872159).length < 2 ^ (prefixWord ++ tailWord_1872159).sum := by decide
  have hdescent : baseEnd_1872159 < baseStart_1872159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872296 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1872296 : Nat := 118140960795 + 1872296 * 2 ^ 59
def prefixEnd_1872296 : Nat := 4983230072969 + 3 ^ 40 * 1872296 * 2
def baseEnd_1872296 : Nat := 640925183660341244659649

theorem tailTrace_1872296 : CollatzResearch.WordTrace tailWord_1872296 prefixEnd_1872296 640925183660341244659649 := by
  unfold tailWord_1872296
  simp only [CollatzResearch.WordTrace]
  refine ⟨34144122612499414772150371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45525496816665886362867161 34144122612499414772150371)
  ·
    refine ⟨51216183918749122158225557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34144122612499414772150371 51216183918749122158225557)
    ·
      refine ⟨2400758621191365101166823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51216183918749122158225557 2400758621191365101166823)
      ·
        refine ⟨3601137931787047651750235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2400758621191365101166823 3601137931787047651750235)
        ·
          refine ⟨5401706897680571477625353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3601137931787047651750235 5401706897680571477625353)
          ·
            refine ⟨4051280173260428608219015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5401706897680571477625353 4051280173260428608219015)
            ·
              refine ⟨6076920259890642912328523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4051280173260428608219015 6076920259890642912328523)
              ·
                refine ⟨9115380389835964368492785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6076920259890642912328523 9115380389835964368492785)
                ·
                  refine ⟨6836535292376973276369589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9115380389835964368492785 6836535292376973276369589)
                  ·
                    refine ⟨640925183660341244659649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6836535292376973276369589 640925183660341244659649)
                    ·
                      rfl

theorem cell22_1872296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1872296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872296 prefixEnd_1872296 := by exact prefixLift 1872296
  have htrace : WordTrace (prefixWord ++ tailWord_1872296) baseStart_1872296 baseEnd_1872296 := by
    simpa [prefixWord, tailWord_1872296, baseEnd_1872296] using wordTrace_append hprefix tailTrace_1872296
  have hstable : (prefixWord ++ tailWord_1872296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872296).length < 2 ^ (prefixWord ++ tailWord_1872296).sum := by decide
  have hdescent : baseEnd_1872296 < baseStart_1872296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872328 : List Nat := [2, 1, 3, 1, 3, 4, 2, 1, 1, 4]
def baseStart_1872328 : Nat := 118140960795 + 1872328 * 2 ^ 59
def prefixEnd_1872328 : Nat := 4983230072969 + 3 ^ 40 * 1872328 * 2
def baseEnd_1872328 : Nat := 640936137914303827859551

theorem tailTrace_1872328 : CollatzResearch.WordTrace tailWord_1872328 prefixEnd_1872328 640936137914303827859551 := by
  unfold tailWord_1872328
  simp only [CollatzResearch.WordTrace]
  refine ⟨34144706180441449504732819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45526274907255266006310425 34144706180441449504732819)
  ·
    refine ⟨51217059270662174257099229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34144706180441449504732819 51217059270662174257099229)
    ·
      refine ⟨19206397226498315346412211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51217059270662174257099229 19206397226498315346412211)
      ·
        refine ⟨28809595839747473019618317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19206397226498315346412211 28809595839747473019618317)
        ·
          refine ⟨10803598439905302382356869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28809595839747473019618317 10803598439905302382356869)
          ·
            refine ⟨2025674707482244196691913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10803598439905302382356869 2025674707482244196691913)
            ·
              refine ⟨1519256030611683147518935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2025674707482244196691913 1519256030611683147518935)
              ·
                refine ⟨2278884045917524721278403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1519256030611683147518935 2278884045917524721278403)
                ·
                  refine ⟨3418326068876287081917605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2278884045917524721278403 3418326068876287081917605)
                  ·
                    refine ⟨640936137914303827859551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3418326068876287081917605 640936137914303827859551)
                    ·
                      rfl

theorem cell22_1872328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_1872328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872328 prefixEnd_1872328 := by exact prefixLift 1872328
  have htrace : WordTrace (prefixWord ++ tailWord_1872328) baseStart_1872328 baseEnd_1872328 := by
    simpa [prefixWord, tailWord_1872328, baseEnd_1872328] using wordTrace_append hprefix tailTrace_1872328
  have hstable : (prefixWord ++ tailWord_1872328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872328).length < 2 ^ (prefixWord ++ tailWord_1872328).sum := by decide
  have hdescent : baseEnd_1872328 < baseStart_1872328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
