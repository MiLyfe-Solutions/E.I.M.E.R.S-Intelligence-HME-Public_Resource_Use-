import V185TrunkScan23Chunk0911

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5398335 : List Nat := [1, 1, 2, 2, 6, 1, 10]
def baseStart_5398335 : Nat := 118140960795 + 5398335 * 2 ^ 59
def prefixEnd_5398335 : Nat := 4983230072969 + 3 ^ 40 * 5398335 * 2
def baseEnd_5398335 : Nat := 34221488752953601520815

theorem tailTrace_5398335 : CollatzResearch.WordTrace tailWord_5398335 prefixEnd_5398335 34221488752953601520815 := by
  unfold tailWord_5398335
  simp only [CollatzResearch.WordTrace]
  refine ⟨196893452897761732061948459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131262301931841154707965639 196893452897761732061948459)
  ·
    refine ⟨295340179346642598092922689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196893452897761732061948459 295340179346642598092922689)
    ·
      refine ⟨221505134509981948569692017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295340179346642598092922689 221505134509981948569692017)
      ·
        refine ⟨166128850882486461427269013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221505134509981948569692017 166128850882486461427269013)
        ·
          refine ⟨7787289885116552879403235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 166128850882486461427269013 7787289885116552879403235)
          ·
            refine ⟨11680934827674829319104853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7787289885116552879403235 11680934827674829319104853)
            ·
              refine ⟨34221488752953601520815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11680934827674829319104853 34221488752953601520815)
              ·
                rfl

theorem cell23_5398335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 10].length) (baseStart_5398335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398335 prefixEnd_5398335 := by exact prefixLift 5398335
  have htrace : WordTrace (prefixWord ++ tailWord_5398335) baseStart_5398335 baseEnd_5398335 := by
    simpa [prefixWord, tailWord_5398335, baseEnd_5398335] using wordTrace_append hprefix tailTrace_5398335
  have hstable : (prefixWord ++ tailWord_5398335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398335).length < 2 ^ (prefixWord ++ tailWord_5398335).sum := by decide
  have hdescent : baseEnd_5398335 < baseStart_5398335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398339 : List Nat := [1, 1, 1, 3, 1, 7, 1, 2, 2, 4]
def baseStart_5398339 : Nat := 118140960795 + 5398339 * 2 ^ 59
def prefixEnd_5398339 : Nat := 4983230072969 + 3 ^ 40 * 5398339 * 2
def baseEnd_5398339 : Nat := 923980880970619902511999

theorem tailTrace_5398339 : CollatzResearch.WordTrace tailWord_5398339 prefixEnd_5398339 923980880970619902511999 := by
  unfold tailWord_5398339
  simp only [CollatzResearch.WordTrace]
  refine ⟨196893598789747240745094071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131262399193164827163396047 196893598789747240745094071)
  ·
    refine ⟨295340398184620861117641107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196893598789747240745094071 295340398184620861117641107)
    ·
      refine ⟨443010597276931291676461661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295340398184620861117641107 443010597276931291676461661)
      ·
        refine ⟨166128973978849234378673123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 443010597276931291676461661 166128973978849234378673123)
        ·
          refine ⟨249193460968273851568009685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166128973978849234378673123 249193460968273851568009685)
          ·
            refine ⟨5840471741443918396125227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 249193460968273851568009685 5840471741443918396125227)
            ·
              refine ⟨8760707612165877594187841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5840471741443918396125227 8760707612165877594187841)
              ·
                refine ⟨6570530709124408195640881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8760707612165877594187841 6570530709124408195640881)
                ·
                  refine ⟨4927898031843306146730661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6570530709124408195640881 4927898031843306146730661)
                  ·
                    refine ⟨923980880970619902511999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4927898031843306146730661 923980880970619902511999)
                    ·
                      rfl

theorem cell23_5398339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 4].length) (baseStart_5398339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398339 prefixEnd_5398339 := by exact prefixLift 5398339
  have htrace : WordTrace (prefixWord ++ tailWord_5398339) baseStart_5398339 baseEnd_5398339 := by
    simpa [prefixWord, tailWord_5398339, baseEnd_5398339] using wordTrace_append hprefix tailTrace_5398339
  have hstable : (prefixWord ++ tailWord_5398339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398339).length < 2 ^ (prefixWord ++ tailWord_5398339).sum := by decide
  have hdescent : baseEnd_5398339 < baseStart_5398339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398346 : List Nat := [3, 1, 2, 1, 1, 1, 3, 6, 1, 2, 2]
def baseStart_5398346 : Nat := 118140960795 + 5398346 * 2 ^ 59
def prefixEnd_5398346 : Nat := 4983230072969 + 3 ^ 40 * 5398346 * 2
def baseEnd_5398346 : Nat := 2771946237276441180148465

theorem tailTrace_5398346 : CollatzResearch.WordTrace tailWord_5398346 prefixEnd_5398346 2771946237276441180148465 := by
  unfold tailWord_5398346
  simp only [CollatzResearch.WordTrace]
  refine ⟨49223463525180470235149723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131262569400481253960399261 49223463525180470235149723)
  ·
    refine ⟨73835195287770705352724585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49223463525180470235149723 73835195287770705352724585)
    ·
      refine ⟨55376396465828029014543439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73835195287770705352724585 55376396465828029014543439)
      ·
        refine ⟨83064594698742043521815159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55376396465828029014543439 83064594698742043521815159)
        ·
          refine ⟨124596892048113065282722739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83064594698742043521815159 124596892048113065282722739)
          ·
            refine ⟨186895338072169597924084109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124596892048113065282722739 186895338072169597924084109)
            ·
              refine ⟨70085751777063599221531541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186895338072169597924084109 70085751777063599221531541)
              ·
                refine ⟨3285269614549856213509291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70085751777063599221531541 3285269614549856213509291)
                ·
                  refine ⟨4927904421824784320263937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3285269614549856213509291 4927904421824784320263937)
                  ·
                    refine ⟨3695928316368588240197953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4927904421824784320263937 3695928316368588240197953)
                    ·
                      refine ⟨2771946237276441180148465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3695928316368588240197953 2771946237276441180148465)
                      ·
                        rfl

theorem cell23_5398346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 1, 2, 2].length) (baseStart_5398346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398346 prefixEnd_5398346 := by exact prefixLift 5398346
  have htrace : WordTrace (prefixWord ++ tailWord_5398346) baseStart_5398346 baseEnd_5398346 := by
    simpa [prefixWord, tailWord_5398346, baseEnd_5398346] using wordTrace_append hprefix tailTrace_5398346
  have hstable : (prefixWord ++ tailWord_5398346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398346).length < 2 ^ (prefixWord ++ tailWord_5398346).sum := by decide
  have hdescent : baseEnd_5398346 < baseStart_5398346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398349 : List Nat := [1, 6, 1, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_5398349 : Nat := 118140960795 + 5398349 * 2 ^ 59
def prefixEnd_5398349 : Nat := 4983230072969 + 3 ^ 40 * 5398349 * 2
def baseEnd_5398349 : Nat := 2771947777718404668410951

theorem tailTrace_5398349 : CollatzResearch.WordTrace tailWord_5398349 prefixEnd_5398349 2771947777718404668410951 := by
  unfold tailWord_5398349
  simp only [CollatzResearch.WordTrace]
  refine ⟨196893963519711012452958101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131262642346474008301972067 196893963519711012452958101)
  ·
    refine ⟨9229404539986453708732411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 196893963519711012452958101 9229404539986453708732411)
    ·
      refine ⟨13844106809979680563098617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9229404539986453708732411 13844106809979680563098617)
      ·
        refine ⟨10383080107484760422323963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13844106809979680563098617 10383080107484760422323963)
        ·
          refine ⟨15574620161227140633485945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10383080107484760422323963 15574620161227140633485945)
          ·
            refine ⟨11680965120920355475114459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15574620161227140633485945 11680965120920355475114459)
            ·
              refine ⟨17521447681380533212671689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11680965120920355475114459 17521447681380533212671689)
              ·
                refine ⟨13141085761035399909503767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17521447681380533212671689 13141085761035399909503767)
                ·
                  refine ⟨19711628641553099864255651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13141085761035399909503767 19711628641553099864255651)
                  ·
                    refine ⟨29567442962329649796383477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19711628641553099864255651 29567442962329649796383477)
                    ·
                      refine ⟨2771947777718404668410951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29567442962329649796383477 2771947777718404668410951)
                      ·
                        rfl

theorem cell23_5398349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_5398349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398349 prefixEnd_5398349 := by exact prefixLift 5398349
  have htrace : WordTrace (prefixWord ++ tailWord_5398349) baseStart_5398349 baseEnd_5398349 := by
    simpa [prefixWord, tailWord_5398349, baseEnd_5398349] using wordTrace_append hprefix tailTrace_5398349
  have hstable : (prefixWord ++ tailWord_5398349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398349).length < 2 ^ (prefixWord ++ tailWord_5398349).sum := by decide
  have hdescent : baseEnd_5398349 < baseStart_5398349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398356 : List Nat := [2, 4, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_5398356 : Nat := 118140960795 + 5398356 * 2 ^ 59
def prefixEnd_5398356 : Nat := 4983230072969 + 3 ^ 40 * 5398356 * 2
def baseEnd_5398356 : Nat := 923983790694328713674473

theorem tailTrace_5398356 : CollatzResearch.WordTrace tailWord_5398356 prefixEnd_5398356 923983790694328713674473 := by
  unfold tailWord_5398356
  simp only [CollatzResearch.WordTrace]
  refine ⟨98447109415342826324231461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131262812553790435098975281 98447109415342826324231461)
  ·
    refine ⟨18458833015376779935793399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98447109415342826324231461 18458833015376779935793399)
    ·
      refine ⟨27688249523065169903690099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18458833015376779935793399 27688249523065169903690099)
      ·
        refine ⟨41532374284597754855535149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27688249523065169903690099 41532374284597754855535149)
        ·
          refine ⟨15574640356724158070825681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41532374284597754855535149 15574640356724158070825681)
          ·
            refine ⟨11680980267543118553119261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15574640356724158070825681 11680980267543118553119261)
            ·
              refine ⟨4380367600328669457419723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11680980267543118553119261 4380367600328669457419723)
              ·
                refine ⟨6570551400493004186129585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4380367600328669457419723 6570551400493004186129585)
                ·
                  refine ⟨4927913550369753139597189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6570551400493004186129585 4927913550369753139597189)
                  ·
                    refine ⟨923983790694328713674473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4927913550369753139597189 923983790694328713674473)
                    ·
                      rfl

theorem cell23_5398356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_5398356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398356 prefixEnd_5398356 := by exact prefixLift 5398356
  have htrace : WordTrace (prefixWord ++ tailWord_5398356) baseStart_5398356 baseEnd_5398356 := by
    simpa [prefixWord, tailWord_5398356, baseEnd_5398356] using wordTrace_append hprefix tailTrace_5398356
  have hstable : (prefixWord ++ tailWord_5398356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398356).length < 2 ^ (prefixWord ++ tailWord_5398356).sum := by decide
  have hdescent : baseEnd_5398356 < baseStart_5398356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398359 : List Nat := [1, 1, 3, 2, 5, 2, 1, 1, 1, 2, 4]
def baseStart_5398359 : Nat := 118140960795 + 5398359 * 2 ^ 59
def prefixEnd_5398359 : Nat := 4983230072969 + 3 ^ 40 * 5398359 * 2
def baseEnd_5398359 : Nat := 2771952912524949629285905

theorem tailTrace_5398359 : CollatzResearch.WordTrace tailWord_5398359 prefixEnd_5398359 2771952912524949629285905 := by
  unfold tailWord_5398359
  simp only [CollatzResearch.WordTrace]
  refine ⟨196894328249674784160822131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131262885499783189440548087 196894328249674784160822131)
  ·
    refine ⟨295341492374512176241233197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196894328249674784160822131 295341492374512176241233197)
    ·
      refine ⟨110753059640442066090462449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295341492374512176241233197 110753059640442066090462449)
      ·
        refine ⟨83064794730331549567846837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110753059640442066090462449 83064794730331549567846837)
        ·
          refine ⟨7787324505968582771985641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83064794730331549567846837 7787324505968582771985641)
          ·
            refine ⟨5840493379476437078989231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7787324505968582771985641 5840493379476437078989231)
            ·
              refine ⟨8760740069214655618483847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5840493379476437078989231 8760740069214655618483847)
              ·
                refine ⟨13141110103821983427725771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8760740069214655618483847 13141110103821983427725771)
                ·
                  refine ⟨19711665155732975141588657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13141110103821983427725771 19711665155732975141588657)
                  ·
                    refine ⟨14783748866799731356191493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19711665155732975141588657 14783748866799731356191493)
                    ·
                      refine ⟨2771952912524949629285905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14783748866799731356191493 2771952912524949629285905)
                      ·
                        rfl

theorem cell23_5398359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_5398359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398359 prefixEnd_5398359 := by exact prefixLift 5398359
  have htrace : WordTrace (prefixWord ++ tailWord_5398359) baseStart_5398359 baseEnd_5398359 := by
    simpa [prefixWord, tailWord_5398359, baseEnd_5398359] using wordTrace_append hprefix tailTrace_5398359
  have hstable : (prefixWord ++ tailWord_5398359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398359).length < 2 ^ (prefixWord ++ tailWord_5398359).sum := by decide
  have hdescent : baseEnd_5398359 < baseStart_5398359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398375 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_5398375 : Nat := 118140960795 + 5398375 * 2 ^ 59
def prefixEnd_5398375 : Nat := 4983230072969 + 3 ^ 40 * 5398375 * 2
def baseEnd_5398375 : Nat := 2771961128215421566685831

theorem tailTrace_5398375 : CollatzResearch.WordTrace tailWord_5398375 prefixEnd_5398375 2771961128215421566685831 := by
  unfold tailWord_5398375
  simp only [CollatzResearch.WordTrace]
  refine ⟨196894911817616818893404579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131263274545077879262269719 196894911817616818893404579)
  ·
    refine ⟨295342367726425228340106869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196894911817616818893404579 295342367726425228340106869)
    ·
      refine ⟨27688346974352365156885019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 295342367726425228340106869 27688346974352365156885019)
      ·
        refine ⟨41532520461528547735327529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27688346974352365156885019 41532520461528547735327529)
        ·
          refine ⟨31149390346146410801495647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41532520461528547735327529 31149390346146410801495647)
          ·
            refine ⟨46724085519219616202243471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31149390346146410801495647 46724085519219616202243471)
            ·
              refine ⟨70086128278829424303365207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46724085519219616202243471 70086128278829424303365207)
              ·
                refine ⟨105129192418244136455047811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70086128278829424303365207 105129192418244136455047811)
                ·
                  refine ⟨157693788627366204682571717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105129192418244136455047811 157693788627366204682571717)
                  ·
                    refine ⟨29567585367631163377982197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 157693788627366204682571717 29567585367631163377982197)
                    ·
                      refine ⟨2771961128215421566685831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29567585367631163377982197 2771961128215421566685831)
                      ·
                        rfl

theorem cell23_5398375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_5398375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398375 prefixEnd_5398375 := by exact prefixLift 5398375
  have htrace : WordTrace (prefixWord ++ tailWord_5398375) baseStart_5398375 baseEnd_5398375 := by
    simpa [prefixWord, tailWord_5398375, baseEnd_5398375] using wordTrace_append hprefix tailTrace_5398375
  have hstable : (prefixWord ++ tailWord_5398375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398375).length < 2 ^ (prefixWord ++ tailWord_5398375).sum := by decide
  have hdescent : baseEnd_5398375 < baseStart_5398375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398405 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 1, 3, 5]
def baseStart_5398405 : Nat := 118140960795 + 5398405 * 2 ^ 59
def prefixEnd_5398405 : Nat := 4983230072969 + 3 ^ 40 * 5398405 * 2
def baseEnd_5398405 : Nat := 2771976532635056449310693

theorem tailTrace_5398405 : CollatzResearch.WordTrace tailWord_5398405 prefixEnd_5398405 2771976532635056449310693 := by
  unfold tailWord_5398405
  simp only [CollatzResearch.WordTrace]
  refine ⟨196896006007508134016996669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131264004005005422677997779 196896006007508134016996669)
  ·
    refine ⟨73836002252815550256373751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196896006007508134016996669 73836002252815550256373751)
    ·
      refine ⟨110754003379223325384560627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73836002252815550256373751 110754003379223325384560627)
      ·
        refine ⟨166131005068834988076840941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110754003379223325384560627 166131005068834988076840941)
        ·
          refine ⟨62299126900813120528815353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166131005068834988076840941 62299126900813120528815353)
          ·
            refine ⟨46724345175609840396611515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62299126900813120528815353 46724345175609840396611515)
            ·
              refine ⟨70086517763414760594917273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46724345175609840396611515 70086517763414760594917273)
              ·
                refine ⟨52564888322561070446187955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70086517763414760594917273 52564888322561070446187955)
                ·
                  refine ⟨78847332483841605669281933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52564888322561070446187955 78847332483841605669281933)
                  ·
                    refine ⟨29567749681440602125980725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78847332483841605669281933 29567749681440602125980725)
                    ·
                      refine ⟨2771976532635056449310693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29567749681440602125980725 2771976532635056449310693)
                      ·
                        rfl

theorem cell23_5398405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_5398405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398405 prefixEnd_5398405 := by exact prefixLift 5398405
  have htrace : WordTrace (prefixWord ++ tailWord_5398405) baseStart_5398405 baseEnd_5398405 := by
    simpa [prefixWord, tailWord_5398405, baseEnd_5398405] using wordTrace_append hprefix tailTrace_5398405
  have hstable : (prefixWord ++ tailWord_5398405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398405).length < 2 ^ (prefixWord ++ tailWord_5398405).sum := by decide
  have hdescent : baseEnd_5398405 < baseStart_5398405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398415 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 4]
def baseStart_5398415 : Nat := 118140960795 + 5398415 * 2 ^ 59
def prefixEnd_5398415 : Nat := 4983230072969 + 3 ^ 40 * 5398415 * 2
def baseEnd_5398415 : Nat := 2771981667441601410185647

theorem tailTrace_5398415 : CollatzResearch.WordTrace tailWord_5398415 prefixEnd_5398415 2771981667441601410185647 := by
  unfold tailWord_5398415
  simp only [CollatzResearch.WordTrace]
  refine ⟨196896370737471905724860699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131264247158314603816573799 196896370737471905724860699)
  ·
    refine ⟨295344556106207858587291049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196896370737471905724860699 295344556106207858587291049)
    ·
      refine ⟨221508417079655893940468287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295344556106207858587291049 221508417079655893940468287)
      ·
        refine ⟨332262625619483840910702431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221508417079655893940468287 332262625619483840910702431)
        ·
          refine ⟨498393938429225761366053647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332262625619483840910702431 498393938429225761366053647)
          ·
            refine ⟨747590907643838642049080471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498393938429225761366053647 747590907643838642049080471)
            ·
              refine ⟨1121386361465757963073620707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747590907643838642049080471 1121386361465757963073620707)
              ·
                refine ⟨1682079542198636944610431061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1121386361465757963073620707 1682079542198636944610431061)
                ·
                  refine ⟨19711869635140276694653489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1682079542198636944610431061 19711869635140276694653489)
                  ·
                    refine ⟨14783902226355207520990117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19711869635140276694653489 14783902226355207520990117)
                    ·
                      refine ⟨2771981667441601410185647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14783902226355207520990117 2771981667441601410185647)
                      ·
                        rfl

theorem cell23_5398415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_5398415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398415 prefixEnd_5398415 := by exact prefixLift 5398415
  have htrace : WordTrace (prefixWord ++ tailWord_5398415) baseStart_5398415 baseEnd_5398415 := by
    simpa [prefixWord, tailWord_5398415, baseEnd_5398415] using wordTrace_append hprefix tailTrace_5398415
  have hstable : (prefixWord ++ tailWord_5398415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398415).length < 2 ^ (prefixWord ++ tailWord_5398415).sum := by decide
  have hdescent : baseEnd_5398415 < baseStart_5398415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398425 : List Nat := [1, 2, 1, 2, 1, 3, 2, 4, 7]
def baseStart_5398425 : Nat := 118140960795 + 5398425 * 2 ^ 59
def prefixEnd_5398425 : Nat := 4983230072969 + 3 ^ 40 * 5398425 * 2
def baseEnd_5398425 : Nat := 307998533583127374562289

theorem tailTrace_5398425 : CollatzResearch.WordTrace tailWord_5398425 prefixEnd_5398425 307998533583127374562289 := by
  unfold tailWord_5398425
  simp only [CollatzResearch.WordTrace]
  refine ⟨196896735467435677432724729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131264490311623784955149819 196896735467435677432724729)
  ·
    refine ⟨147672551600576758074543547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196896735467435677432724729 147672551600576758074543547)
    ·
      refine ⟨221508827400865137111815321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147672551600576758074543547 221508827400865137111815321)
      ·
        refine ⟨166131620550648852833861491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221508827400865137111815321 166131620550648852833861491)
        ·
          refine ⟨249197430825973279250792237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166131620550648852833861491 249197430825973279250792237)
          ·
            refine ⟨93449036559739979719047089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249197430825973279250792237 93449036559739979719047089)
            ·
              refine ⟨70086777419804984789285317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93449036559739979719047089 70086777419804984789285317)
              ·
                refine ⟨13141270766213434647990997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70086777419804984789285317 13141270766213434647990997)
                ·
                  refine ⟨307998533583127374562289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13141270766213434647990997 307998533583127374562289)
                  ·
                    rfl

theorem cell23_5398425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 7].length) (baseStart_5398425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398425 prefixEnd_5398425 := by exact prefixLift 5398425
  have htrace : WordTrace (prefixWord ++ tailWord_5398425) baseStart_5398425 baseEnd_5398425 := by
    simpa [prefixWord, tailWord_5398425, baseEnd_5398425] using wordTrace_append hprefix tailTrace_5398425
  have hstable : (prefixWord ++ tailWord_5398425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398425).length < 2 ^ (prefixWord ++ tailWord_5398425).sum := by decide
  have hdescent : baseEnd_5398425 < baseStart_5398425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398453 : List Nat := [1, 3, 3, 2, 1, 3, 2, 2, 2, 2, 2]
def baseStart_5398453 : Nat := 118140960795 + 5398453 * 2 ^ 59
def prefixEnd_5398453 : Nat := 4983230072969 + 3 ^ 40 * 5398453 * 2
def baseEnd_5398453 : Nat := 2772001179706472261510473

theorem tailTrace_5398453 : CollatzResearch.WordTrace tailWord_5398453 prefixEnd_5398453 2772001179706472261510473 := by
  unfold tailWord_5398453
  simp only [CollatzResearch.WordTrace]
  refine ⟨196897756711334238214744013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131265171140889492143162675 196897756711334238214744013)
  ·
    refine ⟨73836658766750339330529005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196897756711334238214744013 73836658766750339330529005)
    ·
      refine ⟨27688747037531377248948377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73836658766750339330529005 27688747037531377248948377)
      ·
        refine ⟨20766560278148532936711283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27688747037531377248948377 20766560278148532936711283)
        ·
          refine ⟨31149840417222799405066925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20766560278148532936711283 31149840417222799405066925)
          ·
            refine ⟨11681190156458549776900097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31149840417222799405066925 11681190156458549776900097)
            ·
              refine ⟨8760892617343912332675073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11681190156458549776900097 8760892617343912332675073)
              ·
                refine ⟨6570669463007934249506305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8760892617343912332675073 6570669463007934249506305)
                ·
                  refine ⟨4928002097255950687129729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6570669463007934249506305 4928002097255950687129729)
                  ·
                    refine ⟨3696001572941963015347297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4928002097255950687129729 3696001572941963015347297)
                    ·
                      refine ⟨2772001179706472261510473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3696001572941963015347297 2772001179706472261510473)
                      ·
                        rfl

theorem cell23_5398453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_5398453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398453 prefixEnd_5398453 := by exact prefixLift 5398453
  have htrace : WordTrace (prefixWord ++ tailWord_5398453) baseStart_5398453 baseEnd_5398453 := by
    simpa [prefixWord, tailWord_5398453, baseEnd_5398453] using wordTrace_append hprefix tailTrace_5398453
  have hstable : (prefixWord ++ tailWord_5398453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398453).length < 2 ^ (prefixWord ++ tailWord_5398453).sum := by decide
  have hdescent : baseEnd_5398453 < baseStart_5398453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398455 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 3, 7]
def baseStart_5398455 : Nat := 118140960795 + 5398455 * 2 ^ 59
def prefixEnd_5398455 : Nat := 4983230072969 + 3 ^ 40 * 5398455 * 2
def baseEnd_5398455 : Nat := 924000735555927084561821

theorem tailTrace_5398455 : CollatzResearch.WordTrace tailWord_5398455 prefixEnd_5398455 924000735555927084561821 := by
  unfold tailWord_5398455
  simp only [CollatzResearch.WordTrace]
  refine ⟨196897829657326992556316819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131265219771551328370877879 196897829657326992556316819)
  ·
    refine ⟨295346744485990488834475229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196897829657326992556316819 295346744485990488834475229)
    ·
      refine ⟨110755029182246433312928211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295346744485990488834475229 110755029182246433312928211)
      ·
        refine ⟨166132543773369649969392317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110755029182246433312928211 166132543773369649969392317)
        ·
          refine ⟨62299703915013618738522119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166132543773369649969392317 62299703915013618738522119)
          ·
            refine ⟨93449555872520428107783179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62299703915013618738522119 93449555872520428107783179)
            ·
              refine ⟨140174333808780642161674769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93449555872520428107783179 140174333808780642161674769)
              ·
                refine ⟨105130750356585481621256077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140174333808780642161674769 105130750356585481621256077)
                ·
                  refine ⟨39424031383719555607971029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105130750356585481621256077 39424031383719555607971029)
                  ·
                    refine ⟨924000735555927084561821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39424031383719555607971029 924000735555927084561821)
                    ·
                      rfl

theorem cell23_5398455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_5398455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398455 prefixEnd_5398455 := by exact prefixLift 5398455
  have htrace : WordTrace (prefixWord ++ tailWord_5398455) baseStart_5398455 baseEnd_5398455 := by
    simpa [prefixWord, tailWord_5398455, baseEnd_5398455] using wordTrace_append hprefix tailTrace_5398455
  have hstable : (prefixWord ++ tailWord_5398455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398455).length < 2 ^ (prefixWord ++ tailWord_5398455).sum := by decide
  have hdescent : baseEnd_5398455 < baseStart_5398455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398570 : List Nat := [3, 1, 4, 1, 2, 2, 3, 2, 1, 4]
def baseStart_5398570 : Nat := 118140960795 + 5398570 * 2 ^ 59
def prefixEnd_5398570 : Nat := 4983230072969 + 3 ^ 40 * 5398570 * 2
def baseEnd_5398570 : Nat := 924020418981016101249145

theorem tailTrace_5398570 : CollatzResearch.WordTrace tailWord_5398570 prefixEnd_5398570 924020418981016101249145 := by
  unfold tailWord_5398570
  simp only [CollatzResearch.WordTrace]
  refine ⟨49225506012977591799188291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131268016034606911464502109 49225506012977591799188291)
  ·
    refine ⟨73838259019466387698782437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49225506012977591799188291 73838259019466387698782437)
    ·
      refine ⟨13844673566149947693521707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73838259019466387698782437 13844673566149947693521707)
      ·
        refine ⟨20767010349224921540282561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13844673566149947693521707 20767010349224921540282561)
        ·
          refine ⟨15575257761918691155211921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20767010349224921540282561 15575257761918691155211921)
          ·
            refine ⟨11681443321439018366408941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15575257761918691155211921 11681443321439018366408941)
            ·
              refine ⟨4380541245539631887403353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11681443321439018366408941 4380541245539631887403353)
              ·
                refine ⟨3285405934154723915552515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4380541245539631887403353 3285405934154723915552515)
                ·
                  refine ⟨4928108901232085873328773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3285405934154723915552515 4928108901232085873328773)
                  ·
                    refine ⟨924020418981016101249145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4928108901232085873328773 924020418981016101249145)
                    ·
                      rfl

theorem cell23_5398570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_5398570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398570 prefixEnd_5398570 := by exact prefixLift 5398570
  have htrace : WordTrace (prefixWord ++ tailWord_5398570) baseStart_5398570 baseEnd_5398570 := by
    simpa [prefixWord, tailWord_5398570, baseEnd_5398570] using wordTrace_append hprefix tailTrace_5398570
  have hstable : (prefixWord ++ tailWord_5398570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398570).length < 2 ^ (prefixWord ++ tailWord_5398570).sum := by decide
  have hdescent : baseEnd_5398570 < baseStart_5398570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398576 : List Nat := [2, 1, 1, 1, 2, 5, 3, 1, 3, 1, 3]
def baseStart_5398576 : Nat := 118140960795 + 5398576 * 2 ^ 59
def prefixEnd_5398576 : Nat := 4983230072969 + 3 ^ 40 * 5398576 * 2
def baseEnd_5398576 : Nat := 2772064337826975280272407

theorem tailTrace_5398576 : CollatzResearch.WordTrace tailWord_5398576 prefixEnd_5398576 2772064337826975280272407 := by
  unfold tailWord_5398576
  simp only [CollatzResearch.WordTrace]
  refine ⟨98451121444944315110735791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131268161926592420147647721 98451121444944315110735791)
  ·
    refine ⟨147676682167416472666103687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98451121444944315110735791 147676682167416472666103687)
    ·
      refine ⟨221515023251124708999155531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147676682167416472666103687 221515023251124708999155531)
      ·
        refine ⟨332272534876687063498733297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221515023251124708999155531 332272534876687063498733297)
        ·
          refine ⟨249204401157515297624049973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332272534876687063498733297 249204401157515297624049973)
          ·
            refine ⟨23362912608517059152254685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 249204401157515297624049973 23362912608517059152254685)
            ·
              refine ⟨8761092228193897182095507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23362912608517059152254685 8761092228193897182095507)
              ·
                refine ⟨13141638342290845773143261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8761092228193897182095507 13141638342290845773143261)
                ·
                  refine ⟨4928114378359067164928723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13141638342290845773143261 4928114378359067164928723)
                  ·
                    refine ⟨7392171567538600747393085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4928114378359067164928723 7392171567538600747393085)
                    ·
                      refine ⟨2772064337826975280272407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7392171567538600747393085 2772064337826975280272407)
                      ·
                        rfl

theorem cell23_5398576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 3, 1, 3].length) (baseStart_5398576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398576 prefixEnd_5398576 := by exact prefixLift 5398576
  have htrace : WordTrace (prefixWord ++ tailWord_5398576) baseStart_5398576 baseEnd_5398576 := by
    simpa [prefixWord, tailWord_5398576, baseEnd_5398576] using wordTrace_append hprefix tailTrace_5398576
  have hstable : (prefixWord ++ tailWord_5398576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398576).length < 2 ^ (prefixWord ++ tailWord_5398576).sum := by decide
  have hdescent : baseEnd_5398576 < baseStart_5398576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398599 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_5398599 : Nat := 118140960795 + 5398599 * 2 ^ 59
def prefixEnd_5398599 : Nat := 4983230072969 + 3 ^ 40 * 5398599 * 2
def baseEnd_5398599 : Nat := 2772076147882028690284801

theorem tailTrace_5398599 : CollatzResearch.WordTrace tailWord_5398599 prefixEnd_5398599 2772076147882028690284801 := by
  unfold tailWord_5398599
  simp only [CollatzResearch.WordTrace]
  refine ⟨196903081768805305149558851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131268721179203536766372567 196903081768805305149558851)
  ·
    refine ⟨295354622653207957724338277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196903081768805305149558851 295354622653207957724338277)
    ·
      refine ⟨55378991747476492073313427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 295354622653207957724338277 55378991747476492073313427)
      ·
        refine ⟨83068487621214738109970141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55378991747476492073313427 83068487621214738109970141)
        ·
          refine ⟨31150682857955526791238803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83068487621214738109970141 31150682857955526791238803)
          ·
            refine ⟨46726024286933290186858205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31150682857955526791238803 46726024286933290186858205)
            ·
              refine ⟨17522259107599983820071827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46726024286933290186858205 17522259107599983820071827)
              ·
                refine ⟨26283388661399975730107741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17522259107599983820071827 26283388661399975730107741)
                ·
                  refine ⟨9856270748024990898790403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26283388661399975730107741 9856270748024990898790403)
                  ·
                    refine ⟨14784406122037486348185605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9856270748024990898790403 14784406122037486348185605)
                    ·
                      refine ⟨2772076147882028690284801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14784406122037486348185605 2772076147882028690284801)
                      ·
                        rfl

theorem cell23_5398599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_5398599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398599 prefixEnd_5398599 := by exact prefixLift 5398599
  have htrace : WordTrace (prefixWord ++ tailWord_5398599) baseStart_5398599 baseEnd_5398599 := by
    simpa [prefixWord, tailWord_5398599, baseEnd_5398599] using wordTrace_append hprefix tailTrace_5398599
  have hstable : (prefixWord ++ tailWord_5398599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398599).length < 2 ^ (prefixWord ++ tailWord_5398599).sum := by decide
  have hdescent : baseEnd_5398599 < baseStart_5398599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398639 : List Nat := [1, 1, 2, 1, 3, 6, 1, 8]
def baseStart_5398639 : Nat := 118140960795 + 5398639 * 2 ^ 59
def prefixEnd_5398639 : Nat := 4983230072969 + 3 ^ 40 * 5398639 * 2
def baseEnd_5398639 : Nat := 102670247670674390140171

theorem tailTrace_5398639 : CollatzResearch.WordTrace tailWord_5398639 prefixEnd_5398639 102670247670674390140171 := by
  unfold tailWord_5398639
  simp only [CollatzResearch.WordTrace]
  refine ⟨196904540688660391981014971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131269693792440261320676647 196904540688660391981014971)
  ·
    refine ⟨295356811032990587971522457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196904540688660391981014971 295356811032990587971522457)
    ·
      refine ⟨221517608274742940978641843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295356811032990587971522457 221517608274742940978641843)
      ·
        refine ⟨332276412412114411467962765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221517608274742940978641843 332276412412114411467962765)
        ·
          refine ⟨124603654654542904300486037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332276412412114411467962765 124603654654542904300486037)
          ·
            refine ⟨5840796311931698639085283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 124603654654542904300486037 5840796311931698639085283)
            ·
              refine ⟨8761194467897547958627925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5840796311931698639085283 8761194467897547958627925)
              ·
                refine ⟨102670247670674390140171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8761194467897547958627925 102670247670674390140171)
                ·
                  rfl

theorem cell23_5398639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 8].length) (baseStart_5398639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398639 prefixEnd_5398639 := by exact prefixLift 5398639
  have htrace : WordTrace (prefixWord ++ tailWord_5398639) baseStart_5398639 baseEnd_5398639 := by
    simpa [prefixWord, tailWord_5398639, baseEnd_5398639] using wordTrace_append hprefix tailTrace_5398639
  have hstable : (prefixWord ++ tailWord_5398639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398639).length < 2 ^ (prefixWord ++ tailWord_5398639).sum := by decide
  have hdescent : baseEnd_5398639 < baseStart_5398639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398646 : List Nat := [5, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_5398646 : Nat := 118140960795 + 5398646 * 2 ^ 59
def prefixEnd_5398646 : Nat := 4983230072969 + 3 ^ 40 * 5398646 * 2
def baseEnd_5398646 : Nat := 2772100281472790006397085

theorem tailTrace_5398646 : CollatzResearch.WordTrace tailWord_5398646 prefixEnd_5398646 2772100281472790006397085 := by
  unfold tailWord_5398646
  simp only [CollatzResearch.WordTrace]
  refine ⟨12306549749977189511032487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131269863999756688117679861 12306549749977189511032487)
  ·
    refine ⟨18459824624965784266548731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12306549749977189511032487 18459824624965784266548731)
    ·
      refine ⟨27689736937448676399823097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18459824624965784266548731 27689736937448676399823097)
      ·
        refine ⟨20767302703086507299867323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27689736937448676399823097 20767302703086507299867323)
        ·
          refine ⟨31150954054629760949800985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20767302703086507299867323 31150954054629760949800985)
          ·
            refine ⟨23363215540972320712350739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31150954054629760949800985 23363215540972320712350739)
            ·
              refine ⟨35044823311458481068526109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23363215540972320712350739 35044823311458481068526109)
              ·
                refine ⟨13141808741796930400697291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35044823311458481068526109 13141808741796930400697291)
                ·
                  refine ⟨19712713112695395601045937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13141808741796930400697291 19712713112695395601045937)
                  ·
                    refine ⟨14784534834521546700784453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19712713112695395601045937 14784534834521546700784453)
                    ·
                      refine ⟨2772100281472790006397085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14784534834521546700784453 2772100281472790006397085)
                      ·
                        rfl

theorem cell23_5398646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_5398646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398646 prefixEnd_5398646 := by exact prefixLift 5398646
  have htrace : WordTrace (prefixWord ++ tailWord_5398646) baseStart_5398646 baseEnd_5398646 := by
    simpa [prefixWord, tailWord_5398646, baseEnd_5398646] using wordTrace_append hprefix tailTrace_5398646
  have hstable : (prefixWord ++ tailWord_5398646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398646).length < 2 ^ (prefixWord ++ tailWord_5398646).sum := by decide
  have hdescent : baseEnd_5398646 < baseStart_5398646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398666 : List Nat := [3, 1, 2, 3, 1, 2, 2, 2, 1, 3, 3]
def baseStart_5398666 : Nat := 118140960795 + 5398666 * 2 ^ 59
def prefixEnd_5398666 : Nat := 4983230072969 + 3 ^ 40 * 5398666 * 2
def baseEnd_5398666 : Nat := 2772110551085879928146993

theorem tailTrace_5398666 : CollatzResearch.WordTrace tailWord_5398666 prefixEnd_5398666 2772110551085879928146993 := by
  unfold tailWord_5398666
  simp only [CollatzResearch.WordTrace]
  refine ⟨49226381364890643898061963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131270350306375050394831901 49226381364890643898061963)
  ·
    refine ⟨73839572047335965847092945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49226381364890643898061963 73839572047335965847092945)
    ·
      refine ⟨55379679035501974385319709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73839572047335965847092945 55379679035501974385319709)
      ·
        refine ⟨20767379638313240394494891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55379679035501974385319709 20767379638313240394494891)
        ·
          refine ⟨31151069457469860591742337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20767379638313240394494891 31151069457469860591742337)
          ·
            refine ⟨23363302093102395443806753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31151069457469860591742337 23363302093102395443806753)
            ·
              refine ⟨17522476569826796582855065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23363302093102395443806753 17522476569826796582855065)
              ·
                refine ⟨13141857427370097437141299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17522476569826796582855065 13141857427370097437141299)
                ·
                  refine ⟨19712786141055146155711949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13141857427370097437141299 19712786141055146155711949)
                  ·
                    refine ⟨7392294802895679808391981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19712786141055146155711949 7392294802895679808391981)
                    ·
                      refine ⟨2772110551085879928146993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7392294802895679808391981 2772110551085879928146993)
                      ·
                        rfl

theorem cell23_5398666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_5398666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398666 prefixEnd_5398666 := by exact prefixLift 5398666
  have htrace : WordTrace (prefixWord ++ tailWord_5398666) baseStart_5398666 baseEnd_5398666 := by
    simpa [prefixWord, tailWord_5398666, baseEnd_5398666] using wordTrace_append hprefix tailTrace_5398666
  have hstable : (prefixWord ++ tailWord_5398666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398666).length < 2 ^ (prefixWord ++ tailWord_5398666).sum := by decide
  have hdescent : baseEnd_5398666 < baseStart_5398666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398746 : List Nat := [3, 1, 1, 2, 2, 1, 2, 6, 5]
def baseStart_5398746 : Nat := 118140960795 + 5398746 * 2 ^ 59
def prefixEnd_5398746 : Nat := 4983230072969 + 3 ^ 40 * 5398746 * 2
def baseEnd_5398746 : Nat := 308016847726471068349625

theorem tailTrace_5398746 : CollatzResearch.WordTrace tailWord_5398746 prefixEnd_5398746 308016847726471068349625 := by
  unfold tailWord_5398746
  simp only [CollatzResearch.WordTrace]
  refine ⟨49227110824818187313790023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131272295532848499503440061 49227110824818187313790023)
  ·
    refine ⟨73840666237227280970685035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49227110824818187313790023 73840666237227280970685035)
    ·
      refine ⟨110760999355840921456027553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73840666237227280970685035 110760999355840921456027553)
      ·
        refine ⟨83070749516880691092020665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110760999355840921456027553 83070749516880691092020665)
        ·
          refine ⟨62303062137660518319015499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83070749516880691092020665 62303062137660518319015499)
          ·
            refine ⟨93454593206490777478523249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62303062137660518319015499 93454593206490777478523249)
            ·
              refine ⟨70090944904868083108892437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93454593206490777478523249 70090944904868083108892437)
              ·
                refine ⟨3285513042415691395729333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70090944904868083108892437 3285513042415691395729333)
                ·
                  refine ⟨308016847726471068349625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3285513042415691395729333 308016847726471068349625)
                  ·
                    rfl

theorem cell23_5398746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 5].length) (baseStart_5398746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398746 prefixEnd_5398746 := by exact prefixLift 5398746
  have htrace : WordTrace (prefixWord ++ tailWord_5398746) baseStart_5398746 baseEnd_5398746 := by
    simpa [prefixWord, tailWord_5398746, baseEnd_5398746] using wordTrace_append hprefix tailTrace_5398746
  have hstable : (prefixWord ++ tailWord_5398746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398746).length < 2 ^ (prefixWord ++ tailWord_5398746).sum := by decide
  have hdescent : baseEnd_5398746 < baseStart_5398746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398757 : List Nat := [1, 3, 1, 4, 2, 1, 4, 1, 2, 2, 2]
def baseStart_5398757 : Nat := 118140960795 + 5398757 * 2 ^ 59
def prefixEnd_5398757 : Nat := 4983230072969 + 3 ^ 40 * 5398757 * 2
def baseEnd_5398757 : Nat := 2772157277825439072109075

theorem tailTrace_5398757 : CollatzResearch.WordTrace tailWord_5398757 prefixEnd_5398757 2772157277825439072109075 := by
  unfold tailWord_5398757
  simp only [CollatzResearch.WordTrace]
  refine ⟨196908844502232898133810525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131272563001488598755873683 196908844502232898133810525)
  ·
    refine ⟨73840816688337336800178947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196908844502232898133810525 73840816688337336800178947)
    ·
      refine ⟨110761225032506005200268421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73840816688337336800178947 110761225032506005200268421)
      ·
        refine ⟨20767729693594875975050329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110761225032506005200268421 20767729693594875975050329)
        ·
          refine ⟨15575797270196156981287747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20767729693594875975050329 15575797270196156981287747)
          ·
            refine ⟨23363695905294235471931621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15575797270196156981287747 23363695905294235471931621)
            ·
              refine ⟨4380692982242669150987179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23363695905294235471931621 4380692982242669150987179)
              ·
                refine ⟨6571039473364003726480769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4380692982242669150987179 6571039473364003726480769)
                ·
                  refine ⟨4928279605023002794860577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6571039473364003726480769 4928279605023002794860577)
                  ·
                    refine ⟨3696209703767252096145433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4928279605023002794860577 3696209703767252096145433)
                    ·
                      refine ⟨2772157277825439072109075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3696209703767252096145433 2772157277825439072109075)
                      ·
                        rfl

theorem cell23_5398757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_5398757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398757 prefixEnd_5398757 := by exact prefixLift 5398757
  have htrace : WordTrace (prefixWord ++ tailWord_5398757) baseStart_5398757 baseEnd_5398757 := by
    simpa [prefixWord, tailWord_5398757, baseEnd_5398757] using wordTrace_append hprefix tailTrace_5398757
  have hstable : (prefixWord ++ tailWord_5398757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398757).length < 2 ^ (prefixWord ++ tailWord_5398757).sum := by decide
  have hdescent : baseEnd_5398757 < baseStart_5398757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398796 : List Nat := [2, 2, 1, 2, 2, 2, 1, 4, 2, 1, 4]
def baseStart_5398796 : Nat := 118140960795 + 5398796 * 2 ^ 59
def prefixEnd_5398796 : Nat := 4983230072969 + 3 ^ 40 * 5398796 * 2
def baseEnd_5398796 : Nat := 2772177303570964419521395

theorem tailTrace_5398796 : CollatzResearch.WordTrace tailWord_5398796 prefixEnd_5398796 2772177303570964419521395 := by
  unfold tailWord_5398796
  simp only [CollatzResearch.WordTrace]
  refine ⟨98455133474545803897240121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131273511299394405196320161 98455133474545803897240121)
  ·
    refine ⟨73841350105909352922930091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98455133474545803897240121 73841350105909352922930091)
    ·
      refine ⟨110762025158864029384395137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73841350105909352922930091 110762025158864029384395137)
      ·
        refine ⟨83071518869148022038296353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110762025158864029384395137 83071518869148022038296353)
        ·
          refine ⟨62303639151861016528722265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83071518869148022038296353 62303639151861016528722265)
          ·
            refine ⟨46727729363895762396541699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62303639151861016528722265 46727729363895762396541699)
            ·
              refine ⟨70091594045843643594812549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46727729363895762396541699 70091594045843643594812549)
              ·
                refine ⟨13142173883595683174027353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70091594045843643594812549 13142173883595683174027353)
                ·
                  refine ⟨9856630412696762380520515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13142173883595683174027353 9856630412696762380520515)
                  ·
                    refine ⟨14784945619045143570780773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9856630412696762380520515 14784945619045143570780773)
                    ·
                      refine ⟨2772177303570964419521395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14784945619045143570780773 2772177303570964419521395)
                      ·
                        rfl

theorem cell23_5398796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_5398796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398796 prefixEnd_5398796 := by exact prefixLift 5398796
  have htrace : WordTrace (prefixWord ++ tailWord_5398796) baseStart_5398796 baseEnd_5398796 := by
    simpa [prefixWord, tailWord_5398796, baseEnd_5398796] using wordTrace_append hprefix tailTrace_5398796
  have hstable : (prefixWord ++ tailWord_5398796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398796).length < 2 ^ (prefixWord ++ tailWord_5398796).sum := by decide
  have hdescent : baseEnd_5398796 < baseStart_5398796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398830 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_5398830 : Nat := 118140960795 + 5398830 * 2 ^ 59
def prefixEnd_5398830 : Nat := 4983230072969 + 3 ^ 40 * 5398830 * 2
def baseEnd_5398830 : Nat := 2772194761913217286496239

theorem tailTrace_5398830 : CollatzResearch.WordTrace tailWord_5398830 prefixEnd_5398830 2772194761913217286496239 := by
  unfold tailWord_5398830
  simp only [CollatzResearch.WordTrace]
  refine ⟨24613938378871053950152243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131274338020645621067478629 24613938378871053950152243)
  ·
    refine ⟨36920907568306580925228365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24613938378871053950152243 36920907568306580925228365)
    ·
      refine ⟨13845340338114967846960637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36920907568306580925228365 13845340338114967846960637)
      ·
        refine ⟨5192002626793112942610239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13845340338114967846960637 5192002626793112942610239)
        ·
          refine ⟨7788003940189669413915359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5192002626793112942610239 7788003940189669413915359)
          ·
            refine ⟨11682005910284504120873039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7788003940189669413915359 11682005910284504120873039)
            ·
              refine ⟨17523008865426756181309559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11682005910284504120873039 17523008865426756181309559)
              ·
                refine ⟨26284513298140134271964339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17523008865426756181309559 26284513298140134271964339)
                ·
                  refine ⟨39426769947210201407946509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26284513298140134271964339 39426769947210201407946509)
                  ·
                    refine ⟨14785038730203825527979941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39426769947210201407946509 14785038730203825527979941)
                    ·
                      refine ⟨2772194761913217286496239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14785038730203825527979941 2772194761913217286496239)
                      ·
                        rfl

theorem cell23_5398830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_5398830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398830 prefixEnd_5398830 := by exact prefixLift 5398830
  have htrace : WordTrace (prefixWord ++ tailWord_5398830) baseStart_5398830 baseEnd_5398830 := by
    simpa [prefixWord, tailWord_5398830, baseEnd_5398830] using wordTrace_append hprefix tailTrace_5398830
  have hstable : (prefixWord ++ tailWord_5398830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398830).length < 2 ^ (prefixWord ++ tailWord_5398830).sum := by decide
  have hdescent : baseEnd_5398830 < baseStart_5398830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398833 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 1, 4, 3]
def baseStart_5398833 : Nat := 118140960795 + 5398833 * 2 ^ 59
def prefixEnd_5398833 : Nat := 4983230072969 + 3 ^ 40 * 5398833 * 2
def baseEnd_5398833 : Nat := 2772196302355180774758725

theorem tailTrace_5398833 : CollatzResearch.WordTrace tailWord_5398833 prefixEnd_5398833 2772196302355180774758725 := by
  unfold tailWord_5398833
  simp only [CollatzResearch.WordTrace]
  refine ⟨196911616449957563113577153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131274410966638375409051435 196911616449957563113577153)
  ·
    refine ⟨147683712337468172335182865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196911616449957563113577153 147683712337468172335182865)
    ·
      refine ⟨110762784253101129251387149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147683712337468172335182865 110762784253101129251387149)
      ·
        refine ⟨41536044094912923469270181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110762784253101129251387149 41536044094912923469270181)
        ·
          refine ⟨7788008267796173150488159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41536044094912923469270181 7788008267796173150488159)
          ·
            refine ⟨11682012401694259725732239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7788008267796173150488159 11682012401694259725732239)
            ·
              refine ⟨17523018602541389588598359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11682012401694259725732239 17523018602541389588598359)
              ·
                refine ⟨26284527903812084382897539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17523018602541389588598359 26284527903812084382897539)
                ·
                  refine ⟨39426791855718126574346309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26284527903812084382897539 39426791855718126574346309)
                  ·
                    refine ⟨7392523472947148732689933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39426791855718126574346309 7392523472947148732689933)
                    ·
                      refine ⟨2772196302355180774758725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7392523472947148732689933 2772196302355180774758725)
                      ·
                        rfl

theorem cell23_5398833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_5398833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398833 prefixEnd_5398833 := by exact prefixLift 5398833
  have htrace : WordTrace (prefixWord ++ tailWord_5398833) baseStart_5398833 baseEnd_5398833 := by
    simpa [prefixWord, tailWord_5398833, baseEnd_5398833] using wordTrace_append hprefix tailTrace_5398833
  have hstable : (prefixWord ++ tailWord_5398833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398833).length < 2 ^ (prefixWord ++ tailWord_5398833).sum := by decide
  have hdescent : baseEnd_5398833 < baseStart_5398833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398839 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 6]
def baseStart_5398839 : Nat := 118140960795 + 5398839 * 2 ^ 59
def prefixEnd_5398839 : Nat := 4983230072969 + 3 ^ 40 * 5398839 * 2
def baseEnd_5398839 : Nat := 2772199383239107751283697

theorem tailTrace_5398839 : CollatzResearch.WordTrace tailWord_5398839 prefixEnd_5398839 2772199383239107751283697 := by
  unfold tailWord_5398839
  simp only [CollatzResearch.WordTrace]
  refine ⟨196911835287935826138295571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131274556858623884092197047 196911835287935826138295571)
  ·
    refine ⟨295367752931903739207443357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196911835287935826138295571 295367752931903739207443357)
    ·
      refine ⟨110762907349463902202791259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295367752931903739207443357 110762907349463902202791259)
      ·
        refine ⟨166144361024195853304186889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110762907349463902202791259 166144361024195853304186889)
        ·
          refine ⟨124608270768146889978140167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166144361024195853304186889 124608270768146889978140167)
          ·
            refine ⟨186912406152220334967210251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124608270768146889978140167 186912406152220334967210251)
            ·
              refine ⟨280368609228330502450815377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186912406152220334967210251 280368609228330502450815377)
              ·
                refine ⟨210276456921247876838111533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280368609228330502450815377 210276456921247876838111533)
                ·
                  refine ⟨78853671345467953814291825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210276456921247876838111533 78853671345467953814291825)
                  ·
                    refine ⟨59140253509100965360718869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78853671345467953814291825 59140253509100965360718869)
                    ·
                      refine ⟨2772199383239107751283697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59140253509100965360718869 2772199383239107751283697)
                      ·
                        rfl

theorem cell23_5398839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_5398839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398839 prefixEnd_5398839 := by exact prefixLift 5398839
  have htrace : WordTrace (prefixWord ++ tailWord_5398839) baseStart_5398839 baseEnd_5398839 := by
    simpa [prefixWord, tailWord_5398839, baseEnd_5398839] using wordTrace_append hprefix tailTrace_5398839
  have hstable : (prefixWord ++ tailWord_5398839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398839).length < 2 ^ (prefixWord ++ tailWord_5398839).sum := by decide
  have hdescent : baseEnd_5398839 < baseStart_5398839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398859 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 7]
def baseStart_5398859 : Nat := 118140960795 + 5398859 * 2 ^ 59
def prefixEnd_5398859 : Nat := 4983230072969 + 3 ^ 40 * 5398859 * 2
def baseEnd_5398859 : Nat := 2772209652852197673033605

theorem tailTrace_5398859 : CollatzResearch.WordTrace tailWord_5398859 prefixEnd_5398859 2772209652852197673033605 := by
  unfold tailWord_5398859
  simp only [CollatzResearch.WordTrace]
  refine ⟨196912564747863369554023631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131275043165242246369349087 196912564747863369554023631)
  ·
    refine ⟨295368847121795054331035447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196912564747863369554023631 295368847121795054331035447)
    ·
      refine ⟨443053270682692581496553171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295368847121795054331035447 443053270682692581496553171)
      ·
        refine ⟨664579906024038872244829757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443053270682692581496553171 664579906024038872244829757)
        ·
          refine ⟨249217464759014577091811159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 664579906024038872244829757 249217464759014577091811159)
          ·
            refine ⟨373826197138521865637716739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249217464759014577091811159 373826197138521865637716739)
            ·
              refine ⟨560739295707782798456575109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373826197138521865637716739 560739295707782798456575109)
              ·
                refine ⟨105138617945209274710607833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 560739295707782798456575109 105138617945209274710607833)
                ·
                  refine ⟨78853963458906956032955875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105138617945209274710607833 78853963458906956032955875)
                  ·
                    refine ⟨118280945188360434049433813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78853963458906956032955875 118280945188360434049433813)
                    ·
                      refine ⟨2772209652852197673033605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118280945188360434049433813 2772209652852197673033605)
                      ·
                        rfl

theorem cell23_5398859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 7].length) (baseStart_5398859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398859 prefixEnd_5398859 := by exact prefixLift 5398859
  have htrace : WordTrace (prefixWord ++ tailWord_5398859) baseStart_5398859 baseEnd_5398859 := by
    simpa [prefixWord, tailWord_5398859, baseEnd_5398859] using wordTrace_append hprefix tailTrace_5398859
  have hstable : (prefixWord ++ tailWord_5398859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398859).length < 2 ^ (prefixWord ++ tailWord_5398859).sum := by decide
  have hdescent : baseEnd_5398859 < baseStart_5398859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398866 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 5, 5]
def baseStart_5398866 : Nat := 118140960795 + 5398866 * 2 ^ 59
def prefixEnd_5398866 : Nat := 4983230072969 + 3 ^ 40 * 5398866 * 2
def baseEnd_5398866 : Nat := 924071082405593048548691

theorem tailTrace_5398866 : CollatzResearch.WordTrace tailWord_5398866 prefixEnd_5398866 924071082405593048548691 := by
  unfold tailWord_5398866
  simp only [CollatzResearch.WordTrace]
  refine ⟨49228205014709502437382113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131275213372558673166352301 49228205014709502437382113)
  ·
    refine ⟨36921153761032126828036585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49228205014709502437382113 36921153761032126828036585)
    ·
      refine ⟨27690865320774095121027439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36921153761032126828036585 27690865320774095121027439)
      ·
        refine ⟨41536297981161142681541159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27690865320774095121027439 41536297981161142681541159)
        ·
          refine ⟨62304446971741714022311739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41536297981161142681541159 62304446971741714022311739)
          ·
            refine ⟨93456670457612571033467609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62304446971741714022311739 93456670457612571033467609)
            ·
              refine ⟨70092502843209428275100707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93456670457612571033467609 70092502843209428275100707)
              ·
                refine ⟨105138754264814142412651061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70092502843209428275100707 105138754264814142412651061)
                ·
                  refine ⟨9856758212326325851186037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105138754264814142412651061 9856758212326325851186037)
                  ·
                    refine ⟨924071082405593048548691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9856758212326325851186037 924071082405593048548691)
                    ·
                      rfl

theorem cell23_5398866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_5398866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398866 prefixEnd_5398866 := by exact prefixLift 5398866
  have htrace : WordTrace (prefixWord ++ tailWord_5398866) baseStart_5398866 baseEnd_5398866 := by
    simpa [prefixWord, tailWord_5398866, baseEnd_5398866] using wordTrace_append hprefix tailTrace_5398866
  have hstable : (prefixWord ++ tailWord_5398866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398866).length < 2 ^ (prefixWord ++ tailWord_5398866).sum := by decide
  have hdescent : baseEnd_5398866 < baseStart_5398866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398883 : List Nat := [1, 1, 1, 5, 2, 1, 4, 2, 1, 5]
def baseStart_5398883 : Nat := 118140960795 + 5398883 * 2 ^ 59
def prefixEnd_5398883 : Nat := 4983230072969 + 3 ^ 40 * 5398883 * 2
def baseEnd_5398883 : Nat := 924073992129301859711165

theorem tailTrace_5398883 : CollatzResearch.WordTrace tailWord_5398883 prefixEnd_5398883 924073992129301859711165 := by
  unfold tailWord_5398883
  simp only [CollatzResearch.WordTrace]
  refine ⟨196913440099776421652897303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131275626733184281101931535 196913440099776421652897303)
  ·
    refine ⟨295370160149664632479345955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196913440099776421652897303 295370160149664632479345955)
    ·
      refine ⟨443055240224496948719018933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295370160149664632479345955 443055240224496948719018933)
      ·
        refine ⟨41536428771046588942408025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 443055240224496948719018933 41536428771046588942408025)
        ·
          refine ⟨31152321578284941706806019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41536428771046588942408025 31152321578284941706806019)
          ·
            refine ⟨46728482367427412560209029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31152321578284941706806019 46728482367427412560209029)
            ·
              refine ⟨8761590443892639855039193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46728482367427412560209029 8761590443892639855039193)
              ·
                refine ⟨6571192832919479891279395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8761590443892639855039193 6571192832919479891279395)
                ·
                  refine ⟨9856789249379219836919093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6571192832919479891279395 9856789249379219836919093)
                  ·
                    refine ⟨924073992129301859711165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9856789249379219836919093 924073992129301859711165)
                    ·
                      rfl

theorem cell23_5398883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 5].length) (baseStart_5398883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398883 prefixEnd_5398883 := by exact prefixLift 5398883
  have htrace : WordTrace (prefixWord ++ tailWord_5398883) baseStart_5398883 baseEnd_5398883 := by
    simpa [prefixWord, tailWord_5398883, baseEnd_5398883] using wordTrace_append hprefix tailTrace_5398883
  have hstable : (prefixWord ++ tailWord_5398883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398883).length < 2 ^ (prefixWord ++ tailWord_5398883).sum := by decide
  have hdescent : baseEnd_5398883 < baseStart_5398883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398890 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 1, 5, 2]
def baseStart_5398890 : Nat := 118140960795 + 5398890 * 2 ^ 59
def prefixEnd_5398890 : Nat := 4983230072969 + 3 ^ 40 * 5398890 * 2
def baseEnd_5398890 : Nat := 2772225570752487051745963

theorem tailTrace_5398890 : CollatzResearch.WordTrace tailWord_5398890 prefixEnd_5398890 2772225570752487051745963 := by
  unfold tailWord_5398890
  simp only [CollatzResearch.WordTrace]
  refine ⟨49228423852687765462100531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131275796940500707898934749 49228423852687765462100531)
  ·
    refine ⟨73842635779031648193150797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49228423852687765462100531 73842635779031648193150797)
    ·
      refine ⟨27690988417136868072431549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73842635779031648193150797 27690988417136868072431549)
      ·
        refine ⟨10384120656426325527161831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27690988417136868072431549 10384120656426325527161831)
        ·
          refine ⟨15576180984639488290742747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10384120656426325527161831 15576180984639488290742747)
          ·
            refine ⟨23364271476959232436114121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15576180984639488290742747 23364271476959232436114121)
            ·
              refine ⟨17523203607719424327085591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23364271476959232436114121 17523203607719424327085591)
              ·
                refine ⟨26284805411579136490628387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17523203607719424327085591 26284805411579136490628387)
                ·
                  refine ⟨39427208117368704735942581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26284805411579136490628387 39427208117368704735942581)
                  ·
                    refine ⟨3696300761003316068994617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39427208117368704735942581 3696300761003316068994617)
                    ·
                      refine ⟨2772225570752487051745963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3696300761003316068994617 2772225570752487051745963)
                      ·
                        rfl

theorem cell23_5398890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_5398890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398890 prefixEnd_5398890 := by exact prefixLift 5398890
  have htrace : WordTrace (prefixWord ++ tailWord_5398890) baseStart_5398890 baseEnd_5398890 := by
    simpa [prefixWord, tailWord_5398890, baseEnd_5398890] using wordTrace_append hprefix tailTrace_5398890
  have hstable : (prefixWord ++ tailWord_5398890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398890).length < 2 ^ (prefixWord ++ tailWord_5398890).sum := by decide
  have hdescent : baseEnd_5398890 < baseStart_5398890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398916 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_5398916 : Nat := 118140960795 + 5398916 * 2 ^ 59
def prefixEnd_5398916 : Nat := 4983230072969 + 3 ^ 40 * 5398916 * 2
def baseEnd_5398916 : Nat := 2772238921249503950020843

theorem tailTrace_5398916 : CollatzResearch.WordTrace tailWord_5398916 prefixEnd_5398916 2772238921249503950020843 := by
  unfold tailWord_5398916
  simp only [CollatzResearch.WordTrace]
  refine ⟨98457321854328434144424301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131276429139104578859232401 98457321854328434144424301)
  ·
    refine ⟨36921495695373162804159113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98457321854328434144424301 36921495695373162804159113)
    ·
      refine ⟨27691121771529872103119335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36921495695373162804159113 27691121771529872103119335)
      ·
        refine ⟨41536682657294808154679003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27691121771529872103119335 41536682657294808154679003)
        ·
          refine ⟨62305023985942212232018505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41536682657294808154679003 62305023985942212232018505)
          ·
            refine ⟨46728767989456659174013879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62305023985942212232018505 46728767989456659174013879)
            ·
              refine ⟨70093151984184988761020819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46728767989456659174013879 70093151984184988761020819)
              ·
                refine ⟨105139727976277483141531229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70093151984184988761020819 105139727976277483141531229)
                ·
                  refine ⟨39427397991104056178074211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105139727976277483141531229 39427397991104056178074211)
                  ·
                    refine ⟨59141096986656084267111317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39427397991104056178074211 59141096986656084267111317)
                    ·
                      refine ⟨2772238921249503950020843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59141096986656084267111317 2772238921249503950020843)
                      ·
                        rfl

theorem cell23_5398916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_5398916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398916 prefixEnd_5398916 := by exact prefixLift 5398916
  have htrace : WordTrace (prefixWord ++ tailWord_5398916) baseStart_5398916 baseEnd_5398916 := by
    simpa [prefixWord, tailWord_5398916, baseEnd_5398916] using wordTrace_append hprefix tailTrace_5398916
  have hstable : (prefixWord ++ tailWord_5398916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398916).length < 2 ^ (prefixWord ++ tailWord_5398916).sum := by decide
  have hdescent : baseEnd_5398916 < baseStart_5398916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398934 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_5398934 : Nat := 118140960795 + 5398934 * 2 ^ 59
def prefixEnd_5398934 : Nat := 4983230072969 + 3 ^ 40 * 5398934 * 2
def baseEnd_5398934 : Nat := 924082721300428293198587

theorem tailTrace_5398934 : CollatzResearch.WordTrace tailWord_5398934 prefixEnd_5398934 924082721300428293198587 := by
  unfold tailWord_5398934
  simp only [CollatzResearch.WordTrace]
  refine ⟨12307206263911978585187741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131276866815061104908669237 12307206263911978585187741)
  ·
    refine ⟨4615202348966991969445403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12307206263911978585187741 4615202348966991969445403)
    ·
      refine ⟨6922803523450487954168105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4615202348966991969445403 6922803523450487954168105)
      ·
        refine ⟨5192102642587865965626079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6922803523450487954168105 5192102642587865965626079)
        ·
          refine ⟨7788153963881798948439119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5192102642587865965626079 7788153963881798948439119)
          ·
            refine ⟨11682230945822698422658679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7788153963881798948439119 11682230945822698422658679)
            ·
              refine ⟨17523346418734047633988019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11682230945822698422658679 17523346418734047633988019)
              ·
                refine ⟨26285019628101071450982029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17523346418734047633988019 26285019628101071450982029)
                ·
                  refine ⟨9856882360537901794118261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26285019628101071450982029 9856882360537901794118261)
                  ·
                    refine ⟨924082721300428293198587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9856882360537901794118261 924082721300428293198587)
                    ·
                      rfl

theorem cell23_5398934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_5398934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398934 prefixEnd_5398934 := by exact prefixLift 5398934
  have htrace : WordTrace (prefixWord ++ tailWord_5398934) baseStart_5398934 baseEnd_5398934 := by
    simpa [prefixWord, tailWord_5398934, baseEnd_5398934] using wordTrace_append hprefix tailTrace_5398934
  have hstable : (prefixWord ++ tailWord_5398934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398934).length < 2 ^ (prefixWord ++ tailWord_5398934).sum := by decide
  have hdescent : baseEnd_5398934 < baseStart_5398934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398953 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 6, 1, 3]
def baseStart_5398953 : Nat := 118140960795 + 5398953 * 2 ^ 59
def prefixEnd_5398953 : Nat := 4983230072969 + 3 ^ 40 * 5398953 * 2
def baseEnd_5398953 : Nat := 2772257920033720305258173

theorem tailTrace_5398953 : CollatzResearch.WordTrace tailWord_5398953 prefixEnd_5398953 2772257920033720305258173 := by
  unfold tailWord_5398953
  simp only [CollatzResearch.WordTrace]
  refine ⟨196915993209522823607945513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131277328806348549071963675 196915993209522823607945513)
  ·
    refine ⟨147686994907142117705959135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196915993209522823607945513 147686994907142117705959135)
    ·
      refine ⟨221530492360713176558938703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147686994907142117705959135 221530492360713176558938703)
      ·
        refine ⟨332295738541069764838408055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221530492360713176558938703 332295738541069764838408055)
        ·
          refine ⟨498443607811604647257612083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332295738541069764838408055 498443607811604647257612083)
          ·
            refine ⟨747665411717406970886418125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498443607811604647257612083 747665411717406970886418125)
            ·
              refine ⟨280374529394027614082406797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 747665411717406970886418125 280374529394027614082406797)
              ·
                refine ⟨105140448522760355280902549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 280374529394027614082406797 105140448522760355280902549)
                ·
                  refine ⟨4928458524504391653792307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105140448522760355280902549 4928458524504391653792307)
                  ·
                    refine ⟨7392687786756587480688461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4928458524504391653792307 7392687786756587480688461)
                    ·
                      refine ⟨2772257920033720305258173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7392687786756587480688461 2772257920033720305258173)
                      ·
                        rfl

theorem cell23_5398953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 1, 3].length) (baseStart_5398953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398953 prefixEnd_5398953 := by exact prefixLift 5398953
  have htrace : WordTrace (prefixWord ++ tailWord_5398953) baseStart_5398953 baseEnd_5398953 := by
    simpa [prefixWord, tailWord_5398953, baseEnd_5398953] using wordTrace_append hprefix tailTrace_5398953
  have hstable : (prefixWord ++ tailWord_5398953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398953).length < 2 ^ (prefixWord ++ tailWord_5398953).sum := by decide
  have hdescent : baseEnd_5398953 < baseStart_5398953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398957 : List Nat := [1, 5, 2, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_5398957 : Nat := 118140960795 + 5398957 * 2 ^ 59
def prefixEnd_5398957 : Nat := 4983230072969 + 3 ^ 40 * 5398957 * 2
def baseEnd_5398957 : Nat := 2772259973956338289608155

theorem tailTrace_5398957 : CollatzResearch.WordTrace tailWord_5398957 prefixEnd_5398957 2772259973956338289608155 := by
  unfold tailWord_5398957
  simp only [CollatzResearch.WordTrace]
  refine ⟨196916139101508332291091125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131277426067672221527394083 196916139101508332291091125)
  ·
    refine ⟨18460888040766406152289793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 196916139101508332291091125 18460888040766406152289793)
    ·
      refine ⟨13845666030574804614217345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18460888040766406152289793 13845666030574804614217345)
      ·
        refine ⟨10384249522931103460663009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13845666030574804614217345 10384249522931103460663009)
        ·
          refine ⟨7788187142198327595497257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10384249522931103460663009 7788187142198327595497257)
          ·
            refine ⟨5841140356648745696622943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7788187142198327595497257 5841140356648745696622943)
            ·
              refine ⟨8761710534973118544934415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5841140356648745696622943 8761710534973118544934415)
              ·
                refine ⟨13142565802459677817401623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8761710534973118544934415 13142565802459677817401623)
                ·
                  refine ⟨19713848703689516726102435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13142565802459677817401623 19713848703689516726102435)
                  ·
                    refine ⟨29570773055534275089153653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19713848703689516726102435 29570773055534275089153653)
                    ·
                      refine ⟨2772259973956338289608155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29570773055534275089153653 2772259973956338289608155)
                      ·
                        rfl

theorem cell23_5398957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_5398957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398957 prefixEnd_5398957 := by exact prefixLift 5398957
  have htrace : WordTrace (prefixWord ++ tailWord_5398957) baseStart_5398957 baseEnd_5398957 := by
    simpa [prefixWord, tailWord_5398957, baseEnd_5398957] using wordTrace_append hprefix tailTrace_5398957
  have hstable : (prefixWord ++ tailWord_5398957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398957).length < 2 ^ (prefixWord ++ tailWord_5398957).sum := by decide
  have hdescent : baseEnd_5398957 < baseStart_5398957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399043 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 3]
def baseStart_5399043 : Nat := 118140960795 + 5399043 * 2 ^ 59
def prefixEnd_5399043 : Nat := 4983230072969 + 3 ^ 40 * 5399043 * 2
def baseEnd_5399043 : Nat := 2772304133292624953132759

theorem tailTrace_5399043 : CollatzResearch.WordTrace tailWord_5399043 prefixEnd_5399043 2772304133292624953132759 := by
  unfold tailWord_5399043
  simp only [CollatzResearch.WordTrace]
  refine ⟨196919275779196768978721783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131279517186131179319147855 196919275779196768978721783)
  ·
    refine ⟨295378913668795153468082675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196919275779196768978721783 295378913668795153468082675)
    ·
      refine ⟨443068370503192730202124013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295378913668795153468082675 443068370503192730202124013)
      ·
        refine ⟨166150638938697273825796505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 443068370503192730202124013 166150638938697273825796505)
        ·
          refine ⟨124612979204022955369347379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166150638938697273825796505 124612979204022955369347379)
          ·
            refine ⟨186919468806034433054021069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124612979204022955369347379 186919468806034433054021069)
            ·
              refine ⟨70094800802262912395257901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186919468806034433054021069 70094800802262912395257901)
              ·
                refine ⟨26285550300848592148221713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70094800802262912395257901 26285550300848592148221713)
                ·
                  refine ⟨19714162725636444111166285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26285550300848592148221713 19714162725636444111166285)
                  ·
                    refine ⟨7392811022113666541687357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19714162725636444111166285 7392811022113666541687357)
                    ·
                      refine ⟨2772304133292624953132759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7392811022113666541687357 2772304133292624953132759)
                      ·
                        rfl

theorem cell23_5399043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_5399043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399043 prefixEnd_5399043 := by exact prefixLift 5399043
  have htrace : WordTrace (prefixWord ++ tailWord_5399043) baseStart_5399043 baseEnd_5399043 := by
    simpa [prefixWord, tailWord_5399043, baseEnd_5399043] using wordTrace_append hprefix tailTrace_5399043
  have hstable : (prefixWord ++ tailWord_5399043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399043).length < 2 ^ (prefixWord ++ tailWord_5399043).sum := by decide
  have hdescent : baseEnd_5399043 < baseStart_5399043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399044 : List Nat := [2, 3, 2, 3, 1, 3, 1, 1, 1, 4, 2]
def baseStart_5399044 : Nat := 118140960795 + 5399044 * 2 ^ 59
def prefixEnd_5399044 : Nat := 4983230072969 + 3 ^ 40 * 5399044 * 2
def baseEnd_5399044 : Nat := 2772304646773279449220255

theorem tailTrace_5399044 : CollatzResearch.WordTrace tailWord_5399044 prefixEnd_5399044 2772304646773279449220255 := by
  unfold tailWord_5399044
  simp only [CollatzResearch.WordTrace]
  refine ⟨98459656126096573074754093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131279541501462097433005457 98459656126096573074754093)
  ·
    refine ⟨36922371047286214903032785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98459656126096573074754093 36922371047286214903032785)
    ·
      refine ⟨27691778285464661177274589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36922371047286214903032785 27691778285464661177274589)
      ·
        refine ⟨10384416857049247941477971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27691778285464661177274589 10384416857049247941477971)
        ·
          refine ⟨15576625285573871912216957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10384416857049247941477971 15576625285573871912216957)
          ·
            refine ⟨5841234482090201967081359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15576625285573871912216957 5841234482090201967081359)
            ·
              refine ⟨8761851723135302950622039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5841234482090201967081359 8761851723135302950622039)
              ·
                refine ⟨13142777584702954425933059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8761851723135302950622039 13142777584702954425933059)
                ·
                  refine ⟨19714166377054431638899589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13142777584702954425933059 19714166377054431638899589)
                  ·
                    refine ⟨3696406195697705932293673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19714166377054431638899589 3696406195697705932293673)
                    ·
                      refine ⟨2772304646773279449220255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3696406195697705932293673 2772304646773279449220255)
                      ·
                        rfl

theorem cell23_5399044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_5399044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399044 prefixEnd_5399044 := by exact prefixLift 5399044
  have htrace : WordTrace (prefixWord ++ tailWord_5399044) baseStart_5399044 baseEnd_5399044 := by
    simpa [prefixWord, tailWord_5399044, baseEnd_5399044] using wordTrace_append hprefix tailTrace_5399044
  have hstable : (prefixWord ++ tailWord_5399044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399044).length < 2 ^ (prefixWord ++ tailWord_5399044).sum := by decide
  have hdescent : baseEnd_5399044 < baseStart_5399044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399073 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_5399073 : Nat := 118140960795 + 5399073 * 2 ^ 59
def prefixEnd_5399073 : Nat := 4983230072969 + 3 ^ 40 * 5399073 * 2
def baseEnd_5399073 : Nat := 2772319537712259835757621

theorem tailTrace_5399073 : CollatzResearch.WordTrace tailWord_5399073 prefixEnd_5399073 2772319537712259835757621 := by
  unfold tailWord_5399073
  simp only [CollatzResearch.WordTrace]
  refine ⟨196920369969088084102313873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131280246646058722734875915 196920369969088084102313873)
  ·
    refine ⟨147690277476816063076735405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196920369969088084102313873 147690277476816063076735405)
    ·
      refine ⟨55383854053806023653775777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147690277476816063076735405 55383854053806023653775777)
      ·
        refine ⟨41537890540354517740331833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55383854053806023653775777 41537890540354517740331833)
        ·
          refine ⟨31153417905265888305248875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41537890540354517740331833 31153417905265888305248875)
          ·
            refine ⟨46730126857898832457873313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31153417905265888305248875 46730126857898832457873313)
            ·
              refine ⟨35047595143424124343404985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46730126857898832457873313 35047595143424124343404985)
              ·
                refine ⟨26285696357568093257553739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35047595143424124343404985 26285696357568093257553739)
                ·
                  refine ⟨39428544536352139886330609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26285696357568093257553739 39428544536352139886330609)
                  ·
                    refine ⟨29571408402264104914747957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39428544536352139886330609 29571408402264104914747957)
                    ·
                      refine ⟨2772319537712259835757621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29571408402264104914747957 2772319537712259835757621)
                      ·
                        rfl

theorem cell23_5399073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_5399073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399073 prefixEnd_5399073 := by exact prefixLift 5399073
  have htrace : WordTrace (prefixWord ++ tailWord_5399073) baseStart_5399073 baseEnd_5399073 := by
    simpa [prefixWord, tailWord_5399073, baseEnd_5399073] using wordTrace_append hprefix tailTrace_5399073
  have hstable : (prefixWord ++ tailWord_5399073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399073).length < 2 ^ (prefixWord ++ tailWord_5399073).sum := by decide
  have hdescent : baseEnd_5399073 < baseStart_5399073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399080 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 4, 5]
def baseStart_5399080 : Nat := 118140960795 + 5399080 * 2 ^ 59
def prefixEnd_5399080 : Nat := 4983230072969 + 3 ^ 40 * 5399080 * 2
def baseEnd_5399080 : Nat := 924107710692280436123363

theorem tailTrace_5399080 : CollatzResearch.WordTrace tailWord_5399080 prefixEnd_5399080 924107710692280436123363 := by
  unfold tailWord_5399080
  simp only [CollatzResearch.WordTrace]
  refine ⟨98460312640031362148909347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131280416853375149531879129 98460312640031362148909347)
  ·
    refine ⟨147690468960047043223364021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98460312640031362148909347 147690468960047043223364021)
    ·
      refine ⟨13845981465004410302190377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147690468960047043223364021 13845981465004410302190377)
      ·
        refine ⟨10384486098753307726642783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13845981465004410302190377 10384486098753307726642783)
        ·
          refine ⟨15576729148129961589964175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10384486098753307726642783 15576729148129961589964175)
          ·
            refine ⟨23365093722194942384946263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15576729148129961589964175 23365093722194942384946263)
            ·
              refine ⟨35047640583292413577419395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23365093722194942384946263 35047640583292413577419395)
              ·
                refine ⟨52571460874938620366129093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35047640583292413577419395 52571460874938620366129093)
                ·
                  refine ⟨9857148914050991318649205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52571460874938620366129093 9857148914050991318649205)
                  ·
                    refine ⟨924107710692280436123363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9857148914050991318649205 924107710692280436123363)
                    ·
                      rfl

theorem cell23_5399080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_5399080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399080 prefixEnd_5399080 := by exact prefixLift 5399080
  have htrace : WordTrace (prefixWord ++ tailWord_5399080) baseStart_5399080 baseEnd_5399080 := by
    simpa [prefixWord, tailWord_5399080, baseEnd_5399080] using wordTrace_append hprefix tailTrace_5399080
  have hstable : (prefixWord ++ tailWord_5399080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399080).length < 2 ^ (prefixWord ++ tailWord_5399080).sum := by decide
  have hdescent : baseEnd_5399080 < baseStart_5399080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399117 : List Nat := [1, 6, 1, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_5399117 : Nat := 118140960795 + 5399117 * 2 ^ 59
def prefixEnd_5399117 : Nat := 4983230072969 + 3 ^ 40 * 5399117 * 2
def baseEnd_5399117 : Nat := 2772342130861057663607419

theorem tailTrace_5399117 : CollatzResearch.WordTrace tailWord_5399117 prefixEnd_5399117 2772342130861057663607419 := by
  unfold tailWord_5399117
  simp only [CollatzResearch.WordTrace]
  refine ⟨196921974780928679616915605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131281316520619119744610403 196921974780928679616915605)
  ·
    refine ⟨9230717567856031857042919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 196921974780928679616915605 9230717567856031857042919)
    ·
      refine ⟨13846076351784047785564379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9230717567856031857042919 13846076351784047785564379)
      ·
        refine ⟨20769114527676071678346569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13846076351784047785564379 20769114527676071678346569)
        ·
          refine ⟨15576835895757053758759927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20769114527676071678346569 15576835895757053758759927)
          ·
            refine ⟨23365253843635580638139891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15576835895757053758759927 23365253843635580638139891)
            ·
              refine ⟨35047880765453370957209837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23365253843635580638139891 35047880765453370957209837)
              ·
                refine ⟨13142955287045014108953689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35047880765453370957209837 13142955287045014108953689)
                ·
                  refine ⟨9857216465283760581715267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13142955287045014108953689 9857216465283760581715267)
                  ·
                    refine ⟨14785824697925640872572901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9857216465283760581715267 14785824697925640872572901)
                    ·
                      refine ⟨2772342130861057663607419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14785824697925640872572901 2772342130861057663607419)
                      ·
                        rfl

theorem cell23_5399117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_5399117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399117 prefixEnd_5399117 := by exact prefixLift 5399117
  have htrace : WordTrace (prefixWord ++ tailWord_5399117) baseStart_5399117 baseEnd_5399117 := by
    simpa [prefixWord, tailWord_5399117, baseEnd_5399117] using wordTrace_append hprefix tailTrace_5399117
  have hstable : (prefixWord ++ tailWord_5399117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399117).length < 2 ^ (prefixWord ++ tailWord_5399117).sum := by decide
  have hdescent : baseEnd_5399117 < baseStart_5399117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399127 : List Nat := [1, 1, 3, 2, 2, 2, 2, 5, 1, 4]
def baseStart_5399127 : Nat := 118140960795 + 5399127 * 2 ^ 59
def prefixEnd_5399127 : Nat := 4983230072969 + 3 ^ 40 * 5399127 * 2
def baseEnd_5399127 : Nat := 924115755222534208160791

theorem tailTrace_5399127 : CollatzResearch.WordTrace tailWord_5399127 prefixEnd_5399127 924115755222534208160791 := by
  unfold tailWord_5399127
  simp only [CollatzResearch.WordTrace]
  refine ⟨196922339510892451324779635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131281559673928300883186423 196922339510892451324779635)
  ·
    refine ⟨295383509266338676987169453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196922339510892451324779635 295383509266338676987169453)
    ·
      refine ⟨110768815974877003870188545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295383509266338676987169453 110768815974877003870188545)
      ·
        refine ⟨83076611981157752902641409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110768815974877003870188545 83076611981157752902641409)
        ·
          refine ⟨62307458985868314676981057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83076611981157752902641409 62307458985868314676981057)
          ·
            refine ⟨46730594239401236007735793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62307458985868314676981057 46730594239401236007735793)
            ·
              refine ⟨35047945679550927005801845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46730594239401236007735793 35047945679550927005801845)
              ·
                refine ⟨3285744907457899406793923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35047945679550927005801845 3285744907457899406793923)
                ·
                  refine ⟨4928617361186849110190885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3285744907457899406793923 4928617361186849110190885)
                  ·
                    refine ⟨924115755222534208160791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4928617361186849110190885 924115755222534208160791)
                    ·
                      rfl

theorem cell23_5399127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 1, 4].length) (baseStart_5399127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399127 prefixEnd_5399127 := by exact prefixLift 5399127
  have htrace : WordTrace (prefixWord ++ tailWord_5399127) baseStart_5399127 baseEnd_5399127 := by
    simpa [prefixWord, tailWord_5399127, baseEnd_5399127] using wordTrace_append hprefix tailTrace_5399127
  have hstable : (prefixWord ++ tailWord_5399127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399127).length < 2 ^ (prefixWord ++ tailWord_5399127).sum := by decide
  have hdescent : baseEnd_5399127 < baseStart_5399127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399140 : List Nat := [2, 3, 1, 1, 2, 2, 4, 2, 6]
def baseStart_5399140 : Nat := 118140960795 + 5399140 * 2 ^ 59
def prefixEnd_5399140 : Nat := 4983230072969 + 3 ^ 40 * 5399140 * 2
def baseEnd_5399140 : Nat := 308039326768456785957757

theorem tailTrace_5399140 : CollatzResearch.WordTrace tailWord_5399140 prefixEnd_5399140 308039326768456785957757 := by
  unfold tailWord_5399140
  simp only [CollatzResearch.WordTrace]
  refine ⟨98461406829922677272501437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131281875773230236363335249 98461406829922677272501437)
  ·
    refine ⟨36923027561221003977188039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98461406829922677272501437 36923027561221003977188039)
    ·
      refine ⟨55384541341831505965782059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36923027561221003977188039 55384541341831505965782059)
      ·
        refine ⟨83076812012747258948673089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55384541341831505965782059 83076812012747258948673089)
        ·
          refine ⟨62307609009560444211504817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83076812012747258948673089 62307609009560444211504817)
          ·
            refine ⟨46730706757170333158628613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62307609009560444211504817 46730706757170333158628613)
            ·
              refine ⟨8762007516969437467242865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46730706757170333158628613 8762007516969437467242865)
              ·
                refine ⟨6571505637727078100432149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8762007516969437467242865 6571505637727078100432149)
                ·
                  refine ⟨308039326768456785957757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6571505637727078100432149 308039326768456785957757)
                  ·
                    rfl

theorem cell23_5399140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_5399140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399140 prefixEnd_5399140 := by exact prefixLift 5399140
  have htrace : WordTrace (prefixWord ++ tailWord_5399140) baseStart_5399140 baseEnd_5399140 := by
    simpa [prefixWord, tailWord_5399140, baseEnd_5399140] using wordTrace_append hprefix tailTrace_5399140
  have hstable : (prefixWord ++ tailWord_5399140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399140).length < 2 ^ (prefixWord ++ tailWord_5399140).sum := by decide
  have hdescent : baseEnd_5399140 < baseStart_5399140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399143 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_5399143 : Nat := 118140960795 + 5399143 * 2 ^ 59
def prefixEnd_5399143 : Nat := 4983230072969 + 3 ^ 40 * 5399143 * 2
def baseEnd_5399143 : Nat := 2772355481358074561882299

theorem tailTrace_5399143 : CollatzResearch.WordTrace tailWord_5399143 prefixEnd_5399143 2772355481358074561882299 := by
  unfold tailWord_5399143
  simp only [CollatzResearch.WordTrace]
  refine ⟨196922923078834486057362083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131281948719222990704908055 196922923078834486057362083)
  ·
    refine ⟨295384384618251729086043125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196922923078834486057362083 295384384618251729086043125)
    ·
      refine ⟨27692286057961099601816543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 295384384618251729086043125 27692286057961099601816543)
      ·
        refine ⟨41538429086941649402724815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27692286057961099601816543 41538429086941649402724815)
        ·
          refine ⟨62307643630412474104087223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41538429086941649402724815 62307643630412474104087223)
          ·
            refine ⟨93461465445618711156130835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62307643630412474104087223 93461465445618711156130835)
            ·
              refine ⟨140192198168428066734196253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93461465445618711156130835 140192198168428066734196253)
              ·
                refine ⟨52572074313160525025323595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140192198168428066734196253 52572074313160525025323595)
                ·
                  refine ⟨78858111469740787537985393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52572074313160525025323595 78858111469740787537985393)
                  ·
                    refine ⟨59143583602305590653489045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78858111469740787537985393 59143583602305590653489045)
                    ·
                      refine ⟨2772355481358074561882299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59143583602305590653489045 2772355481358074561882299)
                      ·
                        rfl

theorem cell23_5399143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_5399143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399143 prefixEnd_5399143 := by exact prefixLift 5399143
  have htrace : WordTrace (prefixWord ++ tailWord_5399143) baseStart_5399143 baseEnd_5399143 := by
    simpa [prefixWord, tailWord_5399143, baseEnd_5399143] using wordTrace_append hprefix tailTrace_5399143
  have hstable : (prefixWord ++ tailWord_5399143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399143).length < 2 ^ (prefixWord ++ tailWord_5399143).sum := by decide
  have hdescent : baseEnd_5399143 < baseStart_5399143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399160 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 3, 5, 2]
def baseStart_5399160 : Nat := 118140960795 + 5399160 * 2 ^ 59
def prefixEnd_5399160 : Nat := 4983230072969 + 3 ^ 40 * 5399160 * 2
def baseEnd_5399160 : Nat := 2772364210529200995369721

theorem tailTrace_5399160 : CollatzResearch.WordTrace tailWord_5399160 prefixEnd_5399160 2772364210529200995369721 := by
  unfold tailWord_5399160
  simp only [CollatzResearch.WordTrace]
  refine ⟨98461771559886448980365467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131282362079848598640487289 98461771559886448980365467)
  ·
    refine ⟨147692657339829673470548201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98461771559886448980365467 147692657339829673470548201)
    ·
      refine ⟨110769493004872255102911151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147692657339829673470548201 110769493004872255102911151)
      ·
        refine ⟨166154239507308382654366727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110769493004872255102911151 166154239507308382654366727)
        ·
          refine ⟨249231359260962573981550091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166154239507308382654366727 249231359260962573981550091)
          ·
            refine ⟨373847038891443860972325137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249231359260962573981550091 373847038891443860972325137)
            ·
              refine ⟨280385279168582895729243853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373847038891443860972325137 280385279168582895729243853)
              ·
                refine ⟨105144479688218585898466445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 280385279168582895729243853 105144479688218585898466445)
                ·
                  refine ⟨39429179883081969711924917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105144479688218585898466445 39429179883081969711924917)
                  ·
                    refine ⟨3696485614038934660492961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39429179883081969711924917 3696485614038934660492961)
                    ·
                      refine ⟨2772364210529200995369721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3696485614038934660492961 2772364210529200995369721)
                      ·
                        rfl

theorem cell23_5399160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 3, 5, 2].length) (baseStart_5399160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399160 prefixEnd_5399160 := by exact prefixLift 5399160
  have htrace : WordTrace (prefixWord ++ tailWord_5399160) baseStart_5399160 baseEnd_5399160 := by
    simpa [prefixWord, tailWord_5399160, baseEnd_5399160] using wordTrace_append hprefix tailTrace_5399160
  have hstable : (prefixWord ++ tailWord_5399160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399160).length < 2 ^ (prefixWord ++ tailWord_5399160).sum := by decide
  have hdescent : baseEnd_5399160 < baseStart_5399160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399230 : List Nat := [4, 2, 1, 1, 2, 1, 3, 9]
def baseStart_5399230 : Nat := 118140960795 + 5399230 * 2 ^ 59
def prefixEnd_5399230 : Nat := 4983230072969 + 3 ^ 40 * 5399230 * 2
def baseEnd_5399230 : Nat := 102681487191667248944237

theorem tailTrace_5399230 : CollatzResearch.WordTrace tailWord_5399230 prefixEnd_5399230 102681487191667248944237 := by
  unfold tailWord_5399230
  simp only [CollatzResearch.WordTrace]
  refine ⟨24615762028689912489472393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131284064153012866610519429 24615762028689912489472393)
  ·
    refine ⟨18461821521517434367104295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24615762028689912489472393 18461821521517434367104295)
    ·
      refine ⟨27692732282276151550656443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18461821521517434367104295 27692732282276151550656443)
      ·
        refine ⟨41539098423414227325984665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27692732282276151550656443 41539098423414227325984665)
        ·
          refine ⟨31154323817560670494488499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41539098423414227325984665 31154323817560670494488499)
          ·
            refine ⟨46731485726341005741732749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31154323817560670494488499 46731485726341005741732749)
            ·
              refine ⟨17524307147377877153149781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46731485726341005741732749 17524307147377877153149781)
              ·
                refine ⟨102681487191667248944237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17524307147377877153149781 102681487191667248944237)
                ·
                  rfl

theorem cell23_5399230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 9].length) (baseStart_5399230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399230 prefixEnd_5399230 := by exact prefixLift 5399230
  have htrace : WordTrace (prefixWord ++ tailWord_5399230) baseStart_5399230 baseEnd_5399230 := by
    simpa [prefixWord, tailWord_5399230, baseEnd_5399230] using wordTrace_append hprefix tailTrace_5399230
  have hstable : (prefixWord ++ tailWord_5399230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399230).length < 2 ^ (prefixWord ++ tailWord_5399230).sum := by decide
  have hdescent : baseEnd_5399230 < baseStart_5399230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399243 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 3, 9]
def baseStart_5399243 : Nat := 118140960795 + 5399243 * 2 ^ 59
def prefixEnd_5399243 : Nat := 4983230072969 + 3 ^ 40 * 5399243 * 2
def baseEnd_5399243 : Nat := 924135609807841390210613

theorem tailTrace_5399243 : CollatzResearch.WordTrace tailWord_5399243 prefixEnd_5399243 924135609807841390210613 := by
  unfold tailWord_5399243
  simp only [CollatzResearch.WordTrace]
  refine ⟨196926570378472203136002383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131284380252314802090668255 196926570378472203136002383)
  ·
    refine ⟨295389855567708304704003575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196926570378472203136002383 295389855567708304704003575)
    ·
      refine ⟨443084783351562457056005363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295389855567708304704003575 443084783351562457056005363)
      ·
        refine ⟨664627175027343685584008045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443084783351562457056005363 664627175027343685584008045)
        ·
          refine ⟨249235190635253882094003017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 664627175027343685584008045 249235190635253882094003017)
          ·
            refine ⟨186926392976440411570502263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249235190635253882094003017 186926392976440411570502263)
            ·
              refine ⟨280389589464660617355753395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186926392976440411570502263 280389589464660617355753395)
              ·
                refine ⟨420584384196990926033630093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280389589464660617355753395 420584384196990926033630093)
                ·
                  refine ⟨157719144073871597262611285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420584384196990926033630093 157719144073871597262611285)
                  ·
                    refine ⟨924135609807841390210613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 157719144073871597262611285 924135609807841390210613)
                    ·
                      rfl

theorem cell23_5399243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 9].length) (baseStart_5399243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399243 prefixEnd_5399243 := by exact prefixLift 5399243
  have htrace : WordTrace (prefixWord ++ tailWord_5399243) baseStart_5399243 baseEnd_5399243 := by
    simpa [prefixWord, tailWord_5399243, baseEnd_5399243] using wordTrace_append hprefix tailTrace_5399243
  have hstable : (prefixWord ++ tailWord_5399243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399243).length < 2 ^ (prefixWord ++ tailWord_5399243).sum := by decide
  have hdescent : baseEnd_5399243 < baseStart_5399243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399244 : List Nat := [2, 2, 1, 5, 1, 1, 2, 3, 1, 2, 3]
def baseStart_5399244 : Nat := 118140960795 + 5399244 * 2 ^ 59
def prefixEnd_5399244 : Nat := 4983230072969 + 3 ^ 40 * 5399244 * 2
def baseEnd_5399244 : Nat := 2772407342904178666719335

theorem tailTrace_5399244 : CollatzResearch.WordTrace tailWord_5399244 prefixEnd_5399244 2772407342904178666719335 := by
  unfold tailWord_5399244
  simp only [CollatzResearch.WordTrace]
  refine ⟨98463303425734290153394393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131284404567645720204525857 98463303425734290153394393)
  ·
    refine ⟨73847477569300717615045795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98463303425734290153394393 73847477569300717615045795)
    ·
      refine ⟨110771216353951076422568693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73847477569300717615045795 110771216353951076422568693)
      ·
        refine ⟨10384801533182913414615815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110771216353951076422568693 10384801533182913414615815)
        ·
          refine ⟨15577202299774370121923723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10384801533182913414615815 15577202299774370121923723)
          ·
            refine ⟨23365803449661555182885585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15577202299774370121923723 23365803449661555182885585)
            ·
              refine ⟨17524352587246166387164189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23365803449661555182885585 17524352587246166387164189)
              ·
                refine ⟨6571632220217312395186571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17524352587246166387164189 6571632220217312395186571)
                ·
                  refine ⟨9857448330325968592779857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6571632220217312395186571 9857448330325968592779857)
                  ·
                    refine ⟨7393086247744476444584893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9857448330325968592779857 7393086247744476444584893)
                    ·
                      refine ⟨2772407342904178666719335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7393086247744476444584893 2772407342904178666719335)
                      ·
                        rfl

theorem cell23_5399244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_5399244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399244 prefixEnd_5399244 := by exact prefixLift 5399244
  have htrace : WordTrace (prefixWord ++ tailWord_5399244) baseStart_5399244 baseEnd_5399244 := by
    simpa [prefixWord, tailWord_5399244, baseEnd_5399244] using wordTrace_append hprefix tailTrace_5399244
  have hstable : (prefixWord ++ tailWord_5399244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399244).length < 2 ^ (prefixWord ++ tailWord_5399244).sum := by decide
  have hdescent : baseEnd_5399244 < baseStart_5399244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399257 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 4, 1, 3]
def baseStart_5399257 : Nat := 118140960795 + 5399257 * 2 ^ 59
def prefixEnd_5399257 : Nat := 4983230072969 + 3 ^ 40 * 5399257 * 2
def baseEnd_5399257 : Nat := 2772414018152687115856775

theorem tailTrace_5399257 : CollatzResearch.WordTrace tailWord_5399257 prefixEnd_5399257 2772414018152687115856775 := by
  unfold tailWord_5399257
  simp only [CollatzResearch.WordTrace]
  refine ⟨196927081000421483527012025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131284720666947655684674683 196927081000421483527012025)
  ·
    refine ⟨147695310750316112645259019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196927081000421483527012025 147695310750316112645259019)
    ·
      refine ⟨221542966125474168967888529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147695310750316112645259019 221542966125474168967888529)
      ·
        refine ⟨166157224594105626725916397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221542966125474168967888529 166157224594105626725916397)
        ·
          refine ⟨62308959222789610022218649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166157224594105626725916397 62308959222789610022218649)
          ·
            refine ⟨46731719417092207516663987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62308959222789610022218649 46731719417092207516663987)
            ·
              refine ⟨70097579125638311274995981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46731719417092207516663987 70097579125638311274995981)
              ·
                refine ⟨26286592172114366728123493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70097579125638311274995981 26286592172114366728123493)
                ·
                  refine ⟨4928736032271443761523155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26286592172114366728123493 4928736032271443761523155)
                  ·
                    refine ⟨7393104048407165642284733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4928736032271443761523155 7393104048407165642284733)
                    ·
                      refine ⟨2772414018152687115856775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7393104048407165642284733 2772414018152687115856775)
                      ·
                        rfl

theorem cell23_5399257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 1, 3].length) (baseStart_5399257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399257 prefixEnd_5399257 := by exact prefixLift 5399257
  have htrace : WordTrace (prefixWord ++ tailWord_5399257) baseStart_5399257 baseEnd_5399257 := by
    simpa [prefixWord, tailWord_5399257, baseEnd_5399257] using wordTrace_append hprefix tailTrace_5399257
  have hstable : (prefixWord ++ tailWord_5399257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399257).length < 2 ^ (prefixWord ++ tailWord_5399257).sum := by decide
  have hdescent : baseEnd_5399257 < baseStart_5399257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399258 : List Nat := [3, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2]
def baseStart_5399258 : Nat := 118140960795 + 5399258 * 2 ^ 59
def prefixEnd_5399258 : Nat := 4983230072969 + 3 ^ 40 * 5399258 * 2
def baseEnd_5399258 : Nat := 2772414531633341611944271

theorem tailTrace_5399258 : CollatzResearch.WordTrace tailWord_5399258 prefixEnd_5399258 2772414531633341611944271 := by
  unfold tailWord_5399258
  simp only [CollatzResearch.WordTrace]
  refine ⟨49231779368354465174449607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131284744982278573798532285 49231779368354465174449607)
  ·
    refine ⟨73847669052531697761674411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49231779368354465174449607 73847669052531697761674411)
    ·
      refine ⟨110771503578797546642511617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73847669052531697761674411 110771503578797546642511617)
      ·
        refine ⟨83078627684098159981883713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110771503578797546642511617 83078627684098159981883713)
        ·
          refine ⟨62308970763073619986412785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83078627684098159981883713 62308970763073619986412785)
          ·
            refine ⟨46731728072305214989809589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62308970763073619986412785 46731728072305214989809589)
            ·
              refine ⟨4381099506778613905294649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46731728072305214989809589 4381099506778613905294649)
              ·
                refine ⟨3285824630083960428970987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4381099506778613905294649 3285824630083960428970987)
                ·
                  refine ⟨4928736945125940643456481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3285824630083960428970987 4928736945125940643456481)
                  ·
                    refine ⟨3696552708844455482592361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4928736945125940643456481 3696552708844455482592361)
                    ·
                      refine ⟨2772414531633341611944271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3696552708844455482592361 2772414531633341611944271)
                      ·
                        rfl

theorem cell23_5399258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2].length) (baseStart_5399258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399258 prefixEnd_5399258 := by exact prefixLift 5399258
  have htrace : WordTrace (prefixWord ++ tailWord_5399258) baseStart_5399258 baseEnd_5399258 := by
    simpa [prefixWord, tailWord_5399258, baseEnd_5399258] using wordTrace_append hprefix tailTrace_5399258
  have hstable : (prefixWord ++ tailWord_5399258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399258).length < 2 ^ (prefixWord ++ tailWord_5399258).sum := by decide
  have hdescent : baseEnd_5399258 < baseStart_5399258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399310 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_5399310 : Nat := 118140960795 + 5399310 * 2 ^ 59
def prefixEnd_5399310 : Nat := 4983230072969 + 3 ^ 40 * 5399310 * 2
def baseEnd_5399310 : Nat := 2772441232627375408494031

theorem tailTrace_5399310 : CollatzResearch.WordTrace tailWord_5399310 prefixEnd_5399310 2772441232627375408494031 := by
  unfold tailWord_5399310
  simp only [CollatzResearch.WordTrace]
  refine ⟨24616126758653684197336423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131286009379486315719127589 24616126758653684197336423)
  ·
    refine ⟨36924190137980526296004635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24616126758653684197336423 36924190137980526296004635)
    ·
      refine ⟨55386285206970789444006953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36924190137980526296004635 55386285206970789444006953)
      ·
        refine ⟨41539713905228092083005215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55386285206970789444006953 41539713905228092083005215)
        ·
          refine ⟨62309570857842138124507823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41539713905228092083005215 62309570857842138124507823)
          ·
            refine ⟨93464356286763207186761735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62309570857842138124507823 93464356286763207186761735)
            ·
              refine ⟨140196534430144810780142603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93464356286763207186761735 140196534430144810780142603)
              ·
                refine ⟨210294801645217216170213905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140196534430144810780142603 210294801645217216170213905)
                ·
                  refine ⟨157721101233912912127660429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210294801645217216170213905 157721101233912912127660429)
                  ·
                    refine ⟨59145412962717342047872661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 157721101233912912127660429 59145412962717342047872661)
                    ·
                      refine ⟨2772441232627375408494031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59145412962717342047872661 2772441232627375408494031)
                      ·
                        rfl

theorem cell23_5399310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_5399310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399310 prefixEnd_5399310 := by exact prefixLift 5399310
  have htrace : WordTrace (prefixWord ++ tailWord_5399310) baseStart_5399310 baseEnd_5399310 := by
    simpa [prefixWord, tailWord_5399310, baseEnd_5399310] using wordTrace_append hprefix tailTrace_5399310
  have hstable : (prefixWord ++ tailWord_5399310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399310).length < 2 ^ (prefixWord ++ tailWord_5399310).sum := by decide
  have hdescent : baseEnd_5399310 < baseStart_5399310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399320 : List Nat := [2, 1, 2, 3, 1, 1, 1, 5, 7]
def baseStart_5399320 : Nat := 118140960795 + 5399320 * 2 ^ 59
def prefixEnd_5399320 : Nat := 4983230072969 + 3 ^ 40 * 5399320 * 2
def baseEnd_5399320 : Nat := 308049596381546707707665

theorem tailTrace_5399320 : CollatzResearch.WordTrace tailWord_5399320 prefixEnd_5399320 308049596381546707707665 := by
  unfold tailWord_5399320
  simp only [CollatzResearch.WordTrace]
  refine ⟨98464689399596622643277707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131286252532795496857703609 98464689399596622643277707)
  ·
    refine ⟨147697034099394933964916561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98464689399596622643277707 147697034099394933964916561)
    ·
      refine ⟨110772775574546200473687421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147697034099394933964916561 110772775574546200473687421)
      ·
        refine ⟨41539790840454825177632783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110772775574546200473687421 41539790840454825177632783)
        ·
          refine ⟨62309686260682237766449175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41539790840454825177632783 62309686260682237766449175)
          ·
            refine ⟨93464529391023356649673763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62309686260682237766449175 93464529391023356649673763)
            ·
              refine ⟨140196794086535034974510645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93464529391023356649673763 140196794086535034974510645)
              ·
                refine ⟨13143449445612659528860373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140196794086535034974510645 13143449445612659528860373)
                ·
                  refine ⟨308049596381546707707665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13143449445612659528860373 308049596381546707707665)
                  ·
                    rfl

theorem cell23_5399320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 7].length) (baseStart_5399320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399320 prefixEnd_5399320 := by exact prefixLift 5399320
  have htrace : WordTrace (prefixWord ++ tailWord_5399320) baseStart_5399320 baseEnd_5399320 := by
    simpa [prefixWord, tailWord_5399320, baseEnd_5399320] using wordTrace_append hprefix tailTrace_5399320
  have hstable : (prefixWord ++ tailWord_5399320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399320).length < 2 ^ (prefixWord ++ tailWord_5399320).sum := by decide
  have hdescent : baseEnd_5399320 < baseStart_5399320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399327 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 4]
def baseStart_5399327 : Nat := 118140960795 + 5399327 * 2 ^ 59
def prefixEnd_5399327 : Nat := 4983230072969 + 3 ^ 40 * 5399327 * 2
def baseEnd_5399327 : Nat := 2772449961798501841981453

theorem tailTrace_5399327 : CollatzResearch.WordTrace tailWord_5399327 prefixEnd_5399327 2772449961798501841981453 := by
  unfold tailWord_5399327
  simp only [CollatzResearch.WordTrace]
  refine ⟨196929634110167885482060235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131286422740111923654706823 196929634110167885482060235)
  ·
    refine ⟨295394451165251828223090353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196929634110167885482060235 295394451165251828223090353)
    ·
      refine ⟨221545838373938871167317765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295394451165251828223090353 221545838373938871167317765)
      ·
        refine ⟨41539844695113538343872081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221545838373938871167317765 41539844695113538343872081)
        ·
          refine ⟨31154883521335153757904061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41539844695113538343872081 31154883521335153757904061)
          ·
            refine ⟨11683081320500682659214023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31154883521335153757904061 11683081320500682659214023)
            ·
              refine ⟨17524621980751023988821035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11683081320500682659214023 17524621980751023988821035)
              ·
                refine ⟨26286932971126535983231553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17524621980751023988821035 26286932971126535983231553)
                ·
                  refine ⟨19715199728344901987423665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26286932971126535983231553 19715199728344901987423665)
                  ·
                    refine ⟨14786399796258676490567749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19715199728344901987423665 14786399796258676490567749)
                    ·
                      refine ⟨2772449961798501841981453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14786399796258676490567749 2772449961798501841981453)
                      ·
                        rfl

theorem cell23_5399327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_5399327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399327 prefixEnd_5399327 := by exact prefixLift 5399327
  have htrace : WordTrace (prefixWord ++ tailWord_5399327) baseStart_5399327 baseEnd_5399327 := by
    simpa [prefixWord, tailWord_5399327, baseEnd_5399327] using wordTrace_append hprefix tailTrace_5399327
  have hstable : (prefixWord ++ tailWord_5399327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399327).length < 2 ^ (prefixWord ++ tailWord_5399327).sum := by decide
  have hdescent : baseEnd_5399327 < baseStart_5399327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399360 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 5]
def baseStart_5399360 : Nat := 118140960795 + 5399360 * 2 ^ 59
def prefixEnd_5399360 : Nat := 4983230072969 + 3 ^ 40 * 5399360 * 2
def baseEnd_5399360 : Nat := 2772466906660100212868801

theorem tailTrace_5399360 : CollatzResearch.WordTrace tailWord_5399360 prefixEnd_5399360 2772466906660100212868801 := by
  unfold tailWord_5399360
  simp only [CollatzResearch.WordTrace]
  refine ⟨98465418859524166059005767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131287225146032221412007689 98465418859524166059005767)
  ·
    refine ⟨147698128289286249088508651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98465418859524166059005767 147698128289286249088508651)
    ·
      refine ⟨221547192433929373632762977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147698128289286249088508651 221547192433929373632762977)
      ·
        refine ⟨166160394325447030224572233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221547192433929373632762977 166160394325447030224572233)
        ·
          refine ⟨124620295744085272668429175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166160394325447030224572233 124620295744085272668429175)
          ·
            refine ⟨186930443616127909002643763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124620295744085272668429175 186930443616127909002643763)
            ·
              refine ⟨280395665424191863503965645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186930443616127909002643763 280395665424191863503965645)
              ·
                refine ⟨105148374534071948813987117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 280395665424191863503965645 105148374534071948813987117)
                ·
                  refine ⟨39430640450276980805245169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105148374534071948813987117 39430640450276980805245169)
                  ·
                    refine ⟨29572980337707735603933877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39430640450276980805245169 29572980337707735603933877)
                    ·
                      refine ⟨2772466906660100212868801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29572980337707735603933877 2772466906660100212868801)
                      ·
                        rfl

theorem cell23_5399360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_5399360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399360 prefixEnd_5399360 := by exact prefixLift 5399360
  have htrace : WordTrace (prefixWord ++ tailWord_5399360) baseStart_5399360 baseEnd_5399360 := by
    simpa [prefixWord, tailWord_5399360, baseEnd_5399360] using wordTrace_append hprefix tailTrace_5399360
  have hstable : (prefixWord ++ tailWord_5399360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399360).length < 2 ^ (prefixWord ++ tailWord_5399360).sum := by decide
  have hdescent : baseEnd_5399360 < baseStart_5399360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399387 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 7, 6, 2]
def baseStart_5399387 : Nat := 118140960795 + 5399387 * 2 ^ 59
def prefixEnd_5399387 : Nat := 4983230072969 + 3 ^ 40 * 5399387 * 2
def baseEnd_5399387 : Nat := 2772480770637771607231177

theorem tailTrace_5399387 : CollatzResearch.WordTrace tailWord_5399387 prefixEnd_5399387 2772480770637771607231177 := by
  unfold tailWord_5399387
  simp only [CollatzResearch.WordTrace]
  refine ⟨196931822489950515729244415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131287881659967010486162943 196931822489950515729244415)
  ·
    refine ⟨295397733734925773593866623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196931822489950515729244415 295397733734925773593866623)
    ·
      refine ⟨443096600602388660390799935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295397733734925773593866623 443096600602388660390799935)
      ·
        refine ⟨664644900903582990586199903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443096600602388660390799935 664644900903582990586199903)
        ·
          refine ⟨996967351355374485879299855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 664644900903582990586199903 996967351355374485879299855)
          ·
            refine ⟨1495451027033061728818949783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996967351355374485879299855 1495451027033061728818949783)
            ·
              refine ⟨2243176540549592593228424675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495451027033061728818949783 2243176540549592593228424675)
              ·
                refine ⟨3364764810824388889842637013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2243176540549592593228424675 3364764810824388889842637013)
                ·
                  refine ⟨78861675253696614605686805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3364764810824388889842637013 78861675253696614605686805)
                  ·
                    refine ⟨3696641027517028809641569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78861675253696614605686805 3696641027517028809641569)
                    ·
                      refine ⟨2772480770637771607231177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3696641027517028809641569 2772480770637771607231177)
                      ·
                        rfl

theorem cell23_5399387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 6, 2].length) (baseStart_5399387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399387 prefixEnd_5399387 := by exact prefixLift 5399387
  have htrace : WordTrace (prefixWord ++ tailWord_5399387) baseStart_5399387 baseEnd_5399387 := by
    simpa [prefixWord, tailWord_5399387, baseEnd_5399387] using wordTrace_append hprefix tailTrace_5399387
  have hstable : (prefixWord ++ tailWord_5399387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399387).length < 2 ^ (prefixWord ++ tailWord_5399387).sum := by decide
  have hdescent : baseEnd_5399387 < baseStart_5399387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399407 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 3]
def baseStart_5399407 : Nat := 118140960795 + 5399407 * 2 ^ 59
def prefixEnd_5399407 : Nat := 4983230072969 + 3 ^ 40 * 5399407 * 2
def baseEnd_5399407 : Nat := 2772491040250861528981085

theorem tailTrace_5399407 : CollatzResearch.WordTrace tailWord_5399407 prefixEnd_5399407 2772491040250861528981085 := by
  unfold tailWord_5399407
  simp only [CollatzResearch.WordTrace]
  refine ⟨196932551949878059144972475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131288367966585372763314983 196932551949878059144972475)
  ·
    refine ⟨295398827924817088717458713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196932551949878059144972475 295398827924817088717458713)
    ·
      refine ⟨221549120943612816538094035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295398827924817088717458713 221549120943612816538094035)
      ·
        refine ⟨332323681415419224807141053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221549120943612816538094035 332323681415419224807141053)
        ·
          refine ⟨124621380530782209302677895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332323681415419224807141053 124621380530782209302677895)
          ·
            refine ⟨186932070796173313954016843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124621380530782209302677895 186932070796173313954016843)
            ·
              refine ⟨280398106194259970931025265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186932070796173313954016843 280398106194259970931025265)
              ·
                refine ⟨210298579645694978198268949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280398106194259970931025265 210298579645694978198268949)
                ·
                  refine ⟨9857745920891952103043857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 210298579645694978198268949 9857745920891952103043857)
                  ·
                    refine ⟨7393309440668964077282893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9857745920891952103043857 7393309440668964077282893)
                    ·
                      refine ⟨2772491040250861528981085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7393309440668964077282893 2772491040250861528981085)
                      ·
                        rfl

theorem cell23_5399407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 3].length) (baseStart_5399407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399407 prefixEnd_5399407 := by exact prefixLift 5399407
  have htrace : WordTrace (prefixWord ++ tailWord_5399407) baseStart_5399407 baseEnd_5399407 := by
    simpa [prefixWord, tailWord_5399407, baseEnd_5399407] using wordTrace_append hprefix tailTrace_5399407
  have hstable : (prefixWord ++ tailWord_5399407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399407).length < 2 ^ (prefixWord ++ tailWord_5399407).sum := by decide
  have hdescent : baseEnd_5399407 < baseStart_5399407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399427 : List Nat := [1, 1, 1, 3, 4, 1, 2, 4, 6]
def baseStart_5399427 : Nat := 118140960795 + 5399427 * 2 ^ 59
def prefixEnd_5399427 : Nat := 4983230072969 + 3 ^ 40 * 5399427 * 2
def baseEnd_5399427 : Nat := 308055701095994605636777

theorem tailTrace_5399427 : CollatzResearch.WordTrace tailWord_5399427 prefixEnd_5399427 308055701095994605636777 := by
  unfold tailWord_5399427
  simp only [CollatzResearch.WordTrace]
  refine ⟨196933281409805602560700535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131288854273203735040467023 196933281409805602560700535)
  ·
    refine ⟨295399922114708403841050803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196933281409805602560700535 295399922114708403841050803)
    ·
      refine ⟨443099883172062605761576205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295399922114708403841050803 443099883172062605761576205)
      ·
        refine ⟨166162456189523477160591077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 443099883172062605761576205 166162456189523477160591077)
        ·
          refine ⟨31155460535535651967610827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166162456189523477160591077 31155460535535651967610827)
          ·
            refine ⟨46733190803303477951416241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31155460535535651967610827 46733190803303477951416241)
            ·
              refine ⟨35049893102477608463562181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46733190803303477951416241 35049893102477608463562181)
              ·
                refine ⟨6571854956714551586917909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35049893102477608463562181 6571854956714551586917909)
                ·
                  refine ⟨308055701095994605636777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6571854956714551586917909 308055701095994605636777)
                  ·
                    rfl

theorem cell23_5399427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 6].length) (baseStart_5399427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399427 prefixEnd_5399427 := by exact prefixLift 5399427
  have htrace : WordTrace (prefixWord ++ tailWord_5399427) baseStart_5399427 baseEnd_5399427 := by
    simpa [prefixWord, tailWord_5399427, baseEnd_5399427] using wordTrace_append hprefix tailTrace_5399427
  have hstable : (prefixWord ++ tailWord_5399427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399427).length < 2 ^ (prefixWord ++ tailWord_5399427).sum := by decide
  have hdescent : baseEnd_5399427 < baseStart_5399427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399431 : List Nat := [1, 1, 4, 2, 3, 3, 1, 1, 3, 4]
def baseStart_5399431 : Nat := 118140960795 + 5399431 * 2 ^ 59
def prefixEnd_5399431 : Nat := 4983230072969 + 3 ^ 40 * 5399431 * 2
def baseEnd_5399431 : Nat := 924167787928856478360325

theorem tailTrace_5399431 : CollatzResearch.WordTrace tailWord_5399431 prefixEnd_5399431 924167787928856478360325 := by
  unfold tailWord_5399431
  simp only [CollatzResearch.WordTrace]
  refine ⟨196933427301791111243846147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131288951534527407495897431 196933427301791111243846147)
  ·
    refine ⟨295400140952686666865769221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196933427301791111243846147 295400140952686666865769221)
    ·
      refine ⟨55387526428628750037331729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 295400140952686666865769221 55387526428628750037331729)
      ·
        refine ⟨41540644821471562527998797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55387526428628750037331729 41540644821471562527998797)
        ·
          refine ⟨15577741808051835947999549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41540644821471562527998797 15577741808051835947999549)
          ·
            refine ⟨5841653178019438480499831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15577741808051835947999549 5841653178019438480499831)
            ·
              refine ⟨8762479767029157720749747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5841653178019438480499831 8762479767029157720749747)
              ·
                refine ⟨13143719650543736581124621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8762479767029157720749747 13143719650543736581124621)
                ·
                  refine ⟨4928894868953901217921733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13143719650543736581124621 4928894868953901217921733)
                  ·
                    refine ⟨924167787928856478360325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4928894868953901217921733 924167787928856478360325)
                    ·
                      rfl

theorem cell23_5399431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_5399431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399431 prefixEnd_5399431 := by exact prefixLift 5399431
  have htrace : WordTrace (prefixWord ++ tailWord_5399431) baseStart_5399431 baseEnd_5399431 := by
    simpa [prefixWord, tailWord_5399431, baseEnd_5399431] using wordTrace_append hprefix tailTrace_5399431
  have hstable : (prefixWord ++ tailWord_5399431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399431).length < 2 ^ (prefixWord ++ tailWord_5399431).sum := by decide
  have hdescent : baseEnd_5399431 < baseStart_5399431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399444 : List Nat := [2, 4, 2, 1, 1, 1, 3, 3, 6]
def baseStart_5399444 : Nat := 118140960795 + 5399444 * 2 ^ 59
def prefixEnd_5399444 : Nat := 4983230072969 + 3 ^ 40 * 5399444 * 2
def baseEnd_5399444 : Nat := 308056671003897542690935

theorem tailTrace_5399444 : CollatzResearch.WordTrace tailWord_5399444 prefixEnd_5399444 308056671003897542690935 := by
  unfold tailWord_5399444
  simp only [CollatzResearch.WordTrace]
  refine ⟨98466950725372007232034693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131289267633829342976046257 98466950725372007232034693)
  ·
    refine ⟨18462553261007251356006505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98466950725372007232034693 18462553261007251356006505)
    ·
      refine ⟨13846914945755438517004879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18462553261007251356006505 13846914945755438517004879)
      ·
        refine ⟨20770372418633157775507319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13846914945755438517004879 20770372418633157775507319)
        ·
          refine ⟨31155558627949736663260979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20770372418633157775507319 31155558627949736663260979)
          ·
            refine ⟨46733337941924604994891469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31155558627949736663260979 46733337941924604994891469)
            ·
              refine ⟨17525001728221726873084301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46733337941924604994891469 17525001728221726873084301)
              ·
                refine ⟨6571875648083147577406613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17525001728221726873084301 6571875648083147577406613)
                ·
                  refine ⟨308056671003897542690935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6571875648083147577406613 308056671003897542690935)
                  ·
                    rfl

theorem cell23_5399444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_5399444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399444 prefixEnd_5399444 := by exact prefixLift 5399444
  have htrace : WordTrace (prefixWord ++ tailWord_5399444) baseStart_5399444 baseEnd_5399444 := by
    simpa [prefixWord, tailWord_5399444, baseEnd_5399444] using wordTrace_append hprefix tailTrace_5399444
  have hstable : (prefixWord ++ tailWord_5399444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399444).length < 2 ^ (prefixWord ++ tailWord_5399444).sum := by decide
  have hdescent : baseEnd_5399444 < baseStart_5399444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399481 : List Nat := [1, 2, 1, 4, 2, 2, 2, 2, 2, 3, 2]
def baseStart_5399481 : Nat := 118140960795 + 5399481 * 2 ^ 59
def prefixEnd_5399481 : Nat := 4983230072969 + 3 ^ 40 * 5399481 * 2
def baseEnd_5399481 : Nat := 2772529037819294239455745

theorem tailTrace_5399481 : CollatzResearch.WordTrace tailWord_5399481 prefixEnd_5399481 2772529037819294239455745 := by
  unfold tailWord_5399481
  simp only [CollatzResearch.WordTrace]
  refine ⟨196935250951609969783166297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131290167301073313188777531 196935250951609969783166297)
  ·
    refine ⟨147701438213707477337374723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196935250951609969783166297 147701438213707477337374723)
    ·
      refine ⟨221552157320561216006062085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147701438213707477337374723 221552157320561216006062085)
      ·
        refine ⟨41541029497605228001136641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221552157320561216006062085 41541029497605228001136641)
        ·
          refine ⟨31155772123203921000852481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41541029497605228001136641 31155772123203921000852481)
          ·
            refine ⟨23366829092402940750639361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31155772123203921000852481 23366829092402940750639361)
            ·
              refine ⟨17525121819302205562979521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23366829092402940750639361 17525121819302205562979521)
              ·
                refine ⟨13143841364476654172234641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17525121819302205562979521 13143841364476654172234641)
                ·
                  refine ⟨9857881023357490629175981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13143841364476654172234641 9857881023357490629175981)
                  ·
                    refine ⟨3696705383759058985940993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9857881023357490629175981 3696705383759058985940993)
                    ·
                      refine ⟨2772529037819294239455745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3696705383759058985940993 2772529037819294239455745)
                      ·
                        rfl

theorem cell23_5399481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_5399481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399481 prefixEnd_5399481 := by exact prefixLift 5399481
  have htrace : WordTrace (prefixWord ++ tailWord_5399481) baseStart_5399481 baseEnd_5399481 := by
    simpa [prefixWord, tailWord_5399481, baseEnd_5399481] using wordTrace_append hprefix tailTrace_5399481
  have hstable : (prefixWord ++ tailWord_5399481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399481).length < 2 ^ (prefixWord ++ tailWord_5399481).sum := by decide
  have hdescent : baseEnd_5399481 < baseStart_5399481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399488 : List Nat := [2, 1, 1, 2, 3, 4, 1, 4, 1, 1, 3]
def baseStart_5399488 : Nat := 118140960795 + 5399488 * 2 ^ 59
def prefixEnd_5399488 : Nat := 4983230072969 + 3 ^ 40 * 5399488 * 2
def baseEnd_5399488 : Nat := 2772532632183875712068213

theorem tailTrace_5399488 : CollatzResearch.WordTrace tailWord_5399488 prefixEnd_5399488 2772532632183875712068213 := by
  unfold tailWord_5399488
  simp only [CollatzResearch.WordTrace]
  refine ⟨98467753131292304989335559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131290337508389739985780745 98467753131292304989335559)
  ·
    refine ⟨147701629696938457484003339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98467753131292304989335559 147701629696938457484003339)
    ·
      refine ⟨221552444545407686226005009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147701629696938457484003339 221552444545407686226005009)
      ·
        refine ⟨166164333409055764669503757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221552444545407686226005009 166164333409055764669503757)
        ·
          refine ⟨62311625028395911751063909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166164333409055764669503757 62311625028395911751063909)
          ·
            refine ⟨11683429692824233453324483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62311625028395911751063909 11683429692824233453324483)
            ·
              refine ⟨17525144539236350179986725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11683429692824233453324483 17525144539236350179986725)
              ·
                refine ⟨3285964601106815658747511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17525144539236350179986725 3285964601106815658747511)
                ·
                  refine ⟨4928946901660223488121267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3285964601106815658747511 4928946901660223488121267)
                  ·
                    refine ⟨7393420352490335232181901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4928946901660223488121267 7393420352490335232181901)
                    ·
                      refine ⟨2772532632183875712068213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7393420352490335232181901 2772532632183875712068213)
                      ·
                        rfl

theorem cell23_5399488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 1, 1, 3].length) (baseStart_5399488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399488 prefixEnd_5399488 := by exact prefixLift 5399488
  have htrace : WordTrace (prefixWord ++ tailWord_5399488) baseStart_5399488 baseEnd_5399488 := by
    simpa [prefixWord, tailWord_5399488, baseEnd_5399488] using wordTrace_append hprefix tailTrace_5399488
  have hstable : (prefixWord ++ tailWord_5399488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399488).length < 2 ^ (prefixWord ++ tailWord_5399488).sum := by decide
  have hdescent : baseEnd_5399488 < baseStart_5399488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399497 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 1, 8, 3]
def baseStart_5399497 : Nat := 118140960795 + 5399497 * 2 ^ 59
def prefixEnd_5399497 : Nat := 4983230072969 + 3 ^ 40 * 5399497 * 2
def baseEnd_5399497 : Nat := 2772537253509766176855671

theorem tailTrace_5399497 : CollatzResearch.WordTrace tailWord_5399497 prefixEnd_5399497 2772537253509766176855671 := by
  unfold tailWord_5399497
  simp only [CollatzResearch.WordTrace]
  refine ⟨196935834519552004515748745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131290556346368003010499163 196935834519552004515748745)
  ·
    refine ⟨147701875889664003386811559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196935834519552004515748745 147701875889664003386811559)
    ·
      refine ⟨221552813834496005080217339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147701875889664003386811559 221552813834496005080217339)
      ·
        refine ⟨332329220751744007620326009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221552813834496005080217339 332329220751744007620326009)
        ·
          refine ⟨249246915563808005715244507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332329220751744007620326009 249246915563808005715244507)
          ·
            refine ⟨373870373345712008572866761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249246915563808005715244507 373870373345712008572866761)
            ·
              refine ⟨280402780009284006429650071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373870373345712008572866761 280402780009284006429650071)
              ·
                refine ⟨420604170013926009644475107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280402780009284006429650071 420604170013926009644475107)
                ·
                  refine ⟨630906255020889014466712661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 420604170013926009644475107 630906255020889014466712661)
                  ·
                    refine ⟨7393432676026043138281789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 630906255020889014466712661 7393432676026043138281789)
                    ·
                      refine ⟨2772537253509766176855671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7393432676026043138281789 2772537253509766176855671)
                      ·
                        rfl

theorem cell23_5399497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 8, 3].length) (baseStart_5399497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399497 prefixEnd_5399497 := by exact prefixLift 5399497
  have htrace : WordTrace (prefixWord ++ tailWord_5399497) baseStart_5399497 baseEnd_5399497 := by
    simpa [prefixWord, tailWord_5399497, baseEnd_5399497] using wordTrace_append hprefix tailTrace_5399497
  have hstable : (prefixWord ++ tailWord_5399497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399497).length < 2 ^ (prefixWord ++ tailWord_5399497).sum := by decide
  have hdescent : baseEnd_5399497 < baseStart_5399497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399522 : List Nat := [3, 3, 3, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_5399522 : Nat := 118140960795 + 5399522 * 2 ^ 59
def prefixEnd_5399522 : Nat := 4983230072969 + 3 ^ 40 * 5399522 * 2
def baseEnd_5399522 : Nat := 2772550090526128579043057

theorem tailTrace_5399522 : CollatzResearch.WordTrace tailWord_5399522 prefixEnd_5399522 2772550090526128579043057 := by
  unfold tailWord_5399522
  simp only [CollatzResearch.WordTrace]
  refine ⟨49234186586115358446352205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131291164229640955856939213 49234186586115358446352205)
  ·
    refine ⟨18462819969793259417382077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49234186586115358446352205 18462819969793259417382077)
    ·
      refine ⟨6923557488672472281518279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18462819969793259417382077 6923557488672472281518279)
      ·
        refine ⟨10385336233008708422277419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6923557488672472281518279 10385336233008708422277419)
        ·
          refine ⟨15578004349513062633416129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10385336233008708422277419 15578004349513062633416129)
          ·
            refine ⟨11683503262134796975062097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15578004349513062633416129 11683503262134796975062097)
            ·
              refine ⟨8762627446601097731296573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11683503262134796975062097 8762627446601097731296573)
              ·
                refine ⟨3285985292475411649236215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8762627446601097731296573 3285985292475411649236215)
                ·
                  refine ⟨4928977938713117473854323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3285985292475411649236215 4928977938713117473854323)
                  ·
                    refine ⟨7393466908069676210781485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4928977938713117473854323 7393466908069676210781485)
                    ·
                      refine ⟨2772550090526128579043057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7393466908069676210781485 2772550090526128579043057)
                      ·
                        rfl

theorem cell23_5399522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_5399522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399522 prefixEnd_5399522 := by exact prefixLift 5399522
  have htrace : WordTrace (prefixWord ++ tailWord_5399522) baseStart_5399522 baseEnd_5399522 := by
    simpa [prefixWord, tailWord_5399522, baseEnd_5399522] using wordTrace_append hprefix tailTrace_5399522
  have hstable : (prefixWord ++ tailWord_5399522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399522).length < 2 ^ (prefixWord ++ tailWord_5399522).sum := by decide
  have hdescent : baseEnd_5399522 < baseStart_5399522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399525 : List Nat := [1, 3, 1, 6, 1, 2, 2, 1, 1, 5]
def baseStart_5399525 : Nat := 118140960795 + 5399525 * 2 ^ 59
def prefixEnd_5399525 : Nat := 4983230072969 + 3 ^ 40 * 5399525 * 2
def baseEnd_5399525 : Nat := 924183876989364022435181

theorem tailTrace_5399525 : CollatzResearch.WordTrace tailWord_5399525 prefixEnd_5399525 924183876989364022435181 := by
  unfold tailWord_5399525
  simp only [CollatzResearch.WordTrace]
  refine ⟨196936855763450565297768029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131291237175633710198512019 196936855763450565297768029)
  ·
    refine ⟨73851320911293961986663011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196936855763450565297768029 73851320911293961986663011)
    ·
      refine ⟨110776981366940942979994517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73851320911293961986663011 110776981366940942979994517)
      ·
        refine ⟨5192671001575356702187243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 110776981366940942979994517 5192671001575356702187243)
        ·
          refine ⟨7789006502363035053280865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5192671001575356702187243 7789006502363035053280865)
          ·
            refine ⟨5841754876772276289960649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7789006502363035053280865 5841754876772276289960649)
            ·
              refine ⟨4381316157579207217470487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5841754876772276289960649 4381316157579207217470487)
              ·
                refine ⟨6571974236368810826205731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4381316157579207217470487 6571974236368810826205731)
                ·
                  refine ⟨9857961354553216239308597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6571974236368810826205731 9857961354553216239308597)
                  ·
                    refine ⟨924183876989364022435181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9857961354553216239308597 924183876989364022435181)
                    ·
                      rfl

theorem cell23_5399525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 1, 5].length) (baseStart_5399525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399525 prefixEnd_5399525 := by exact prefixLift 5399525
  have htrace : WordTrace (prefixWord ++ tailWord_5399525) baseStart_5399525 baseEnd_5399525 := by
    simpa [prefixWord, tailWord_5399525, baseEnd_5399525] using wordTrace_append hprefix tailTrace_5399525
  have hstable : (prefixWord ++ tailWord_5399525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399525).length < 2 ^ (prefixWord ++ tailWord_5399525).sum := by decide
  have hdescent : baseEnd_5399525 < baseStart_5399525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399534 : List Nat := [4, 1, 2, 1, 4, 1, 10]
def baseStart_5399534 : Nat := 118140960795 + 5399534 * 2 ^ 59
def prefixEnd_5399534 : Nat := 4983230072969 + 3 ^ 40 * 5399534 * 2
def baseEnd_5399534 : Nat := 34229089534493611507321

theorem tailTrace_5399534 : CollatzResearch.WordTrace tailWord_5399534 prefixEnd_5399534 34229089534493611507321 := by
  unfold tailWord_5399534
  simp only [CollatzResearch.WordTrace]
  refine ⟨24617148002552244979355707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131291456013611973223230437 24617148002552244979355707)
  ·
    refine ⟨36925722003828367469033561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24617148002552244979355707 36925722003828367469033561)
    ·
      refine ⟨27694291502871275601775171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36925722003828367469033561 27694291502871275601775171)
      ·
        refine ⟨41541437254306913402662757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27694291502871275601775171 41541437254306913402662757)
        ·
          refine ⟨7789019485182546262999267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41541437254306913402662757 7789019485182546262999267)
          ·
            refine ⟨11683529227773819394498901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7789019485182546262999267 11683529227773819394498901)
            ·
              refine ⟨34229089534493611507321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11683529227773819394498901 34229089534493611507321)
              ·
                rfl

theorem cell23_5399534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 10].length) (baseStart_5399534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399534 prefixEnd_5399534 := by exact prefixLift 5399534
  have htrace : WordTrace (prefixWord ++ tailWord_5399534) baseStart_5399534 baseEnd_5399534 := by
    simpa [prefixWord, tailWord_5399534, baseEnd_5399534] using wordTrace_append hprefix tailTrace_5399534
  have hstable : (prefixWord ++ tailWord_5399534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399534).length < 2 ^ (prefixWord ++ tailWord_5399534).sum := by decide
  have hdescent : baseEnd_5399534 < baseStart_5399534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399538 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 4, 4]
def baseStart_5399538 : Nat := 118140960795 + 5399538 * 2 ^ 59
def prefixEnd_5399538 : Nat := 4983230072969 + 3 ^ 40 * 5399538 * 2
def baseEnd_5399538 : Nat := 924186102072200172147661

theorem tailTrace_5399538 : CollatzResearch.WordTrace tailWord_5399538 prefixEnd_5399538 924186102072200172147661 := by
  unfold tailWord_5399538
  simp only [CollatzResearch.WordTrace]
  refine ⟨49234332478100867129497817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131291553274935645678660845 49234332478100867129497817)
  ·
    refine ⟨36925749358575650347123363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49234332478100867129497817 36925749358575650347123363)
    ·
      refine ⟨55388624037863475520685045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36925749358575650347123363 55388624037863475520685045)
      ·
        refine ⟨5192683503549700830064223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55388624037863475520685045 5192683503549700830064223)
        ·
          refine ⟨7789025255324551245096335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5192683503549700830064223 7789025255324551245096335)
          ·
            refine ⟨11683537882986826867644503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7789025255324551245096335 11683537882986826867644503)
            ·
              refine ⟨17525306824480240301466755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11683537882986826867644503 17525306824480240301466755)
              ·
                refine ⟨26287960236720360452200133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17525306824480240301466755 26287960236720360452200133)
                ·
                  refine ⟨4928992544385067584787525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26287960236720360452200133 4928992544385067584787525)
                  ·
                    refine ⟨924186102072200172147661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4928992544385067584787525 924186102072200172147661)
                    ·
                      rfl

theorem cell23_5399538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_5399538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399538 prefixEnd_5399538 := by exact prefixLift 5399538
  have htrace : WordTrace (prefixWord ++ tailWord_5399538) baseStart_5399538 baseEnd_5399538 := by
    simpa [prefixWord, tailWord_5399538, baseEnd_5399538] using wordTrace_append hprefix tailTrace_5399538
  have hstable : (prefixWord ++ tailWord_5399538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399538).length < 2 ^ (prefixWord ++ tailWord_5399538).sum := by decide
  have hdescent : baseEnd_5399538 < baseStart_5399538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399561 : List Nat := [1, 2, 1, 1, 3, 1, 1, 7, 2, 1, 3]
def baseStart_5399561 : Nat := 118140960795 + 5399561 * 2 ^ 59
def prefixEnd_5399561 : Nat := 4983230072969 + 3 ^ 40 * 5399561 * 2
def baseEnd_5399561 : Nat := 2772570116271653926455377

theorem tailTrace_5399561 : CollatzResearch.WordTrace tailWord_5399561 prefixEnd_5399561 2772570116271653926455377 := by
  unfold tailWord_5399561
  simp only [CollatzResearch.WordTrace]
  refine ⟨196938168791320143446078537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131292112527546762297385691 196938168791320143446078537)
  ·
    refine ⟨147703626593490107584558903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196938168791320143446078537 147703626593490107584558903)
    ·
      refine ⟨221555439890235161376838355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147703626593490107584558903 221555439890235161376838355)
      ·
        refine ⟨332333159835352742065257533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221555439890235161376838355 332333159835352742065257533)
        ·
          refine ⟨124624934938257278274471575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332333159835352742065257533 124624934938257278274471575)
          ·
            refine ⟨186937402407385917411707363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124624934938257278274471575 186937402407385917411707363)
            ·
              refine ⟨280406103611078876117561045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186937402407385917411707363 280406103611078876117561045)
              ·
                refine ⟨6572018053384661159005337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 280406103611078876117561045 6572018053384661159005337)
                ·
                  refine ⟨4929013540038495869254003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6572018053384661159005337 4929013540038495869254003)
                  ·
                    refine ⟨7393520310057743803881005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4929013540038495869254003 7393520310057743803881005)
                    ·
                      refine ⟨2772570116271653926455377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7393520310057743803881005 2772570116271653926455377)
                      ·
                        rfl

theorem cell23_5399561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 1, 3].length) (baseStart_5399561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399561 prefixEnd_5399561 := by exact prefixLift 5399561
  have htrace : WordTrace (prefixWord ++ tailWord_5399561) baseStart_5399561 baseEnd_5399561 := by
    simpa [prefixWord, tailWord_5399561, baseEnd_5399561] using wordTrace_append hprefix tailTrace_5399561
  have hstable : (prefixWord ++ tailWord_5399561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399561).length < 2 ^ (prefixWord ++ tailWord_5399561).sum := by decide
  have hdescent : baseEnd_5399561 < baseStart_5399561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399577 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 1, 8]
def baseStart_5399577 : Nat := 118140960795 + 5399577 * 2 ^ 59
def prefixEnd_5399577 : Nat := 4983230072969 + 3 ^ 40 * 5399577 * 2
def baseEnd_5399577 : Nat := 924192777320708621285101

theorem tailTrace_5399577 : CollatzResearch.WordTrace tailWord_5399577 prefixEnd_5399577 924192777320708621285101 := by
  unfold tailWord_5399577
  simp only [CollatzResearch.WordTrace]
  refine ⟨196938752359262178178660985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131292501572841452119107323 196938752359262178178660985)
  ·
    refine ⟨147704064269446633633995739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196938752359262178178660985 147704064269446633633995739)
    ·
      refine ⟨221556096404169950450993609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147704064269446633633995739 221556096404169950450993609)
      ·
        refine ⟨166167072303127462838245207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221556096404169950450993609 166167072303127462838245207)
        ·
          refine ⟨249250608454691194257367811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166167072303127462838245207 249250608454691194257367811)
          ·
            refine ⟨373875912682036791386051717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249250608454691194257367811 373875912682036791386051717)
            ·
              refine ⟨70101733627881898384884697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 373875912682036791386051717 70101733627881898384884697)
              ·
                refine ⟨52576300220911423788663523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70101733627881898384884697 52576300220911423788663523)
                ·
                  refine ⟨78864450331367135682995285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52576300220911423788663523 78864450331367135682995285)
                  ·
                    refine ⟨924192777320708621285101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78864450331367135682995285 924192777320708621285101)
                    ·
                      rfl

theorem cell23_5399577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 8].length) (baseStart_5399577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399577 prefixEnd_5399577 := by exact prefixLift 5399577
  have htrace : WordTrace (prefixWord ++ tailWord_5399577) baseStart_5399577 baseEnd_5399577 := by
    simpa [prefixWord, tailWord_5399577, baseEnd_5399577] using wordTrace_append hprefix tailTrace_5399577
  have hstable : (prefixWord ++ tailWord_5399577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399577).length < 2 ^ (prefixWord ++ tailWord_5399577).sum := by decide
  have hdescent : baseEnd_5399577 < baseStart_5399577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399622 : List Nat := [6, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_5399622 : Nat := 118140960795 + 5399622 * 2 ^ 59
def prefixEnd_5399622 : Nat := 4983230072969 + 3 ^ 40 * 5399622 * 2
def baseEnd_5399622 : Nat := 2772601438591578187792597

theorem tailTrace_5399622 : CollatzResearch.WordTrace tailWord_5399622 prefixEnd_5399622 2772601438591578187792597 := by
  unfold tailWord_5399622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6154387301378098464501535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 131293595762732767242699413 6154387301378098464501535)
  ·
    refine ⟨9231580952067147696752303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6154387301378098464501535 9231580952067147696752303)
    ·
      refine ⟨13847371428100721545128455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9231580952067147696752303 13847371428100721545128455)
      ·
        refine ⟨20771057142151082317692683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13847371428100721545128455 20771057142151082317692683)
        ·
          refine ⟨31156585713226623476539025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20771057142151082317692683 31156585713226623476539025)
          ·
            refine ⟨23367439284919967607404269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31156585713226623476539025 23367439284919967607404269)
            ·
              refine ⟨8762789731844987852776601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23367439284919967607404269 8762789731844987852776601)
              ·
                refine ⟨6572092298883740889582451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8762789731844987852776601 6572092298883740889582451)
                ·
                  refine ⟨9858138448325611334373677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6572092298883740889582451 9858138448325611334373677)
                  ·
                    refine ⟨3696801918122104250390129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9858138448325611334373677 3696801918122104250390129)
                    ·
                      refine ⟨2772601438591578187792597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3696801918122104250390129 2772601438591578187792597)
                      ·
                        rfl

theorem cell23_5399622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_5399622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399622 prefixEnd_5399622 := by exact prefixLift 5399622
  have htrace : WordTrace (prefixWord ++ tailWord_5399622) baseStart_5399622 baseEnd_5399622 := by
    simpa [prefixWord, tailWord_5399622, baseEnd_5399622] using wordTrace_append hprefix tailTrace_5399622
  have hstable : (prefixWord ++ tailWord_5399622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399622).length < 2 ^ (prefixWord ++ tailWord_5399622).sum := by decide
  have hdescent : baseEnd_5399622 < baseStart_5399622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399658 : List Nat := [3, 1, 3, 2, 2, 2, 1, 4, 5]
def baseStart_5399658 : Nat := 118140960795 + 5399658 * 2 ^ 59
def prefixEnd_5399658 : Nat := 4983230072969 + 3 ^ 40 * 5399658 * 2
def baseEnd_5399658 : Nat := 308068880432793338549159

theorem tailTrace_5399658 : CollatzResearch.WordTrace tailWord_5399658 prefixEnd_5399658 308068880432793338549159 := by
  unfold tailWord_5399658
  simp only [CollatzResearch.WordTrace]
  refine ⟨49235426667992182253089907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131294471114645819341573085 49235426667992182253089907)
  ·
    refine ⟨73853140001988273379634861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49235426667992182253089907 73853140001988273379634861)
    ·
      refine ⟨27694927500745602517363073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73853140001988273379634861 27694927500745602517363073)
      ·
        refine ⟨20771195625559201888022305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27694927500745602517363073 20771195625559201888022305)
        ·
          refine ⟨15578396719169401416016729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20771195625559201888022305 15578396719169401416016729)
          ·
            refine ⟨11683797539377051062012547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15578396719169401416016729 11683797539377051062012547)
            ·
              refine ⟨17525696309065576593018821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11683797539377051062012547 17525696309065576593018821)
              ·
                refine ⟨3286068057949795611191029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17525696309065576593018821 3286068057949795611191029)
                ·
                  refine ⟨308068880432793338549159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3286068057949795611191029 308068880432793338549159)
                  ·
                    rfl

theorem cell23_5399658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 5].length) (baseStart_5399658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399658 prefixEnd_5399658 := by exact prefixLift 5399658
  have htrace : WordTrace (prefixWord ++ tailWord_5399658) baseStart_5399658 baseEnd_5399658 := by
    simpa [prefixWord, tailWord_5399658, baseEnd_5399658] using wordTrace_append hprefix tailTrace_5399658
  have hstable : (prefixWord ++ tailWord_5399658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399658).length < 2 ^ (prefixWord ++ tailWord_5399658).sum := by decide
  have hdescent : baseEnd_5399658 < baseStart_5399658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399664 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 5]
def baseStart_5399664 : Nat := 118140960795 + 5399664 * 2 ^ 59
def prefixEnd_5399664 : Nat := 4983230072969 + 3 ^ 40 * 5399664 * 2
def baseEnd_5399664 : Nat := 2772623004779067023467403

theorem tailTrace_5399664 : CollatzResearch.WordTrace tailWord_5399664 prefixEnd_5399664 2772623004779067023467403 := by
  unfold tailWord_5399664
  simp only [CollatzResearch.WordTrace]
  refine ⟨98470962754973496018539023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131294617006631328024718697 98470962754973496018539023)
  ·
    refine ⟨147706444132460244027808535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98470962754973496018539023 147706444132460244027808535)
    ·
      refine ⟨221559666198690366041712803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147706444132460244027808535 221559666198690366041712803)
      ·
        refine ⟨332339499298035549062569205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221559666198690366041712803 332339499298035549062569205)
        ·
          refine ⟨31156828059190832724615863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 332339499298035549062569205 31156828059190832724615863)
          ·
            refine ⟨46735242088786249086923795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31156828059190832724615863 46735242088786249086923795)
            ·
              refine ⟨70102863133179373630385693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46735242088786249086923795 70102863133179373630385693)
              ·
                refine ⟨26288573674942265111394635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70102863133179373630385693 26288573674942265111394635)
                ·
                  refine ⟨39432860512413397667091953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26288573674942265111394635 39432860512413397667091953)
                  ·
                    refine ⟨29574645384310048250318965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39432860512413397667091953 29574645384310048250318965)
                    ·
                      refine ⟨2772623004779067023467403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29574645384310048250318965 2772623004779067023467403)
                      ·
                        rfl

theorem cell23_5399664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_5399664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399664 prefixEnd_5399664 := by exact prefixLift 5399664
  have htrace : WordTrace (prefixWord ++ tailWord_5399664) baseStart_5399664 baseEnd_5399664 := by
    simpa [prefixWord, tailWord_5399664, baseEnd_5399664] using wordTrace_append hprefix tailTrace_5399664
  have hstable : (prefixWord ++ tailWord_5399664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399664).length < 2 ^ (prefixWord ++ tailWord_5399664).sum := by decide
  have hdescent : baseEnd_5399664 < baseStart_5399664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399708 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 2, 4, 2]
def baseStart_5399708 : Nat := 118140960795 + 5399708 * 2 ^ 59
def prefixEnd_5399708 : Nat := 4983230072969 + 3 ^ 40 * 5399708 * 2
def baseEnd_5399708 : Nat := 2772645597927864851317201

theorem tailTrace_5399708 : CollatzResearch.WordTrace tailWord_5399708 prefixEnd_5399708 2772645597927864851317201 := by
  unfold tailWord_5399708
  simp only [CollatzResearch.WordTrace]
  refine ⟨98471765160893793775839889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131295686881191725034453185 98471765160893793775839889)
  ·
    refine ⟨73853823870670345331879917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98471765160893793775839889 73853823870670345331879917)
    ·
      refine ⟨27695183951501379499454969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73853823870670345331879917 27695183951501379499454969)
      ·
        refine ⟨20771387963626034624591227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27695183951501379499454969 20771387963626034624591227)
        ·
          refine ⟨31157081945439051936886841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20771387963626034624591227 31157081945439051936886841)
          ·
            refine ⟨23367811459079288952665131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31157081945439051936886841 23367811459079288952665131)
            ·
              refine ⟨35051717188618933428997697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23367811459079288952665131 35051717188618933428997697)
              ·
                refine ⟨26288787891464200071748273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35051717188618933428997697 26288787891464200071748273)
                ·
                  refine ⟨19716590918598150053811205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26288787891464200071748273 19716590918598150053811205)
                  ·
                    refine ⟨3696860797237153135089601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19716590918598150053811205 3696860797237153135089601)
                    ·
                      refine ⟨2772645597927864851317201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3696860797237153135089601 2772645597927864851317201)
                      ·
                        rfl

theorem cell23_5399708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_5399708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399708 prefixEnd_5399708 := by exact prefixLift 5399708
  have htrace : WordTrace (prefixWord ++ tailWord_5399708) baseStart_5399708 baseEnd_5399708 := by
    simpa [prefixWord, tailWord_5399708, baseEnd_5399708] using wordTrace_append hprefix tailTrace_5399708
  have hstable : (prefixWord ++ tailWord_5399708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399708).length < 2 ^ (prefixWord ++ tailWord_5399708).sum := by decide
  have hdescent : baseEnd_5399708 < baseStart_5399708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399775 : List Nat := [1, 1, 2, 3, 2, 1, 2, 6, 1, 1, 3]
def baseStart_5399775 : Nat := 118140960795 + 5399775 * 2 ^ 59
def prefixEnd_5399775 : Nat := 4983230072969 + 3 ^ 40 * 5399775 * 2
def baseEnd_5399775 : Nat := 2772680001131716089179393

theorem tailTrace_5399775 : CollatzResearch.WordTrace tailWord_5399775 prefixEnd_5399775 2772680001131716089179393 := by
  unfold tailWord_5399775
  simp only [CollatzResearch.WordTrace]
  refine ⟨196945974012544857994368779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131297316008363238662912519 196945974012544857994368779)
  ·
    refine ⟨295418961018817286991553169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196945974012544857994368779 295418961018817286991553169)
    ·
      refine ⟨221564220764112965243664877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295418961018817286991553169 221564220764112965243664877)
      ·
        refine ⟨83086582786542361966374329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221564220764112965243664877 83086582786542361966374329)
        ·
          refine ⟨62314937089906771474780747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83086582786542361966374329 62314937089906771474780747)
          ·
            refine ⟨93472405634860157212171121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62314937089906771474780747 93472405634860157212171121)
            ·
              refine ⟨70104304226145117909128341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93472405634860157212171121 70104304226145117909128341)
              ·
                refine ⟨3286139260600552401990391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70104304226145117909128341 3286139260600552401990391)
                ·
                  refine ⟨4929208890900828602985587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3286139260600552401990391 4929208890900828602985587)
                  ·
                    refine ⟨7393813336351242904478381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4929208890900828602985587 7393813336351242904478381)
                    ·
                      refine ⟨2772680001131716089179393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7393813336351242904478381 2772680001131716089179393)
                      ·
                        rfl

theorem cell23_5399775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 1, 1, 3].length) (baseStart_5399775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399775 prefixEnd_5399775 := by exact prefixLift 5399775
  have htrace : WordTrace (prefixWord ++ tailWord_5399775) baseStart_5399775 baseEnd_5399775 := by
    simpa [prefixWord, tailWord_5399775, baseEnd_5399775] using wordTrace_append hprefix tailTrace_5399775
  have hstable : (prefixWord ++ tailWord_5399775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399775).length < 2 ^ (prefixWord ++ tailWord_5399775).sum := by decide
  have hdescent : baseEnd_5399775 < baseStart_5399775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399811 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 4]
def baseStart_5399811 : Nat := 118140960795 + 5399811 * 2 ^ 59
def prefixEnd_5399811 : Nat := 4983230072969 + 3 ^ 40 * 5399811 * 2
def baseEnd_5399811 : Nat := 2772698486435277948329227

theorem tailTrace_5399811 : CollatzResearch.WordTrace tailWord_5399811 prefixEnd_5399811 2772698486435277948329227 := by
  unfold tailWord_5399811
  simp only [CollatzResearch.WordTrace]
  refine ⟨196947287040414436142679287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131298191360276290761786191 196947287040414436142679287)
  ·
    refine ⟨295420930560621654214018931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196947287040414436142679287 295420930560621654214018931)
    ·
      refine ⟨443131395840932481321028397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295420930560621654214018931 443131395840932481321028397)
      ·
        refine ⟨166174273440349680495385649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 443131395840932481321028397 166174273440349680495385649)
        ·
          refine ⟨124630705080262260371539237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166174273440349680495385649 124630705080262260371539237)
          ·
            refine ⟨23368257202549173819663607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124630705080262260371539237 23368257202549173819663607)
            ·
              refine ⟨35052385803823760729495411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23368257202549173819663607 35052385803823760729495411)
              ·
                refine ⟨52578578705735641094243117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35052385803823760729495411 52578578705735641094243117)
                ·
                  refine ⟨19716967014650865410341169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52578578705735641094243117 19716967014650865410341169)
                  ·
                    refine ⟨14787725260988149057755877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19716967014650865410341169 14787725260988149057755877)
                    ·
                      refine ⟨2772698486435277948329227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14787725260988149057755877 2772698486435277948329227)
                      ·
                        rfl

theorem cell23_5399811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_5399811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399811 prefixEnd_5399811 := by exact prefixLift 5399811
  have htrace : WordTrace (prefixWord ++ tailWord_5399811) baseStart_5399811 baseEnd_5399811 := by
    simpa [prefixWord, tailWord_5399811, baseEnd_5399811] using wordTrace_append hprefix tailTrace_5399811
  have hstable : (prefixWord ++ tailWord_5399811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399811).length < 2 ^ (prefixWord ++ tailWord_5399811).sum := by decide
  have hdescent : baseEnd_5399811 < baseStart_5399811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399821 : List Nat := [1, 7, 15]
def baseStart_5399821 : Nat := 118140960795 + 5399821 * 2 ^ 59
def prefixEnd_5399821 : Nat := 4983230072969 + 3 ^ 40 * 5399821 * 2
def baseEnd_5399821 : Nat := 422603813632346122421

theorem tailTrace_5399821 : CollatzResearch.WordTrace tailWord_5399821 prefixEnd_5399821 422603813632346122421 := by
  unfold tailWord_5399821
  simp only [CollatzResearch.WordTrace]
  refine ⟨196947651770378207850543317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131298434513585471900362211 196947651770378207850543317)
  ·
    refine ⟨4615960588368239246497109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 196947651770378207850543317 4615960588368239246497109)
    ·
      refine ⟨422603813632346122421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 4615960588368239246497109 422603813632346122421)
      ·
        rfl

theorem cell23_5399821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 15].length) (baseStart_5399821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399821 prefixEnd_5399821 := by exact prefixLift 5399821
  have htrace : WordTrace (prefixWord ++ tailWord_5399821) baseStart_5399821 baseEnd_5399821 := by
    simpa [prefixWord, tailWord_5399821, baseEnd_5399821] using wordTrace_append hprefix tailTrace_5399821
  have hstable : (prefixWord ++ tailWord_5399821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399821).length < 2 ^ (prefixWord ++ tailWord_5399821).sum := by decide
  have hdescent : baseEnd_5399821 < baseStart_5399821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399826 : List Nat := [3, 2, 4, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_5399826 : Nat := 118140960795 + 5399826 * 2 ^ 59
def prefixEnd_5399826 : Nat := 4983230072969 + 3 ^ 40 * 5399826 * 2
def baseEnd_5399826 : Nat := 2772706188645095389641659

theorem tailTrace_5399826 : CollatzResearch.WordTrace tailWord_5399826 prefixEnd_5399826 2772706188645095389641659 := by
  unfold tailWord_5399826
  simp only [CollatzResearch.WordTrace]
  refine ⟨49236958533840023426118833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131298556090240062469650221 49236958533840023426118833)
  ·
    refine ⟨36927718900380017569589125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49236958533840023426118833 36927718900380017569589125)
    ·
      refine ⟨6923947293821253294297961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36927718900380017569589125 6923947293821253294297961)
      ·
        refine ⟨5192960470365939970723471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6923947293821253294297961 5192960470365939970723471)
        ·
          refine ⟨7789440705548909956085207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5192960470365939970723471 7789440705548909956085207)
          ·
            refine ⟨11684161058323364934127811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7789440705548909956085207 11684161058323364934127811)
            ·
              refine ⟨17526241587485047401191717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11684161058323364934127811 17526241587485047401191717)
              ·
                refine ⟨3286170297653446387723447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17526241587485047401191717 3286170297653446387723447)
                ·
                  refine ⟨4929255446480169581585171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3286170297653446387723447 4929255446480169581585171)
                  ·
                    refine ⟨7393883169720254372377757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4929255446480169581585171 7393883169720254372377757)
                    ·
                      refine ⟨2772706188645095389641659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7393883169720254372377757 2772706188645095389641659)
                      ·
                        rfl

theorem cell23_5399826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_5399826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399826 prefixEnd_5399826 := by exact prefixLift 5399826
  have htrace : WordTrace (prefixWord ++ tailWord_5399826) baseStart_5399826 baseEnd_5399826 := by
    simpa [prefixWord, tailWord_5399826, baseEnd_5399826] using wordTrace_append hprefix tailTrace_5399826
  have hstable : (prefixWord ++ tailWord_5399826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399826).length < 2 ^ (prefixWord ++ tailWord_5399826).sum := by decide
  have hdescent : baseEnd_5399826 < baseStart_5399826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399881 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 2, 6]
def baseStart_5399881 : Nat := 118140960795 + 5399881 * 2 ^ 59
def prefixEnd_5399881 : Nat := 4983230072969 + 3 ^ 40 * 5399881 * 2
def baseEnd_5399881 : Nat := 924244810027030891484635

theorem tailTrace_5399881 : CollatzResearch.WordTrace tailWord_5399881 prefixEnd_5399881 924244810027030891484635 := by
  unfold tailWord_5399881
  simp only [CollatzResearch.WordTrace]
  refine ⟨196949840150160838097727497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131299893433440558731818331 196949840150160838097727497)
  ·
    refine ⟨147712380112620628573295623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196949840150160838097727497 147712380112620628573295623)
    ·
      refine ⟨221568570168930942859943435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147712380112620628573295623 221568570168930942859943435)
      ·
        refine ⟨332352855253396414289915153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221568570168930942859943435 332352855253396414289915153)
        ·
          refine ⟨249264641440047310717436365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332352855253396414289915153 249264641440047310717436365)
          ·
            refine ⟨93474240540017741519038637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249264641440047310717436365 93474240540017741519038637)
            ·
              refine ⟨35052840202506653069639489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93474240540017741519038637 35052840202506653069639489)
              ·
                refine ⟨26289630151879989802229617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35052840202506653069639489 26289630151879989802229617)
                ·
                  refine ⟨19717222613909992351672213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26289630151879989802229617 19717222613909992351672213)
                  ·
                    refine ⟨924244810027030891484635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19717222613909992351672213 924244810027030891484635)
                    ·
                      rfl

theorem cell23_5399881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 6].length) (baseStart_5399881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399881 prefixEnd_5399881 := by exact prefixLift 5399881
  have htrace : WordTrace (prefixWord ++ tailWord_5399881) baseStart_5399881 baseEnd_5399881 := by
    simpa [prefixWord, tailWord_5399881, baseEnd_5399881] using wordTrace_append hprefix tailTrace_5399881
  have hstable : (prefixWord ++ tailWord_5399881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399881).length < 2 ^ (prefixWord ++ tailWord_5399881).sum := by decide
  have hdescent : baseEnd_5399881 < baseStart_5399881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399925 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_5399925 : Nat := 118140960795 + 5399925 * 2 ^ 59
def prefixEnd_5399925 : Nat := 4983230072969 + 3 ^ 40 * 5399925 * 2
def baseEnd_5399925 : Nat := 2772757023229890502303703

theorem tailTrace_5399925 : CollatzResearch.WordTrace tailWord_5399925 prefixEnd_5399925 2772757023229890502303703 := by
  unfold tailWord_5399925
  simp only [CollatzResearch.WordTrace]
  refine ⟨196951444962001433612329229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131300963308000955741552819 196951444962001433612329229)
  ·
    refine ⟨73856791860750537604623461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196951444962001433612329229 73856791860750537604623461)
    ·
      refine ⟨13848148473890725800866899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73856791860750537604623461 13848148473890725800866899)
      ·
        refine ⟨20772222710836088701300349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13848148473890725800866899 20772222710836088701300349)
        ·
          refine ⟨7789583516563533262987631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20772222710836088701300349 7789583516563533262987631)
          ·
            refine ⟨11684375274845299894481447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7789583516563533262987631 11684375274845299894481447)
            ·
              refine ⟨17526562912267949841722171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11684375274845299894481447 17526562912267949841722171)
              ·
                refine ⟨26289844368401924762583257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17526562912267949841722171 26289844368401924762583257)
                ·
                  refine ⟨19717383276301443571937443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26289844368401924762583257 19717383276301443571937443)
                  ·
                    refine ⟨29576074914452165357906165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19717383276301443571937443 29576074914452165357906165)
                    ·
                      refine ⟨2772757023229890502303703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29576074914452165357906165 2772757023229890502303703)
                      ·
                        rfl

theorem cell23_5399925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_5399925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399925 prefixEnd_5399925 := by exact prefixLift 5399925
  have htrace : WordTrace (prefixWord ++ tailWord_5399925) baseStart_5399925 baseEnd_5399925 := by
    simpa [prefixWord, tailWord_5399925, baseEnd_5399925] using wordTrace_append hprefix tailTrace_5399925
  have hstable : (prefixWord ++ tailWord_5399925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399925).length < 2 ^ (prefixWord ++ tailWord_5399925).sum := by decide
  have hdescent : baseEnd_5399925 < baseStart_5399925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399945 : List Nat := [1, 2, 1, 1, 7, 2, 1, 1, 7]
def baseStart_5399945 : Nat := 118140960795 + 5399945 * 2 ^ 59
def prefixEnd_5399945 : Nat := 4983230072969 + 3 ^ 40 * 5399945 * 2
def baseEnd_5399945 : Nat := 308085254760331158228179

theorem tailTrace_5399945 : CollatzResearch.WordTrace tailWord_5399945 prefixEnd_5399945 308085254760331158228179 := by
  unfold tailWord_5399945
  simp only [CollatzResearch.WordTrace]
  refine ⟨196952174421928977028057289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131301449614619318018704859 196952174421928977028057289)
  ·
    refine ⟨147714130816446732771042967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196952174421928977028057289 147714130816446732771042967)
    ·
      refine ⟨221571196224670099156564451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147714130816446732771042967 221571196224670099156564451)
      ·
        refine ⟨332356794337005148734846677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221571196224670099156564451 332356794337005148734846677)
        ·
          refine ⟨7789612367273558173472969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 332356794337005148734846677 7789612367273558173472969)
          ·
            refine ⟨5842209275455168630104727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7789612367273558173472969 5842209275455168630104727)
            ·
              refine ⟨8763313913182752945157091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5842209275455168630104727 8763313913182752945157091)
              ·
                refine ⟨13144970869774129417735637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8763313913182752945157091 13144970869774129417735637)
                ·
                  refine ⟨308085254760331158228179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13144970869774129417735637 308085254760331158228179)
                  ·
                    rfl

theorem cell23_5399945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 7].length) (baseStart_5399945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399945 prefixEnd_5399945 := by exact prefixLift 5399945
  have htrace : WordTrace (prefixWord ++ tailWord_5399945) baseStart_5399945 baseEnd_5399945 := by
    simpa [prefixWord, tailWord_5399945, baseEnd_5399945] using wordTrace_append hprefix tailTrace_5399945
  have hstable : (prefixWord ++ tailWord_5399945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399945).length < 2 ^ (prefixWord ++ tailWord_5399945).sum := by decide
  have hdescent : baseEnd_5399945 < baseStart_5399945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399956 : List Nat := [2, 4, 2, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_5399956 : Nat := 118140960795 + 5399956 * 2 ^ 59
def prefixEnd_5399956 : Nat := 4983230072969 + 3 ^ 40 * 5399956 * 2
def baseEnd_5399956 : Nat := 2772772941130179881016061

theorem tailTrace_5399956 : CollatzResearch.WordTrace tailWord_5399956 prefixEnd_5399956 2772772941130179881016061 := by
  unfold tailWord_5399956
  simp only [CollatzResearch.WordTrace]
  refine ⟨98476287812444562953353861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131301717083259417271138481 98476287812444562953353861)
  ·
    refine ⟨18464303964833355553753849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98476287812444562953353861 18464303964833355553753849)
    ·
      refine ⟨13848227973625016665315387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18464303964833355553753849 13848227973625016665315387)
      ·
        refine ⟨20772341960437524997973081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13848227973625016665315387 20772341960437524997973081)
        ·
          refine ⟨15579256470328143748479811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20772341960437524997973081 15579256470328143748479811)
          ·
            refine ⟨23368884705492215622719717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15579256470328143748479811 23368884705492215622719717)
            ·
              refine ⟨4381665882279790429259947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23368884705492215622719717 4381665882279790429259947)
              ·
                refine ⟨6572498823419685643889921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4381665882279790429259947 6572498823419685643889921)
                ·
                  refine ⟨4929374117564764232917441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6572498823419685643889921 4929374117564764232917441)
                  ·
                    refine ⟨3697030588173573174688081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4929374117564764232917441 3697030588173573174688081)
                    ·
                      refine ⟨2772772941130179881016061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3697030588173573174688081 2772772941130179881016061)
                      ·
                        rfl

theorem cell23_5399956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_5399956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399956 prefixEnd_5399956 := by exact prefixLift 5399956
  have htrace : WordTrace (prefixWord ++ tailWord_5399956) baseStart_5399956 baseEnd_5399956 := by
    simpa [prefixWord, tailWord_5399956, baseEnd_5399956] using wordTrace_append hprefix tailTrace_5399956
  have hstable : (prefixWord ++ tailWord_5399956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399956).length < 2 ^ (prefixWord ++ tailWord_5399956).sum := by decide
  have hdescent : baseEnd_5399956 < baseStart_5399956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399975 : List Nat := [1, 1, 6, 1, 1, 1, 4, 1, 2, 5]
def baseStart_5399975 : Nat := 118140960795 + 5399975 * 2 ^ 59
def prefixEnd_5399975 : Nat := 4983230072969 + 3 ^ 40 * 5399975 * 2
def baseEnd_5399975 : Nat := 924260899087538435559491

theorem tailTrace_5399975 : CollatzResearch.WordTrace tailWord_5399975 prefixEnd_5399975 924260899087538435559491 := by
  unfold tailWord_5399975
  simp only [CollatzResearch.WordTrace]
  refine ⟨196953268611820292151649379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131302179074546861434432919 196953268611820292151649379)
  ·
    refine ⟨295429902917730438227474069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196953268611820292151649379 295429902917730438227474069)
    ·
      refine ⟨13848276699268614291912847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 295429902917730438227474069 13848276699268614291912847)
      ·
        refine ⟨20772415048902921437869271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13848276699268614291912847 20772415048902921437869271)
        ·
          refine ⟨31158622573354382156803907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20772415048902921437869271 31158622573354382156803907)
          ·
            refine ⟨46737933860031573235205861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31158622573354382156803907 46737933860031573235205861)
            ·
              refine ⟨8763362598755919981601099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46737933860031573235205861 8763362598755919981601099)
              ·
                refine ⟨13145043898133879972401649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8763362598755919981601099 13145043898133879972401649)
                ·
                  refine ⟨9858782923600409979301237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13145043898133879972401649 9858782923600409979301237)
                  ·
                    refine ⟨924260899087538435559491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9858782923600409979301237 924260899087538435559491)
                    ·
                      rfl

theorem cell23_5399975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_5399975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399975 prefixEnd_5399975 := by exact prefixLift 5399975
  have htrace : WordTrace (prefixWord ++ tailWord_5399975) baseStart_5399975 baseEnd_5399975 := by
    simpa [prefixWord, tailWord_5399975, baseEnd_5399975] using wordTrace_append hprefix tailTrace_5399975
  have hstable : (prefixWord ++ tailWord_5399975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399975).length < 2 ^ (prefixWord ++ tailWord_5399975).sum := by decide
  have hdescent : baseEnd_5399975 < baseStart_5399975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399996 : List Nat := [2, 2, 2, 4, 3, 1, 2, 2, 5]
def baseStart_5399996 : Nat := 118140960795 + 5399996 * 2 ^ 59
def prefixEnd_5399996 : Nat := 4983230072969 + 3 ^ 40 * 5399996 * 2
def baseEnd_5399996 : Nat := 308088164484039969390653

theorem tailTrace_5399996 : CollatzResearch.WordTrace tailWord_5399996 prefixEnd_5399996 308088164484039969390653 := by
  unfold tailWord_5399996
  simp only [CollatzResearch.WordTrace]
  refine ⟨98477017272372106369081921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131302689696496141825442561 98477017272372106369081921)
  ·
    refine ⟨73857762954279079776811441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98477017272372106369081921 73857762954279079776811441)
    ·
      refine ⟨55393322215709309832608581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73857762954279079776811441 55393322215709309832608581)
      ·
        refine ⟨10386247915445495593614109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55393322215709309832608581 10386247915445495593614109)
        ·
          refine ⟨3894842968292060847605291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10386247915445495593614109 3894842968292060847605291)
          ·
            refine ⟨5842264452438091271407937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3894842968292060847605291 5842264452438091271407937)
            ·
              refine ⟨4381698339328568453555953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5842264452438091271407937 4381698339328568453555953)
              ·
                refine ⟨3286273754496426340166965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4381698339328568453555953 3286273754496426340166965)
                ·
                  refine ⟨308088164484039969390653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3286273754496426340166965 308088164484039969390653)
                  ·
                    rfl

theorem cell23_5399996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 5].length) (baseStart_5399996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399996 prefixEnd_5399996 := by exact prefixLift 5399996
  have htrace : WordTrace (prefixWord ++ tailWord_5399996) baseStart_5399996 baseEnd_5399996 := by
    simpa [prefixWord, tailWord_5399996, baseEnd_5399996] using wordTrace_append hprefix tailTrace_5399996
  have hstable : (prefixWord ++ tailWord_5399996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399996).length < 2 ^ (prefixWord ++ tailWord_5399996).sum := by decide
  have hdescent : baseEnd_5399996 < baseStart_5399996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5399998 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_5399998 : Nat := 118140960795 + 5399998 * 2 ^ 59
def prefixEnd_5399998 : Nat := 4983230072969 + 3 ^ 40 * 5399998 * 2
def baseEnd_5399998 : Nat := 2772794507317668716690867

theorem tailTrace_5399998 : CollatzResearch.WordTrace tailWord_5399998 prefixEnd_5399998 2772794507317668716690867 := by
  unfold tailWord_5399998
  simp only [CollatzResearch.WordTrace]
  refine ⟨24619263436342120884967081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131302738327157978053157765 24619263436342120884967081)
  ·
    refine ⟨18464447577256590663725311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24619263436342120884967081 18464447577256590663725311)
    ·
      refine ⟨27696671365884885995587967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18464447577256590663725311 27696671365884885995587967)
      ·
        refine ⟨41545007048827328993381951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27696671365884885995587967 41545007048827328993381951)
        ·
          refine ⟨62317510573240993490072927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41545007048827328993381951 62317510573240993490072927)
          ·
            refine ⟨93476265859861490235109391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62317510573240993490072927 93476265859861490235109391)
            ·
              refine ⟨140214398789792235352664087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93476265859861490235109391 140214398789792235352664087)
              ·
                refine ⟨210321598184688353028996131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140214398789792235352664087 210321598184688353028996131)
                ·
                  refine ⟨315482397277032529543494197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210321598184688353028996131 315482397277032529543494197)
                  ·
                    refine ⟨29576474744721799644702581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 315482397277032529543494197 29576474744721799644702581)
                    ·
                      refine ⟨2772794507317668716690867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29576474744721799644702581 2772794507317668716690867)
                      ·
                        rfl

theorem cell23_5399998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_5399998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5399998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5399998 prefixEnd_5399998 := by exact prefixLift 5399998
  have htrace : WordTrace (prefixWord ++ tailWord_5399998) baseStart_5399998 baseEnd_5399998 := by
    simpa [prefixWord, tailWord_5399998, baseEnd_5399998] using wordTrace_append hprefix tailTrace_5399998
  have hstable : (prefixWord ++ tailWord_5399998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5399998).length < 2 ^ (prefixWord ++ tailWord_5399998).sum := by decide
  have hdescent : baseEnd_5399998 < baseStart_5399998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5399998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400012 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 2, 4, 2]
def baseStart_5400012 : Nat := 118140960795 + 5400012 * 2 ^ 59
def prefixEnd_5400012 : Nat := 4983230072969 + 3 ^ 40 * 5400012 * 2
def baseEnd_5400012 : Nat := 2772801696046831661915803

theorem tailTrace_5400012 : CollatzResearch.WordTrace tailWord_5400012 prefixEnd_5400012 2772801696046831661915803 := by
  unfold tailWord_5400012
  simp only [CollatzResearch.WordTrace]
  refine ⟨98477309056343123735373145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131303078741790831647164193 98477309056343123735373145)
  ·
    refine ⟨73857981792257342801529859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98477309056343123735373145 73857981792257342801529859)
    ·
      refine ⟨110786972688386014202294789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73857981792257342801529859 110786972688386014202294789)
      ·
        refine ⟨20772557379072377662930273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110786972688386014202294789 20772557379072377662930273)
        ·
          refine ⟨15579418034304283247197705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20772557379072377662930273 15579418034304283247197705)
          ·
            refine ⟨11684563525728212435398279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15579418034304283247197705 11684563525728212435398279)
            ·
              refine ⟨17526845288592318653097419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11684563525728212435398279 17526845288592318653097419)
              ·
                refine ⟨26290267932888477979646129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17526845288592318653097419 26290267932888477979646129)
                ·
                  refine ⟨19717700949666358484734597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26290267932888477979646129 19717700949666358484734597)
                  ·
                    refine ⟨3697068928062442215887737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19717700949666358484734597 3697068928062442215887737)
                    ·
                      refine ⟨2772801696046831661915803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3697068928062442215887737 2772801696046831661915803)
                      ·
                        rfl

theorem cell23_5400012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_5400012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400012 prefixEnd_5400012 := by exact prefixLift 5400012
  have htrace : WordTrace (prefixWord ++ tailWord_5400012) baseStart_5400012 baseEnd_5400012 := by
    simpa [prefixWord, tailWord_5400012, baseEnd_5400012] using wordTrace_append hprefix tailTrace_5400012
  have hstable : (prefixWord ++ tailWord_5400012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400012).length < 2 ^ (prefixWord ++ tailWord_5400012).sum := by decide
  have hdescent : baseEnd_5400012 < baseStart_5400012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400022 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_5400022 : Nat := 118140960795 + 5400022 * 2 ^ 59
def prefixEnd_5400022 : Nat := 4983230072969 + 3 ^ 40 * 5400022 * 2
def baseEnd_5400022 : Nat := 924268943617792207596919

theorem tailTrace_5400022 : CollatzResearch.WordTrace tailWord_5400022 prefixEnd_5400022 924268943617792207596919 := by
  unfold tailWord_5400022
  simp only [CollatzResearch.WordTrace]
  refine ⟨12309686427665626198663145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131303321895100012785740213 12309686427665626198663145)
  ·
    refine ⟨9232264820749219648997359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12309686427665626198663145 9232264820749219648997359)
    ·
      refine ⟨13848397231123829473496039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9232264820749219648997359 13848397231123829473496039)
      ·
        refine ⟨20772595846685744210244059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13848397231123829473496039 20772595846685744210244059)
        ·
          refine ⟨31158893770028616315366089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20772595846685744210244059 31158893770028616315366089)
          ·
            refine ⟨23369170327521462236524567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31158893770028616315366089 23369170327521462236524567)
            ·
              refine ⟨35053755491282193354786851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23369170327521462236524567 35053755491282193354786851)
              ·
                refine ⟨52580633236923290032180277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35053755491282193354786851 52580633236923290032180277)
                ·
                  refine ⟨4929434365961558440516901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52580633236923290032180277 4929434365961558440516901)
                  ·
                    refine ⟨924268943617792207596919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4929434365961558440516901 924268943617792207596919)
                    ·
                      rfl

theorem cell23_5400022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_5400022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400022 prefixEnd_5400022 := by exact prefixLift 5400022
  have htrace : WordTrace (prefixWord ++ tailWord_5400022) baseStart_5400022 baseEnd_5400022 := by
    simpa [prefixWord, tailWord_5400022, baseEnd_5400022] using wordTrace_append hprefix tailTrace_5400022
  have hstable : (prefixWord ++ tailWord_5400022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400022).length < 2 ^ (prefixWord ++ tailWord_5400022).sum := by decide
  have hdescent : baseEnd_5400022 < baseStart_5400022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400039 : List Nat := [1, 1, 5, 2, 1, 3, 2, 3, 1, 4]
def baseStart_5400039 : Nat := 118140960795 + 5400039 * 2 ^ 59
def prefixEnd_5400039 : Nat := 4983230072969 + 3 ^ 40 * 5400039 * 2
def baseEnd_5400039 : Nat := 924271853341501018759393

theorem tailTrace_5400039 : CollatzResearch.WordTrace tailWord_5400039 prefixEnd_5400039 924271853341501018759393 := by
  unfold tailWord_5400039
  simp only [CollatzResearch.WordTrace]
  refine ⟨196955602883588431081979171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131303735255725620721319447 196955602883588431081979171)
  ·
    refine ⟨295433404325382646622968757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196955602883588431081979171 295433404325382646622968757)
    ·
      refine ⟨27696881655504623120903321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 295433404325382646622968757 27696881655504623120903321)
      ·
        refine ⟨20772661241628467340677491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27696881655504623120903321 20772661241628467340677491)
        ·
          refine ⟨31158991862442701011016237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20772661241628467340677491 31158991862442701011016237)
          ·
            refine ⟨11684621948416012879131089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31158991862442701011016237 11684621948416012879131089)
            ·
              refine ⟨8763466461312009659348317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11684621948416012879131089 8763466461312009659348317)
              ·
                refine ⟨3286299922992003622255619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8763466461312009659348317 3286299922992003622255619)
                ·
                  refine ⟨4929449884488005433383429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3286299922992003622255619 4929449884488005433383429)
                  ·
                    refine ⟨924271853341501018759393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4929449884488005433383429 924271853341501018759393)
                    ·
                      rfl

theorem cell23_5400039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_5400039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400039 prefixEnd_5400039 := by exact prefixLift 5400039
  have htrace : WordTrace (prefixWord ++ tailWord_5400039) baseStart_5400039 baseEnd_5400039 := by
    simpa [prefixWord, tailWord_5400039, baseEnd_5400039] using wordTrace_append hprefix tailTrace_5400039
  have hstable : (prefixWord ++ tailWord_5400039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400039).length < 2 ^ (prefixWord ++ tailWord_5400039).sum := by decide
  have hdescent : baseEnd_5400039 < baseStart_5400039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400095 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 4, 4]
def baseStart_5400095 : Nat := 118140960795 + 5400095 * 2 ^ 59
def prefixEnd_5400095 : Nat := 4983230072969 + 3 ^ 40 * 5400095 * 2
def baseEnd_5400095 : Nat := 924281438313718279059307

theorem tailTrace_5400095 : CollatzResearch.WordTrace tailWord_5400095 prefixEnd_5400095 924281438313718279059307 := by
  unfold tailWord_5400095
  simp only [CollatzResearch.WordTrace]
  refine ⟨196957645371385552646017739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131305096914257035097345159 196957645371385552646017739)
  ·
    refine ⟨295436468057078328969026609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196957645371385552646017739 295436468057078328969026609)
    ·
      refine ⟨221577351042808746726769957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295436468057078328969026609 221577351042808746726769957)
      ·
        refine ⟨41545753320526640011269367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221577351042808746726769957 41545753320526640011269367)
        ·
          refine ⟨62318629980789960016904051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41545753320526640011269367 62318629980789960016904051)
          ·
            refine ⟨93477944971184940025356077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62318629980789960016904051 93477944971184940025356077)
            ·
              refine ⟨35054229364194352509508529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93477944971184940025356077 35054229364194352509508529)
              ·
                refine ⟨26290672023145764382131397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35054229364194352509508529 26290672023145764382131397)
                ·
                  refine ⟨4929501004339830821649637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26290672023145764382131397 4929501004339830821649637)
                  ·
                    refine ⟨924281438313718279059307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4929501004339830821649637 924281438313718279059307)
                    ·
                      rfl

theorem cell23_5400095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 4].length) (baseStart_5400095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400095 prefixEnd_5400095 := by exact prefixLift 5400095
  have htrace : WordTrace (prefixWord ++ tailWord_5400095) baseStart_5400095 baseEnd_5400095 := by
    simpa [prefixWord, tailWord_5400095, baseEnd_5400095] using wordTrace_append hprefix tailTrace_5400095
  have hstable : (prefixWord ++ tailWord_5400095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400095).length < 2 ^ (prefixWord ++ tailWord_5400095).sum := by decide
  have hdescent : baseEnd_5400095 < baseStart_5400095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400096 : List Nat := [2, 1, 1, 6, 1, 1, 3, 3, 1, 1, 3]
def baseStart_5400096 : Nat := 118140960795 + 5400096 * 2 ^ 59
def prefixEnd_5400096 : Nat := 4983230072969 + 3 ^ 40 * 5400096 * 2
def baseEnd_5400096 : Nat := 2772844828421809333265417

theorem tailTrace_5400096 : CollatzResearch.WordTrace tailWord_5400096 prefixEnd_5400096 2772844828421809333265417 := by
  unfold tailWord_5400096
  simp only [CollatzResearch.WordTrace]
  refine ⟨98478840922190964908402071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131305121229587953211202761 98478840922190964908402071)
  ·
    refine ⟨147718261383286447362603107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98478840922190964908402071 147718261383286447362603107)
    ·
      refine ⟨221577392074929671043904661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147718261383286447362603107 221577392074929671043904661)
      ·
        refine ⟨10386440253512328330183031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 221577392074929671043904661 10386440253512328330183031)
        ·
          refine ⟨15579660380268492495274547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10386440253512328330183031 15579660380268492495274547)
          ·
            refine ⟨23369490570402738742911821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15579660380268492495274547 23369490570402738742911821)
            ·
              refine ⟨8763558963901027028591933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23369490570402738742911821 8763558963901027028591933)
              ·
                refine ⟨3286334611462885135721975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8763558963901027028591933 3286334611462885135721975)
                ·
                  refine ⟨4929501917194327703582963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3286334611462885135721975 4929501917194327703582963)
                  ·
                    refine ⟨7394252875791491555374445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4929501917194327703582963 7394252875791491555374445)
                    ·
                      refine ⟨2772844828421809333265417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7394252875791491555374445 2772844828421809333265417)
                      ·
                        rfl

theorem cell23_5400096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_5400096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400096 prefixEnd_5400096 := by exact prefixLift 5400096
  have htrace : WordTrace (prefixWord ++ tailWord_5400096) baseStart_5400096 baseEnd_5400096 := by
    simpa [prefixWord, tailWord_5400096, baseEnd_5400096] using wordTrace_append hprefix tailTrace_5400096
  have hstable : (prefixWord ++ tailWord_5400096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400096).length < 2 ^ (prefixWord ++ tailWord_5400096).sum := by decide
  have hdescent : baseEnd_5400096 < baseStart_5400096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400119 : List Nat := [1, 1, 3, 1, 2, 4, 3, 1, 3, 2, 2]
def baseStart_5400119 : Nat := 118140960795 + 5400119 * 2 ^ 59
def prefixEnd_5400119 : Nat := 4983230072969 + 3 ^ 40 * 5400119 * 2
def baseEnd_5400119 : Nat := 2772856638476862743277811

theorem tailTrace_5400119 : CollatzResearch.WordTrace tailWord_5400119 prefixEnd_5400119 2772856638476862743277811 := by
  unfold tailWord_5400119
  simp only [CollatzResearch.WordTrace]
  refine ⟨196958520723298604744891411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131305680482199069829927607 196958520723298604744891411)
  ·
    refine ⟨295437781084947907117337117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196958520723298604744891411 295437781084947907117337117)
    ·
      refine ⟨110789167906855465169001419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295437781084947907117337117 110789167906855465169001419)
      ·
        refine ⟨166183751860283197753502129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110789167906855465169001419 166183751860283197753502129)
        ·
          refine ⟨124637813895212398315126597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166183751860283197753502129 124637813895212398315126597)
          ·
            refine ⟨23369590105352324684086237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124637813895212398315126597 23369590105352324684086237)
            ·
              refine ⟨8763596289507121756532339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23369590105352324684086237 8763596289507121756532339)
              ·
                refine ⟨13145394434260682634798509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8763596289507121756532339 13145394434260682634798509)
                ·
                  refine ⟨4929522912847755988049441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13145394434260682634798509 4929522912847755988049441)
                  ·
                    refine ⟨3697142184635816991037081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4929522912847755988049441 3697142184635816991037081)
                    ·
                      refine ⟨2772856638476862743277811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3697142184635816991037081 2772856638476862743277811)
                      ·
                        rfl

theorem cell23_5400119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 2, 2].length) (baseStart_5400119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400119 prefixEnd_5400119 := by exact prefixLift 5400119
  have htrace : WordTrace (prefixWord ++ tailWord_5400119) baseStart_5400119 baseEnd_5400119 := by
    simpa [prefixWord, tailWord_5400119, baseEnd_5400119] using wordTrace_append hprefix tailTrace_5400119
  have hstable : (prefixWord ++ tailWord_5400119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400119).length < 2 ^ (prefixWord ++ tailWord_5400119).sum := by decide
  have hdescent : baseEnd_5400119 < baseStart_5400119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400128 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 6]
def baseStart_5400128 : Nat := 118140960795 + 5400128 * 2 ^ 59
def prefixEnd_5400128 : Nat := 4983230072969 + 3 ^ 40 * 5400128 * 2
def baseEnd_5400128 : Nat := 2772861259802753208065269

theorem tailTrace_5400128 : CollatzResearch.WordTrace tailWord_5400128 prefixEnd_5400128 2772861259802753208065269 := by
  unfold tailWord_5400128
  simp only [CollatzResearch.WordTrace]
  refine ⟨98479424490132999640984519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131305899320177332854646025 98479424490132999640984519)
  ·
    refine ⟨147719136735199499461476779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98479424490132999640984519 147719136735199499461476779)
    ·
      refine ⟨221578705102799249192215169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147719136735199499461476779 221578705102799249192215169)
      ·
        refine ⟨166184028827099436894161377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221578705102799249192215169 166184028827099436894161377)
        ·
          refine ⟨124638021620324577670621033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166184028827099436894161377 124638021620324577670621033)
          ·
            refine ⟨93478516215243433252965775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124638021620324577670621033 93478516215243433252965775)
            ·
              refine ⟨140217774322865149879448663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93478516215243433252965775 140217774322865149879448663)
              ·
                refine ⟨210326661484297724819172995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140217774322865149879448663 210326661484297724819172995)
                ·
                  refine ⟨315489992226446587228759493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210326661484297724819172995 315489992226446587228759493)
                  ·
                    refine ⟨59154373542458735105392405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 315489992226446587228759493 59154373542458735105392405)
                    ·
                      refine ⟨2772861259802753208065269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59154373542458735105392405 2772861259802753208065269)
                      ·
                        rfl

theorem cell23_5400128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_5400128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400128 prefixEnd_5400128 := by exact prefixLift 5400128
  have htrace : WordTrace (prefixWord ++ tailWord_5400128) baseStart_5400128 baseEnd_5400128 := by
    simpa [prefixWord, tailWord_5400128, baseEnd_5400128] using wordTrace_append hprefix tailTrace_5400128
  have hstable : (prefixWord ++ tailWord_5400128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400128).length < 2 ^ (prefixWord ++ tailWord_5400128).sum := by decide
  have hdescent : baseEnd_5400128 < baseStart_5400128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400156 : List Nat := [2, 2, 4, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_5400156 : Nat := 118140960795 + 5400156 * 2 ^ 59
def prefixEnd_5400156 : Nat := 4983230072969 + 3 ^ 40 * 5400156 * 2
def baseEnd_5400156 : Nat := 2772875637261079098515141

theorem tailTrace_5400156 : CollatzResearch.WordTrace tailWord_5400156 prefixEnd_5400156 2772875637261079098515141 := by
  unfold tailWord_5400156
  simp only [CollatzResearch.WordTrace]
  refine ⟨98479935112082280031994161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131306580149443040042658881 98479935112082280031994161)
  ·
    refine ⟨73859951334061710023995621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98479935112082280031994161 73859951334061710023995621)
    ·
      refine ⟨13848740875136570629499179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73859951334061710023995621 13848740875136570629499179)
      ·
        refine ⟨20773111312704855944248769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13848740875136570629499179 20773111312704855944248769)
        ·
          refine ⟨15579833484528641958186577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20773111312704855944248769 15579833484528641958186577)
          ·
            refine ⟨11684875113396481468639933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15579833484528641958186577 11684875113396481468639933)
            ·
              refine ⟨4381828167523680550739975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11684875113396481468639933 4381828167523680550739975)
              ·
                refine ⟨6572742251285520826109963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4381828167523680550739975 6572742251285520826109963)
                ·
                  refine ⟨9859113376928281239164945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6572742251285520826109963 9859113376928281239164945)
                  ·
                    refine ⟨7394335032696210929373709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9859113376928281239164945 7394335032696210929373709)
                    ·
                      refine ⟨2772875637261079098515141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7394335032696210929373709 2772875637261079098515141)
                      ·
                        rfl

theorem cell23_5400156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_5400156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400156 prefixEnd_5400156 := by exact prefixLift 5400156
  have htrace : WordTrace (prefixWord ++ tailWord_5400156) baseStart_5400156 baseEnd_5400156 := by
    simpa [prefixWord, tailWord_5400156, baseEnd_5400156] using wordTrace_append hprefix tailTrace_5400156
  have hstable : (prefixWord ++ tailWord_5400156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400156).length < 2 ^ (prefixWord ++ tailWord_5400156).sum := by decide
  have hdescent : baseEnd_5400156 < baseStart_5400156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400170 : List Nat := [3, 1, 3, 2, 1, 4, 2, 2, 1, 2, 2]
def baseStart_5400170 : Nat := 118140960795 + 5400170 * 2 ^ 59
def prefixEnd_5400170 : Nat := 4983230072969 + 3 ^ 40 * 5400170 * 2
def baseEnd_5400170 : Nat := 2772882825990242043740077

theorem tailTrace_5400170 : CollatzResearch.WordTrace tailWord_5400170 prefixEnd_5400170 2772882825990242043740077 := by
  unfold tailWord_5400170
  simp only [CollatzResearch.WordTrace]
  refine ⟨49240095211528460113749491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131306920564075893636665309 49240095211528460113749491)
  ·
    refine ⟨73860142817292690170624237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49240095211528460113749491 73860142817292690170624237)
    ·
      refine ⟨27697553556484758813984089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73860142817292690170624237 27697553556484758813984089)
      ·
        refine ⟨20773165167363569110488067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27697553556484758813984089 20773165167363569110488067)
        ·
          refine ⟨31159747751045353665732101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20773165167363569110488067 31159747751045353665732101)
          ·
            refine ⟨5842452703321003812324769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31159747751045353665732101 5842452703321003812324769)
            ·
              refine ⟨4381839527490752859243577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5842452703321003812324769 4381839527490752859243577)
              ·
                refine ⟨3286379645618064644432683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4381839527490752859243577 3286379645618064644432683)
                ·
                  refine ⟨4929569468427096966649025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3286379645618064644432683 4929569468427096966649025)
                  ·
                    refine ⟨3697177101320322724986769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4929569468427096966649025 3697177101320322724986769)
                    ·
                      refine ⟨2772882825990242043740077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3697177101320322724986769 2772882825990242043740077)
                      ·
                        rfl

theorem cell23_5400170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_5400170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400170 prefixEnd_5400170 := by exact prefixLift 5400170
  have htrace : WordTrace (prefixWord ++ tailWord_5400170) baseStart_5400170 baseEnd_5400170 := by
    simpa [prefixWord, tailWord_5400170, baseEnd_5400170] using wordTrace_append hprefix tailTrace_5400170
  have hstable : (prefixWord ++ tailWord_5400170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400170).length < 2 ^ (prefixWord ++ tailWord_5400170).sum := by decide
  have hdescent : baseEnd_5400170 < baseStart_5400170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400185 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 2, 6]
def baseStart_5400185 : Nat := 118140960795 + 5400185 * 2 ^ 59
def prefixEnd_5400185 : Nat := 4983230072969 + 3 ^ 40 * 5400185 * 2
def baseEnd_5400185 : Nat := 924296842733353161684169

theorem tailTrace_5400185 : CollatzResearch.WordTrace tailWord_5400185 prefixEnd_5400185 924296842733353161684169 := by
  unfold tailWord_5400185
  simp only [CollatzResearch.WordTrace]
  refine ⟨196960927941059498016794009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131307285294039665344529339 196960927941059498016794009)
  ·
    refine ⟨147720695955794623512595507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196960927941059498016794009 147720695955794623512595507)
    ·
      refine ⟨221581043933691935268893261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147720695955794623512595507 221581043933691935268893261)
      ·
        refine ⟨83092891475134475725834973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221581043933691935268893261 83092891475134475725834973)
        ·
          refine ⟨31159834303175428397188115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83092891475134475725834973 31159834303175428397188115)
          ·
            refine ⟨46739751454763142595782173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31159834303175428397188115 46739751454763142595782173)
            ·
              refine ⟨17527406795536178473418315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46739751454763142595782173 17527406795536178473418315)
              ·
                refine ⟨26291110193304267710127473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17527406795536178473418315 26291110193304267710127473)
                ·
                  refine ⟨19718332644978200782595605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26291110193304267710127473 19718332644978200782595605)
                  ·
                    refine ⟨924296842733353161684169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19718332644978200782595605 924296842733353161684169)
                    ·
                      rfl

theorem cell23_5400185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 6].length) (baseStart_5400185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400185 prefixEnd_5400185 := by exact prefixLift 5400185
  have htrace : WordTrace (prefixWord ++ tailWord_5400185) baseStart_5400185 baseEnd_5400185 := by
    simpa [prefixWord, tailWord_5400185, baseEnd_5400185] using wordTrace_append hprefix tailTrace_5400185
  have hstable : (prefixWord ++ tailWord_5400185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400185).length < 2 ^ (prefixWord ++ tailWord_5400185).sum := by decide
  have hdescent : baseEnd_5400185 < baseStart_5400185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400195 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 3]
def baseStart_5400195 : Nat := 118140960795 + 5400195 * 2 ^ 59
def prefixEnd_5400195 : Nat := 4983230072969 + 3 ^ 40 * 5400195 * 2
def baseEnd_5400195 : Nat := 2772895663006604445927461

theorem tailTrace_5400195 : CollatzResearch.WordTrace tailWord_5400195 prefixEnd_5400195 2772895663006604445927461 := by
  unfold tailWord_5400195
  simp only [CollatzResearch.WordTrace]
  refine ⟨196961292671023269724658039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131307528447348846483105359 196961292671023269724658039)
  ·
    refine ⟨295441939006534904586987059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196961292671023269724658039 295441939006534904586987059)
    ·
      refine ⟨443162908509802356880480589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295441939006534904586987059 443162908509802356880480589)
      ·
        refine ⟨166186090691175883830180221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 443162908509802356880480589 166186090691175883830180221)
        ·
          refine ⟨62319784009190956436317583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166186090691175883830180221 62319784009190956436317583)
          ·
            refine ⟨93479676013786434654476375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62319784009190956436317583 93479676013786434654476375)
            ·
              refine ⟨140219514020679651981714563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93479676013786434654476375 140219514020679651981714563)
              ·
                refine ⟨210329271031019477972571845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140219514020679651981714563 210329271031019477972571845)
                ·
                  refine ⟨39436738318316152119857221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210329271031019477972571845 39436738318316152119857221)
                  ·
                    refine ⟨7394388434684278522473229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39436738318316152119857221 7394388434684278522473229)
                    ·
                      refine ⟨2772895663006604445927461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7394388434684278522473229 2772895663006604445927461)
                      ·
                        rfl

theorem cell23_5400195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_5400195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400195 prefixEnd_5400195 := by exact prefixLift 5400195
  have htrace : WordTrace (prefixWord ++ tailWord_5400195) baseStart_5400195 baseEnd_5400195 := by
    simpa [prefixWord, tailWord_5400195, baseEnd_5400195] using wordTrace_append hprefix tailTrace_5400195
  have hstable : (prefixWord ++ tailWord_5400195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400195).length < 2 ^ (prefixWord ++ tailWord_5400195).sum := by decide
  have hdescent : baseEnd_5400195 < baseStart_5400195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400242 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3]
def baseStart_5400242 : Nat := 118140960795 + 5400242 * 2 ^ 59
def prefixEnd_5400242 : Nat := 4983230072969 + 3 ^ 40 * 5400242 * 2
def baseEnd_5400242 : Nat := 2772919796597365762039745

theorem tailTrace_5400242 : CollatzResearch.WordTrace tailWord_5400242 prefixEnd_5400242 2772919796597365762039745 := by
  unfold tailWord_5400242
  simp only [CollatzResearch.WordTrace]
  refine ⟨49240751725463249187904745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131308671267901997834412653 49240751725463249187904745)
  ·
    refine ⟨36930563794097436890928559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49240751725463249187904745 36930563794097436890928559)
    ·
      refine ⟨55395845691146155336392839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36930563794097436890928559 55395845691146155336392839)
      ·
        refine ⟨83093768536719233004589259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55395845691146155336392839 83093768536719233004589259)
        ·
          refine ⟨124640652805078849506883889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83093768536719233004589259 124640652805078849506883889)
          ·
            refine ⟨93480489603809137130162917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124640652805078849506883889 93480489603809137130162917)
            ·
              refine ⟨17527591800714213211905547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93480489603809137130162917 17527591800714213211905547)
              ·
                refine ⟨26291387701071319817858321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17527591800714213211905547 26291387701071319817858321)
                ·
                  refine ⟨19718540775803489863393741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26291387701071319817858321 19718540775803489863393741)
                  ·
                    refine ⟨7394452790926308698772653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19718540775803489863393741 7394452790926308698772653)
                    ·
                      refine ⟨2772919796597365762039745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7394452790926308698772653 2772919796597365762039745)
                      ·
                        rfl

theorem cell23_5400242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_5400242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400242 prefixEnd_5400242 := by exact prefixLift 5400242
  have htrace : WordTrace (prefixWord ++ tailWord_5400242) baseStart_5400242 baseEnd_5400242 := by
    simpa [prefixWord, tailWord_5400242, baseEnd_5400242] using wordTrace_append hprefix tailTrace_5400242
  have hstable : (prefixWord ++ tailWord_5400242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400242).length < 2 ^ (prefixWord ++ tailWord_5400242).sum := by decide
  have hdescent : baseEnd_5400242 < baseStart_5400242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400266 : List Nat := [3, 1, 2, 1, 5, 2, 1, 3, 5]
def baseStart_5400266 : Nat := 118140960795 + 5400266 * 2 ^ 59
def prefixEnd_5400266 : Nat := 4983230072969 + 3 ^ 40 * 5400266 * 2
def baseEnd_5400266 : Nat := 308103568903674852015515

theorem tailTrace_5400266 : CollatzResearch.WordTrace tailWord_5400266 prefixEnd_5400266 308103568903674852015515 := by
  unfold tailWord_5400266
  simp only [CollatzResearch.WordTrace]
  refine ⟨49240970563441512212623163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131309254835844032566995101 49240970563441512212623163)
  ·
    refine ⟨73861455845162268318934745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49240970563441512212623163 73861455845162268318934745)
    ·
      refine ⟨55396091883871701239201059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73861455845162268318934745 55396091883871701239201059)
      ·
        refine ⟨83094137825807551858801589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55396091883871701239201059 83094137825807551858801589)
        ·
          refine ⟨7790075421169457986762649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83094137825807551858801589 7790075421169457986762649)
          ·
            refine ⟨5842556565877093490071987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7790075421169457986762649 5842556565877093490071987)
            ·
              refine ⟨8763834848815640235107981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5842556565877093490071987 8763834848815640235107981)
              ·
                refine ⟨3286438068305865088165493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8763834848815640235107981 3286438068305865088165493)
                ·
                  refine ⟨308103568903674852015515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3286438068305865088165493 308103568903674852015515)
                  ·
                    rfl

theorem cell23_5400266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 5].length) (baseStart_5400266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400266 prefixEnd_5400266 := by exact prefixLift 5400266
  have htrace : WordTrace (prefixWord ++ tailWord_5400266) baseStart_5400266 baseEnd_5400266 := by
    simpa [prefixWord, tailWord_5400266, baseEnd_5400266] using wordTrace_append hprefix tailTrace_5400266
  have hstable : (prefixWord ++ tailWord_5400266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400266).length < 2 ^ (prefixWord ++ tailWord_5400266).sum := by decide
  have hdescent : baseEnd_5400266 < baseStart_5400266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400282 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4]
def baseStart_5400282 : Nat := 118140960795 + 5400282 * 2 ^ 59
def prefixEnd_5400282 : Nat := 4983230072969 + 3 ^ 40 * 5400282 * 2
def baseEnd_5400282 : Nat := 2772940335823545605539561

theorem tailTrace_5400282 : CollatzResearch.WordTrace tailWord_5400282 prefixEnd_5400282 2772940335823545605539561 := by
  unfold tailWord_5400282
  simp only [CollatzResearch.WordTrace]
  refine ⟨49241116455427020895768775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131309643881138722388716733 49241116455427020895768775)
  ·
    refine ⟨73861674683140531343653163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49241116455427020895768775 73861674683140531343653163)
    ·
      refine ⟨110792512024710797015479745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73861674683140531343653163 110792512024710797015479745)
      ·
        refine ⟨83094384018533097761609809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110792512024710797015479745 83094384018533097761609809)
        ·
          refine ⟨62320788013899823321207357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83094384018533097761609809 62320788013899823321207357)
          ·
            refine ⟨23370295505212433745452759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62320788013899823321207357 23370295505212433745452759)
            ·
              refine ⟨35055443257818650618179139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23370295505212433745452759 35055443257818650618179139)
              ·
                refine ⟨52583164886727975927268709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35055443257818650618179139 52583164886727975927268709)
                ·
                  refine ⟨9859343416261495486362883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52583164886727975927268709 9859343416261495486362883)
                  ·
                    refine ⟨14789015124392243229544325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9859343416261495486362883 14789015124392243229544325)
                    ·
                      refine ⟨2772940335823545605539561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14789015124392243229544325 2772940335823545605539561)
                      ·
                        rfl

theorem cell23_5400282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_5400282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400282 prefixEnd_5400282 := by exact prefixLift 5400282
  have htrace : WordTrace (prefixWord ++ tailWord_5400282) baseStart_5400282 baseEnd_5400282 := by
    simpa [prefixWord, tailWord_5400282, baseEnd_5400282] using wordTrace_append hprefix tailTrace_5400282
  have hstable : (prefixWord ++ tailWord_5400282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400282).length < 2 ^ (prefixWord ++ tailWord_5400282).sum := by decide
  have hdescent : baseEnd_5400282 < baseStart_5400282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400325 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 8]
def baseStart_5400325 : Nat := 118140960795 + 5400325 * 2 ^ 59
def prefixEnd_5400325 : Nat := 4983230072969 + 3 ^ 40 * 5400325 * 2
def baseEnd_5400325 : Nat := 2772962415491688937301863

theorem tailTrace_5400325 : CollatzResearch.WordTrace tailWord_5400325 prefixEnd_5400325 2772962415491688937301863 := by
  unfold tailWord_5400325
  simp only [CollatzResearch.WordTrace]
  refine ⟨196966034160552301926890429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131310689440368201284593619 196966034160552301926890429)
  ·
    refine ⟨73862262810207113222583911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196966034160552301926890429 73862262810207113222583911)
    ·
      refine ⟨110793394215310669833875867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73862262810207113222583911 110793394215310669833875867)
      ·
        refine ⟨166190091322966004750813801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110793394215310669833875867 166190091322966004750813801)
        ·
          refine ⟨124642568492224503563110351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166190091322966004750813801 124642568492224503563110351)
          ·
            refine ⟨186963852738336755344665527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124642568492224503563110351 186963852738336755344665527)
            ·
              refine ⟨280445779107505133016998291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186963852738336755344665527 280445779107505133016998291)
              ·
                refine ⟨420668668661257699525497437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280445779107505133016998291 420668668661257699525497437)
                ·
                  refine ⟨157750750747971637322061539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420668668661257699525497437 157750750747971637322061539)
                  ·
                    refine ⟨236626126121957455983092309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 157750750747971637322061539 236626126121957455983092309)
                    ·
                      refine ⟨2772962415491688937301863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 236626126121957455983092309 2772962415491688937301863)
                      ·
                        rfl

theorem cell23_5400325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_5400325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400325 prefixEnd_5400325 := by exact prefixLift 5400325
  have htrace : WordTrace (prefixWord ++ tailWord_5400325) baseStart_5400325 baseEnd_5400325 := by
    simpa [prefixWord, tailWord_5400325, baseEnd_5400325] using wordTrace_append hprefix tailTrace_5400325
  have hstable : (prefixWord ++ tailWord_5400325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400325).length < 2 ^ (prefixWord ++ tailWord_5400325).sum := by decide
  have hdescent : baseEnd_5400325 < baseStart_5400325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400343 : List Nat := [1, 1, 3, 4, 2, 1, 4, 2, 1, 4]
def baseStart_5400343 : Nat := 118140960795 + 5400343 * 2 ^ 59
def prefixEnd_5400343 : Nat := 4983230072969 + 3 ^ 40 * 5400343 * 2
def baseEnd_5400343 : Nat := 924323886047823288958927

theorem tailTrace_5400343 : CollatzResearch.WordTrace tailWord_5400343 prefixEnd_5400343 924323886047823288958927 := by
  unfold tailWord_5400343
  simp only [CollatzResearch.WordTrace]
  refine ⟨196966690674487091001045683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131311127116324727334030455 196966690674487091001045683)
  ·
    refine ⟨295450036011730636501568525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196966690674487091001045683 295450036011730636501568525)
    ·
      refine ⟨110793763504398988688088197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295450036011730636501568525 110793763504398988688088197)
      ·
        refine ⟨20773830657074810379016537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110793763504398988688088197 20773830657074810379016537)
        ·
          refine ⟨15580372992806107784262403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20773830657074810379016537 15580372992806107784262403)
          ·
            refine ⟨23370559489209161676393605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15580372992806107784262403 23370559489209161676393605)
            ·
              refine ⟨4381979904226717814323801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23370559489209161676393605 4381979904226717814323801)
              ·
                refine ⟨3286484928170038360742851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4381979904226717814323801 3286484928170038360742851)
                ·
                  refine ⟨4929727392255057541114277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3286484928170038360742851 4929727392255057541114277)
                  ·
                    refine ⟨924323886047823288958927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4929727392255057541114277 924323886047823288958927)
                    ·
                      rfl

theorem cell23_5400343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 1, 4].length) (baseStart_5400343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400343 prefixEnd_5400343 := by exact prefixLift 5400343
  have htrace : WordTrace (prefixWord ++ tailWord_5400343) baseStart_5400343 baseEnd_5400343 := by
    simpa [prefixWord, tailWord_5400343, baseEnd_5400343] using wordTrace_append hprefix tailTrace_5400343
  have hstable : (prefixWord ++ tailWord_5400343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400343).length < 2 ^ (prefixWord ++ tailWord_5400343).sum := by decide
  have hdescent : baseEnd_5400343 < baseStart_5400343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400350 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_5400350 : Nat := 118140960795 + 5400350 * 2 ^ 59
def prefixEnd_5400350 : Nat := 4983230072969 + 3 ^ 40 * 5400350 * 2
def baseEnd_5400350 : Nat := 2772975252508051339489249

theorem tailTrace_5400350 : CollatzResearch.WordTrace tailWord_5400350 prefixEnd_5400350 2772975252508051339489249 := by
  unfold tailWord_5400350
  simp only [CollatzResearch.WordTrace]
  refine ⟨24620868248182716399568813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131311297323641154131033669 24620868248182716399568813)
  ·
    refine ⟨9232825593068518649838305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24620868248182716399568813 9232825593068518649838305)
    ·
      refine ⟨6924619194801388987378729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9232825593068518649838305 6924619194801388987378729)
      ·
        refine ⟨5193464396101041740534047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6924619194801388987378729 5193464396101041740534047)
        ·
          refine ⟨7790196594151562610801071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5193464396101041740534047 7790196594151562610801071)
          ·
            refine ⟨11685294891227343916201607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7790196594151562610801071 11685294891227343916201607)
            ·
              refine ⟨17527942336841015874302411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11685294891227343916201607 17527942336841015874302411)
              ·
                refine ⟨26291913505261523811453617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17527942336841015874302411 26291913505261523811453617)
                ·
                  refine ⟨19718935128946142858590213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26291913505261523811453617 19718935128946142858590213)
                  ·
                    refine ⟨3697300336677401785985665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19718935128946142858590213 3697300336677401785985665)
                    ·
                      refine ⟨2772975252508051339489249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3697300336677401785985665 2772975252508051339489249)
                      ·
                        rfl

theorem cell23_5400350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_5400350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400350 prefixEnd_5400350 := by exact prefixLift 5400350
  have htrace : WordTrace (prefixWord ++ tailWord_5400350) baseStart_5400350 baseEnd_5400350 := by
    simpa [prefixWord, tailWord_5400350, baseEnd_5400350] using wordTrace_append hprefix tailTrace_5400350
  have hstable : (prefixWord ++ tailWord_5400350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400350).length < 2 ^ (prefixWord ++ tailWord_5400350).sum := by decide
  have hdescent : baseEnd_5400350 < baseStart_5400350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400352 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 5, 5]
def baseStart_5400352 : Nat := 118140960795 + 5400352 * 2 ^ 59
def prefixEnd_5400352 : Nat := 4983230072969 + 3 ^ 40 * 5400352 * 2
def baseEnd_5400352 : Nat := 924325426489786777221413

theorem tailTrace_5400352 : CollatzResearch.WordTrace tailWord_5400352 prefixEnd_5400352 924325426489786777221413 := by
  unfold tailWord_5400352
  simp only [CollatzResearch.WordTrace]
  refine ⟨98483509465727242769061655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131311345954302990358748873 98483509465727242769061655)
  ·
    refine ⟨147725264198590864153592483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98483509465727242769061655 147725264198590864153592483)
    ·
      refine ⟨221587896297886296230388725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147725264198590864153592483 221587896297886296230388725)
      ·
        refine ⟨20773865277926840271598943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 221587896297886296230388725 20773865277926840271598943)
        ·
          refine ⟨31160797916890260407398415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20773865277926840271598943 31160797916890260407398415)
          ·
            refine ⟨46741196875335390611097623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31160797916890260407398415 46741196875335390611097623)
            ·
              refine ⟨70111795313003085916646435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46741196875335390611097623 70111795313003085916646435)
              ·
                refine ⟨105167692969504628874969653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70111795313003085916646435 105167692969504628874969653)
                ·
                  refine ⟨9859471215891058957028405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105167692969504628874969653 9859471215891058957028405)
                  ·
                    refine ⟨924325426489786777221413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9859471215891058957028405 924325426489786777221413)
                    ·
                      rfl

theorem cell23_5400352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 5, 5].length) (baseStart_5400352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400352 prefixEnd_5400352 := by exact prefixLift 5400352
  have htrace : WordTrace (prefixWord ++ tailWord_5400352) baseStart_5400352 baseEnd_5400352 := by
    simpa [prefixWord, tailWord_5400352, baseEnd_5400352] using wordTrace_append hprefix tailTrace_5400352
  have hstable : (prefixWord ++ tailWord_5400352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400352).length < 2 ^ (prefixWord ++ tailWord_5400352).sum := by decide
  have hdescent : baseEnd_5400352 < baseStart_5400352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400376 : List Nat := [2, 1, 2, 1, 3, 3, 3, 1, 2, 3, 2]
def baseStart_5400376 : Nat := 118140960795 + 5400376 * 2 ^ 59
def prefixEnd_5400376 : Nat := 4983230072969 + 3 ^ 40 * 5400376 * 2
def baseEnd_5400376 : Nat := 2772988603005068237764129

theorem tailTrace_5400376 : CollatzResearch.WordTrace tailWord_5400376 prefixEnd_5400376 2772988603005068237764129 := by
  unfold tailWord_5400376
  simp only [CollatzResearch.WordTrace]
  refine ⟨98483947141683768818498491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131311929522245025091331321 98483947141683768818498491)
  ·
    refine ⟨147725920712525653227747737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98483947141683768818498491 147725920712525653227747737)
    ·
      refine ⟨110794440534394239920810803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147725920712525653227747737 110794440534394239920810803)
      ·
        refine ⟨166191660801591359881216205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110794440534394239920810803 166191660801591359881216205)
        ·
          refine ⟨62321872800596759955456077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166191660801591359881216205 62321872800596759955456077)
          ·
            refine ⟨23370702300223784983296029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62321872800596759955456077 23370702300223784983296029)
            ·
              refine ⟨8764013362583919368736011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23370702300223784983296029 8764013362583919368736011)
              ·
                refine ⟨13146020043875879053104017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8764013362583919368736011 13146020043875879053104017)
                ·
                  refine ⟨9859515032906909289828013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13146020043875879053104017 9859515032906909289828013)
                  ·
                    refine ⟨3697318137340090983685505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9859515032906909289828013 3697318137340090983685505)
                    ·
                      refine ⟨2772988603005068237764129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3697318137340090983685505 2772988603005068237764129)
                      ·
                        rfl

theorem cell23_5400376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 2, 3, 2].length) (baseStart_5400376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400376 prefixEnd_5400376 := by exact prefixLift 5400376
  have htrace : WordTrace (prefixWord ++ tailWord_5400376) baseStart_5400376 baseEnd_5400376 := by
    simpa [prefixWord, tailWord_5400376, baseEnd_5400376] using wordTrace_append hprefix tailTrace_5400376
  have hstable : (prefixWord ++ tailWord_5400376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400376).length < 2 ^ (prefixWord ++ tailWord_5400376).sum := by decide
  have hdescent : baseEnd_5400376 < baseStart_5400376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400389 : List Nat := [1, 3, 1, 1, 1, 2, 5, 3, 1, 1, 4]
def baseStart_5400389 : Nat := 118140960795 + 5400389 * 2 ^ 59
def prefixEnd_5400389 : Nat := 4983230072969 + 3 ^ 40 * 5400389 * 2
def baseEnd_5400389 : Nat := 2772995278253576686901569

theorem tailTrace_5400389 : CollatzResearch.WordTrace tailWord_5400389 prefixEnd_5400389 2772995278253576686901569 := by
  unfold tailWord_5400389
  simp only [CollatzResearch.WordTrace]
  refine ⟨196968368432320440857220221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131312245621546960571480147 196968368432320440857220221)
  ·
    refine ⟨73863138162120165321457583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196968368432320440857220221 73863138162120165321457583)
    ·
      refine ⟨110794707243180247982186375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73863138162120165321457583 110794707243180247982186375)
      ·
        refine ⟨166192060864770371973279563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110794707243180247982186375 166192060864770371973279563)
        ·
          refine ⟨249288091297155557959919345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166192060864770371973279563 249288091297155557959919345)
          ·
            refine ⟨186966068472866668469939509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249288091297155557959919345 186966068472866668469939509)
            ·
              refine ⟨17528068919331250169056829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 186966068472866668469939509 17528068919331250169056829)
              ·
                refine ⟨6573025844749218813396311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17528068919331250169056829 6573025844749218813396311)
                ·
                  refine ⟨9859538767123828220094467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6573025844749218813396311 9859538767123828220094467)
                  ·
                    refine ⟨14789308150685742330141701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9859538767123828220094467 14789308150685742330141701)
                    ·
                      refine ⟨2772995278253576686901569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14789308150685742330141701 2772995278253576686901569)
                      ·
                        rfl

theorem cell23_5400389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 1, 4].length) (baseStart_5400389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400389 prefixEnd_5400389 := by exact prefixLift 5400389
  have htrace : WordTrace (prefixWord ++ tailWord_5400389) baseStart_5400389 baseEnd_5400389 := by
    simpa [prefixWord, tailWord_5400389, baseEnd_5400389] using wordTrace_append hprefix tailTrace_5400389
  have hstable : (prefixWord ++ tailWord_5400389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400389).length < 2 ^ (prefixWord ++ tailWord_5400389).sum := by decide
  have hdescent : baseEnd_5400389 < baseStart_5400389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400419 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 6]
def baseStart_5400419 : Nat := 118140960795 + 5400419 * 2 ^ 59
def prefixEnd_5400419 : Nat := 4983230072969 + 3 ^ 40 * 5400419 * 2
def baseEnd_5400419 : Nat := 2773010682673211569526431

theorem tailTrace_5400419 : CollatzResearch.WordTrace tailWord_5400419 prefixEnd_5400419 2773010682673211569526431 := by
  unfold tailWord_5400419
  simp only [CollatzResearch.WordTrace]
  refine ⟨196969462622211755980812311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131312975081474503987208207 196969462622211755980812311)
  ·
    refine ⟨295454193933317633971218467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196969462622211755980812311 295454193933317633971218467)
    ·
      refine ⟨443181290899976450956827701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295454193933317633971218467 443181290899976450956827701)
      ·
        refine ⟨41548246021872792277202597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 443181290899976450956827701 41548246021872792277202597)
        ·
          refine ⟨7790296129101148551975487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41548246021872792277202597 7790296129101148551975487)
          ·
            refine ⟨11685444193651722827963231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7790296129101148551975487 11685444193651722827963231)
            ·
              refine ⟨17528166290477584241944847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11685444193651722827963231 17528166290477584241944847)
              ·
                refine ⟨26292249435716376362917271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17528166290477584241944847 26292249435716376362917271)
                ·
                  refine ⟨39438374153574564544375907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26292249435716376362917271 39438374153574564544375907)
                  ·
                    refine ⟨59157561230361846816563861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39438374153574564544375907 59157561230361846816563861)
                    ·
                      refine ⟨2773010682673211569526431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59157561230361846816563861 2773010682673211569526431)
                      ·
                        rfl

theorem cell23_5400419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_5400419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400419 prefixEnd_5400419 := by exact prefixLift 5400419
  have htrace : WordTrace (prefixWord ++ tailWord_5400419) baseStart_5400419 baseEnd_5400419 := by
    simpa [prefixWord, tailWord_5400419, baseEnd_5400419] using wordTrace_append hprefix tailTrace_5400419
  have hstable : (prefixWord ++ tailWord_5400419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400419).length < 2 ^ (prefixWord ++ tailWord_5400419).sum := by decide
  have hdescent : baseEnd_5400419 < baseStart_5400419 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400429 : List Nat := [1, 5, 1, 1, 1, 1, 6, 7]
def baseStart_5400429 : Nat := 118140960795 + 5400429 * 2 ^ 59
def prefixEnd_5400429 : Nat := 4983230072969 + 3 ^ 40 * 5400429 * 2
def baseEnd_5400429 : Nat := 102704289536287278903755

theorem tailTrace_5400429 : CollatzResearch.WordTrace tailWord_5400429 prefixEnd_5400429 102704289536287278903755 := by
  unfold tailWord_5400429
  simp only [CollatzResearch.WordTrace]
  refine ⟨196969827352175527688676341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131313218234783685125784227 196969827352175527688676341)
  ·
    refine ⟨18465921314266455720813407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 196969827352175527688676341 18465921314266455720813407)
    ·
      refine ⟨27698881971399683581220111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18465921314266455720813407 27698881971399683581220111)
      ·
        refine ⟨41548322957099525371830167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27698881971399683581220111 41548322957099525371830167)
        ·
          refine ⟨62322484435649288057745251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41548322957099525371830167 62322484435649288057745251)
          ·
            refine ⟨93483726653473932086617877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62322484435649288057745251 93483726653473932086617877)
            ·
              refine ⟨4382049686881590566560213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93483726653473932086617877 4382049686881590566560213)
              ·
                refine ⟨102704289536287278903755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4382049686881590566560213 102704289536287278903755)
                ·
                  rfl

theorem cell23_5400429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 7].length) (baseStart_5400429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400429 prefixEnd_5400429 := by exact prefixLift 5400429
  have htrace : WordTrace (prefixWord ++ tailWord_5400429) baseStart_5400429 baseEnd_5400429 := by
    simpa [prefixWord, tailWord_5400429, baseEnd_5400429] using wordTrace_append hprefix tailTrace_5400429
  have hstable : (prefixWord ++ tailWord_5400429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400429).length < 2 ^ (prefixWord ++ tailWord_5400429).sum := by decide
  have hdescent : baseEnd_5400429 < baseStart_5400429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400446 : List Nat := [4, 2, 3, 1, 1, 3, 9]
def baseStart_5400446 : Nat := 118140960795 + 5400446 * 2 ^ 59
def prefixEnd_5400446 : Nat := 4983230072969 + 3 ^ 40 * 5400446 * 2
def baseEnd_5400446 : Nat := 34234870946307197085047

theorem tailTrace_5400446 : CollatzResearch.WordTrace tailWord_5400446 prefixEnd_5400446 34234870946307197085047 := by
  unfold tailWord_5400446
  simp only [CollatzResearch.WordTrace]
  refine ⟨24621305924139242449005649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131313631595409293061363461 24621305924139242449005649)
  ·
    refine ⟨18465979443104431836754237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24621305924139242449005649 18465979443104431836754237)
    ·
      refine ⟨6924742291164161938782839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18465979443104431836754237 6924742291164161938782839)
      ·
        refine ⟨10387113436746242908174259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6924742291164161938782839 10387113436746242908174259)
        ·
          refine ⟨15580670155119364362261389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10387113436746242908174259 15580670155119364362261389)
          ·
            refine ⟨5842751308169761635848021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15580670155119364362261389 5842751308169761635848021)
            ·
              refine ⟨34234870946307197085047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5842751308169761635848021 34234870946307197085047)
              ·
                rfl

theorem cell23_5400446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 9].length) (baseStart_5400446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400446 prefixEnd_5400446 := by exact prefixLift 5400446
  have htrace : WordTrace (prefixWord ++ tailWord_5400446) baseStart_5400446 baseEnd_5400446 := by
    simpa [prefixWord, tailWord_5400446, baseEnd_5400446] using wordTrace_append hprefix tailTrace_5400446
  have hstable : (prefixWord ++ tailWord_5400446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400446).length < 2 ^ (prefixWord ++ tailWord_5400446).sum := by decide
  have hdescent : baseEnd_5400446 < baseStart_5400446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400473 : List Nat := [1, 2, 1, 2, 1, 3, 6, 1, 2, 1, 3]
def baseStart_5400473 : Nat := 118140960795 + 5400473 * 2 ^ 59
def prefixEnd_5400473 : Nat := 4983230072969 + 3 ^ 40 * 5400473 * 2
def baseEnd_5400473 : Nat := 2773038410628554358251183

theorem tailTrace_5400473 : CollatzResearch.WordTrace tailWord_5400473 prefixEnd_5400473 2773038410628554358251183 := by
  unfold tailWord_5400473
  simp only [CollatzResearch.WordTrace]
  refine ⟨196971432164016123203278073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131314288109344082135518715 196971432164016123203278073)
  ·
    refine ⟨147728574123012092402458555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196971432164016123203278073 147728574123012092402458555)
    ·
      refine ⟨221592861184518138603687833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147728574123012092402458555 221592861184518138603687833)
      ·
        refine ⟨166194645888388603952765875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221592861184518138603687833 166194645888388603952765875)
        ·
          refine ⟨249291968832582905929148813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166194645888388603952765875 249291968832582905929148813)
          ·
            refine ⟨93484488312218589723430805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249291968832582905929148813 93484488312218589723430805)
            ·
              refine ⟨4382085389635246393285819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93484488312218589723430805 4382085389635246393285819)
              ·
                refine ⟨6573128084452869589928729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4382085389635246393285819 6573128084452869589928729)
                ·
                  refine ⟨4929846063339652192446547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6573128084452869589928729 4929846063339652192446547)
                  ·
                    refine ⟨7394769095009478288669821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4929846063339652192446547 7394769095009478288669821)
                    ·
                      refine ⟨2773038410628554358251183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7394769095009478288669821 2773038410628554358251183)
                      ·
                        rfl

theorem cell23_5400473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 2, 1, 3].length) (baseStart_5400473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400473 prefixEnd_5400473 := by exact prefixLift 5400473
  have htrace : WordTrace (prefixWord ++ tailWord_5400473) baseStart_5400473 baseEnd_5400473 := by
    simpa [prefixWord, tailWord_5400473, baseEnd_5400473] using wordTrace_append hprefix tailTrace_5400473
  have hstable : (prefixWord ++ tailWord_5400473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400473).length < 2 ^ (prefixWord ++ tailWord_5400473).sum := by decide
  have hdescent : baseEnd_5400473 < baseStart_5400473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400494 : List Nat := [4, 1, 5, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_5400494 : Nat := 118140960795 + 5400494 * 2 ^ 59
def prefixEnd_5400494 : Nat := 4983230072969 + 3 ^ 40 * 5400494 * 2
def baseEnd_5400494 : Nat := 2773049193722298776088587

theorem tailTrace_5400494 : CollatzResearch.WordTrace tailWord_5400494 prefixEnd_5400494 2773049193722298776088587 := by
  unfold tailWord_5400494
  simp only [CollatzResearch.WordTrace]
  refine ⟨24621524762117505473724067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131314798731293362526528357 24621524762117505473724067)
  ·
    refine ⟨36932287143176258210586101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24621524762117505473724067 36932287143176258210586101)
    ·
      refine ⟨3462401919672774207242447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36932287143176258210586101 3462401919672774207242447)
      ·
        refine ⟨5193602879509161310863671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3462401919672774207242447 5193602879509161310863671)
        ·
          refine ⟨7790404319263741966295507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5193602879509161310863671 7790404319263741966295507)
          ·
            refine ⟨11685606478895612949443261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7790404319263741966295507 11685606478895612949443261)
            ·
              refine ⟨4382102429585854856041223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11685606478895612949443261 4382102429585854856041223)
              ·
                refine ⟨6573153644378782284061835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4382102429585854856041223 6573153644378782284061835)
                ·
                  refine ⟨9859730466568173426092753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6573153644378782284061835 9859730466568173426092753)
                  ·
                    refine ⟨7394797849926130069569565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9859730466568173426092753 7394797849926130069569565)
                    ·
                      refine ⟨2773049193722298776088587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7394797849926130069569565 2773049193722298776088587)
                      ·
                        rfl

theorem cell23_5400494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_5400494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400494 prefixEnd_5400494 := by exact prefixLift 5400494
  have htrace : WordTrace (prefixWord ++ tailWord_5400494) baseStart_5400494 baseEnd_5400494 := by
    simpa [prefixWord, tailWord_5400494, baseEnd_5400494] using wordTrace_append hprefix tailTrace_5400494
  have hstable : (prefixWord ++ tailWord_5400494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400494).length < 2 ^ (prefixWord ++ tailWord_5400494).sum := by decide
  have hdescent : baseEnd_5400494 < baseStart_5400494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400530 : List Nat := [3, 2, 2, 3, 2, 1, 2, 1, 1, 4, 2]
def baseStart_5400530 : Nat := 118140960795 + 5400530 * 2 ^ 59
def prefixEnd_5400530 : Nat := 4983230072969 + 3 ^ 40 * 5400530 * 2
def baseEnd_5400530 : Nat := 2773067679025860635238421

theorem tailTrace_5400530 : CollatzResearch.WordTrace tailWord_5400530 prefixEnd_5400530 2773067679025860635238421 := by
  unfold tailWord_5400530
  simp only [CollatzResearch.WordTrace]
  refine ⟨49243377781202405484525761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131315674083206414625402029 49243377781202405484525761)
  ·
    refine ⟨36932533335901804113394321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49243377781202405484525761 36932533335901804113394321)
    ·
      refine ⟨27699400001926353085045741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36932533335901804113394321 27699400001926353085045741)
      ·
        refine ⟨10387275000722382406892153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27699400001926353085045741 10387275000722382406892153)
        ·
          refine ⟨7790456250541786805169115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10387275000722382406892153 7790456250541786805169115)
          ·
            refine ⟨11685684375812680207753673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7790456250541786805169115 11685684375812680207753673)
            ·
              refine ⟨8764263281859510155815255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11685684375812680207753673 8764263281859510155815255)
              ·
                refine ⟨13146394922789265233722883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8764263281859510155815255 13146394922789265233722883)
                ·
                  refine ⟨19719592384183897850584325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13146394922789265233722883 19719592384183897850584325)
                  ·
                    refine ⟨3697423572034480846984561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19719592384183897850584325 3697423572034480846984561)
                    ·
                      refine ⟨2773067679025860635238421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3697423572034480846984561 2773067679025860635238421)
                      ·
                        rfl

theorem cell23_5400530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_5400530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400530 prefixEnd_5400530 := by exact prefixLift 5400530
  have htrace : WordTrace (prefixWord ++ tailWord_5400530) baseStart_5400530 baseEnd_5400530 := by
    simpa [prefixWord, tailWord_5400530, baseEnd_5400530] using wordTrace_append hprefix tailTrace_5400530
  have hstable : (prefixWord ++ tailWord_5400530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400530).length < 2 ^ (prefixWord ++ tailWord_5400530).sum := by decide
  have hdescent : baseEnd_5400530 < baseStart_5400530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400629 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_5400629 : Nat := 118140960795 + 5400629 * 2 ^ 59
def prefixEnd_5400629 : Nat := 4983230072969 + 3 ^ 40 * 5400629 * 2
def baseEnd_5400629 : Nat := 2773118513610655747900465

theorem tailTrace_5400629 : CollatzResearch.WordTrace tailWord_5400629 prefixEnd_5400629 2773118513610655747900465 := by
  unfold tailWord_5400629
  simp only [CollatzResearch.WordTrace]
  refine ⟨196977121951450961845956941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131318081300967307897304627 196977121951450961845956941)
  ·
    refine ⟨73866420731794110692233853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196977121951450961845956941 73866420731794110692233853)
    ·
      refine ⟨27699907774422791509587695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73866420731794110692233853 27699907774422791509587695)
      ·
        refine ⟨41549861661634187264381543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27699907774422791509587695 41549861661634187264381543)
        ·
          refine ⟨62324792492451280896572315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41549861661634187264381543 62324792492451280896572315)
          ·
            refine ⟨93487188738676921344858473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62324792492451280896572315 93487188738676921344858473)
            ·
              refine ⟨70115391554007691008643855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93487188738676921344858473 70115391554007691008643855)
              ·
                refine ⟨105173087331011536512965783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70115391554007691008643855 105173087331011536512965783)
                ·
                  refine ⟨157759630996517304769448675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105173087331011536512965783 157759630996517304769448675)
                  ·
                    refine ⟨236639446494775957154173013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 157759630996517304769448675 236639446494775957154173013)
                    ·
                      refine ⟨2773118513610655747900465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 236639446494775957154173013 2773118513610655747900465)
                      ·
                        rfl

theorem cell23_5400629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_5400629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400629 prefixEnd_5400629 := by exact prefixLift 5400629
  have htrace : WordTrace (prefixWord ++ tailWord_5400629) baseStart_5400629 baseEnd_5400629 := by
    simpa [prefixWord, tailWord_5400629, baseEnd_5400629] using wordTrace_append hprefix tailTrace_5400629
  have hstable : (prefixWord ++ tailWord_5400629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400629).length < 2 ^ (prefixWord ++ tailWord_5400629).sum := by decide
  have hdescent : baseEnd_5400629 < baseStart_5400629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400663 : List Nat := [1, 1, 3, 2, 2, 1, 3, 3, 2, 3, 2]
def baseStart_5400663 : Nat := 118140960795 + 5400663 * 2 ^ 59
def prefixEnd_5400663 : Nat := 4983230072969 + 3 ^ 40 * 5400663 * 2
def baseEnd_5400663 : Nat := 2773135971952908614875309

theorem tailTrace_5400663 : CollatzResearch.WordTrace tailWord_5400663 prefixEnd_5400663 2773135971952908614875309 := by
  unfold tailWord_5400663
  simp only [CollatzResearch.WordTrace]
  refine ⟨196978362033327785652694643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131318908022218523768463095 196978362033327785652694643)
  ·
    refine ⟨295467543049991678479041965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196978362033327785652694643 295467543049991678479041965)
    ·
      refine ⟨110800328643746879429640737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295467543049991678479041965 110800328643746879429640737)
      ·
        refine ⟨83100246482810159572230553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110800328643746879429640737 83100246482810159572230553)
        ·
          refine ⟨62325184862107619679172915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83100246482810159572230553 62325184862107619679172915)
          ·
            refine ⟨93487777293161429518759373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62325184862107619679172915 93487777293161429518759373)
            ·
              refine ⟨35057916484935536069534765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93487777293161429518759373 35057916484935536069534765)
              ·
                refine ⟨13146718681850826026075537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35057916484935536069534765 13146718681850826026075537)
                ·
                  refine ⟨9860039011388119519556653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13146718681850826026075537 9860039011388119519556653)
                  ·
                    refine ⟨3697514629270544819833745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9860039011388119519556653 3697514629270544819833745)
                    ·
                      refine ⟨2773135971952908614875309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3697514629270544819833745 2773135971952908614875309)
                      ·
                        rfl

theorem cell23_5400663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_5400663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400663 prefixEnd_5400663 := by exact prefixLift 5400663
  have htrace : WordTrace (prefixWord ++ tailWord_5400663) baseStart_5400663 baseEnd_5400663 := by
    simpa [prefixWord, tailWord_5400663, baseEnd_5400663] using wordTrace_append hprefix tailTrace_5400663
  have hstable : (prefixWord ++ tailWord_5400663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400663).length < 2 ^ (prefixWord ++ tailWord_5400663).sum := by decide
  have hdescent : baseEnd_5400663 < baseStart_5400663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400686 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 3, 6]
def baseStart_5400686 : Nat := 118140960795 + 5400686 * 2 ^ 59
def prefixEnd_5400686 : Nat := 4983230072969 + 3 ^ 40 * 5400686 * 2
def baseEnd_5400686 : Nat := 924382594002654008295901

theorem tailTrace_5400686 : CollatzResearch.WordTrace tailWord_5400686 prefixEnd_5400686 924382594002654008295901 := by
  unfold tailWord_5400686
  simp only [CollatzResearch.WordTrace]
  refine ⟨24622400114030557572597739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131319467274829640387187941 24622400114030557572597739)
  ·
    refine ⟨36933600171045836358896609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24622400114030557572597739 36933600171045836358896609)
    ·
      refine ⟨27700200128284377269172457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36933600171045836358896609 27700200128284377269172457)
      ·
        refine ⟨20775150096213282951879343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27700200128284377269172457 20775150096213282951879343)
        ·
          refine ⟨31162725144319924427819015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20775150096213282951879343 31162725144319924427819015)
          ·
            refine ⟨46744087716479886641728523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31162725144319924427819015 46744087716479886641728523)
            ·
              refine ⟨70116131574719829962592785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46744087716479886641728523 70116131574719829962592785)
              ·
                refine ⟨52587098681039872471944589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70116131574719829962592785 52587098681039872471944589)
                ·
                  refine ⟨19720162005389952176979221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52587098681039872471944589 19720162005389952176979221)
                  ·
                    refine ⟨924382594002654008295901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19720162005389952176979221 924382594002654008295901)
                    ·
                      rfl

theorem cell23_5400686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_5400686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400686 prefixEnd_5400686 := by exact prefixLift 5400686
  have htrace : WordTrace (prefixWord ++ tailWord_5400686) baseStart_5400686 baseEnd_5400686 := by
    simpa [prefixWord, tailWord_5400686, baseEnd_5400686] using wordTrace_append hprefix tailTrace_5400686
  have hstable : (prefixWord ++ tailWord_5400686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400686).length < 2 ^ (prefixWord ++ tailWord_5400686).sum := by decide
  have hdescent : baseEnd_5400686 < baseStart_5400686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400687 : List Nat := [1, 1, 2, 1, 3, 4, 4, 2, 1, 1, 3]
def baseStart_5400687 : Nat := 118140960795 + 5400687 * 2 ^ 59
def prefixEnd_5400687 : Nat := 4983230072969 + 3 ^ 40 * 5400687 * 2
def baseEnd_5400687 : Nat := 2773148295488616520975199

theorem tailTrace_5400687 : CollatzResearch.WordTrace tailWord_5400687 prefixEnd_5400687 2773148295488616520975199 := by
  unfold tailWord_5400687
  simp only [CollatzResearch.WordTrace]
  refine ⟨196979237385240837751568315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131319491590160558501045543 196979237385240837751568315)
  ·
    refine ⟨295468856077861256627352473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196979237385240837751568315 295468856077861256627352473)
    ·
      refine ⟨221601642058395942470514355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295468856077861256627352473 221601642058395942470514355)
      ·
        refine ⟨332402463087593913705771533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221601642058395942470514355 332402463087593913705771533)
        ·
          refine ⟨124650923657847717639664325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332402463087593913705771533 124650923657847717639664325)
          ·
            refine ⟨23372048185846447057437061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124650923657847717639664325 23372048185846447057437061)
            ·
              refine ⟨4382259034846208823269449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23372048185846447057437061 4382259034846208823269449)
              ·
                refine ⟨3286694276134656617452087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4382259034846208823269449 3286694276134656617452087)
                ·
                  refine ⟨4930041414201984926178131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3286694276134656617452087 4930041414201984926178131)
                  ·
                    refine ⟨7395062121302977389267197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4930041414201984926178131 7395062121302977389267197)
                    ·
                      refine ⟨2773148295488616520975199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7395062121302977389267197 2773148295488616520975199)
                      ·
                        rfl

theorem cell23_5400687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 1, 1, 3].length) (baseStart_5400687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400687 prefixEnd_5400687 := by exact prefixLift 5400687
  have htrace : WordTrace (prefixWord ++ tailWord_5400687) baseStart_5400687 baseEnd_5400687 := by
    simpa [prefixWord, tailWord_5400687, baseEnd_5400687] using wordTrace_append hprefix tailTrace_5400687
  have hstable : (prefixWord ++ tailWord_5400687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400687).length < 2 ^ (prefixWord ++ tailWord_5400687).sum := by decide
  have hdescent : baseEnd_5400687 < baseStart_5400687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400713 : List Nat := [1, 2, 1, 1, 4, 2, 2, 4, 1, 2, 3]
def baseStart_5400713 : Nat := 118140960795 + 5400713 * 2 ^ 59
def prefixEnd_5400713 : Nat := 4983230072969 + 3 ^ 40 * 5400713 * 2
def baseEnd_5400713 : Nat := 2773161645985633419250079

theorem tailTrace_5400713 : CollatzResearch.WordTrace tailWord_5400713 prefixEnd_5400713 2773161645985633419250079 := by
  unfold tailWord_5400713
  simp only [CollatzResearch.WordTrace]
  refine ⟨196980185683146644192014793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131320123788764429461343195 196980185683146644192014793)
  ·
    refine ⟨147735139262359983144011095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196980185683146644192014793 147735139262359983144011095)
    ·
      refine ⟨221602708893539974716016643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147735139262359983144011095 221602708893539974716016643)
      ·
        refine ⟨332404063340309962074024965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221602708893539974716016643 332404063340309962074024965)
        ·
          refine ⟨62325761876308117888879681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 332404063340309962074024965 62325761876308117888879681)
          ·
            refine ⟨46744321407231088416659761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62325761876308117888879681 46744321407231088416659761)
            ·
              refine ⟨35058241055423316312494821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46744321407231088416659761 35058241055423316312494821)
              ·
                refine ⟨6573420197891871808592779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35058241055423316312494821 6573420197891871808592779)
                ·
                  refine ⟨9860130296837807712889169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6573420197891871808592779 9860130296837807712889169)
                  ·
                    refine ⟨7395097722628355784666877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9860130296837807712889169 7395097722628355784666877)
                    ·
                      refine ⟨2773161645985633419250079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7395097722628355784666877 2773161645985633419250079)
                      ·
                        rfl

theorem cell23_5400713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 2, 3].length) (baseStart_5400713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400713 prefixEnd_5400713 := by exact prefixLift 5400713
  have htrace : WordTrace (prefixWord ++ tailWord_5400713) baseStart_5400713 baseEnd_5400713 := by
    simpa [prefixWord, tailWord_5400713, baseEnd_5400713] using wordTrace_append hprefix tailTrace_5400713
  have hstable : (prefixWord ++ tailWord_5400713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400713).length < 2 ^ (prefixWord ++ tailWord_5400713).sum := by decide
  have hdescent : baseEnd_5400713 < baseStart_5400713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400724 : List Nat := [2, 4, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_5400724 : Nat := 118140960795 + 5400724 * 2 ^ 59
def prefixEnd_5400724 : Nat := 4983230072969 + 3 ^ 40 * 5400724 * 2
def baseEnd_5400724 : Nat := 924389098090944292070843

theorem tailTrace_5400724 : CollatzResearch.WordTrace tailWord_5400724 prefixEnd_5400724 924389098090944292070843 := by
  unfold tailWord_5400724
  simp only [CollatzResearch.WordTrace]
  refine ⟨98490293443053396535332613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131320391257404528713776817 98490293443053396535332613)
  ·
    refine ⟨18466930020572511850374865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98490293443053396535332613 18466930020572511850374865)
    ·
      refine ⟨13850197515429383887781149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18466930020572511850374865 13850197515429383887781149)
      ·
        refine ⟨5193824068286018957917931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13850197515429383887781149 5193824068286018957917931)
        ·
          refine ⟨7790736102429028436876897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5193824068286018957917931 7790736102429028436876897)
          ·
            refine ⟨5843052076821771327657673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7790736102429028436876897 5843052076821771327657673)
            ·
              refine ⟨4382289057616328495743255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5843052076821771327657673 4382289057616328495743255)
              ·
                refine ⟨6573433586424492743614883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4382289057616328495743255 6573433586424492743614883)
                ·
                  refine ⟨9860150379636739115422325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6573433586424492743614883 9860150379636739115422325)
                  ·
                    refine ⟨924389098090944292070843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9860150379636739115422325 924389098090944292070843)
                    ·
                      rfl

theorem cell23_5400724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_5400724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400724 prefixEnd_5400724 := by exact prefixLift 5400724
  have htrace : WordTrace (prefixWord ++ tailWord_5400724) baseStart_5400724 baseEnd_5400724 := by
    simpa [prefixWord, tailWord_5400724, baseEnd_5400724] using wordTrace_append hprefix tailTrace_5400724
  have hstable : (prefixWord ++ tailWord_5400724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400724).length < 2 ^ (prefixWord ++ tailWord_5400724).sum := by decide
  have hdescent : baseEnd_5400724 < baseStart_5400724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400727 : List Nat := [1, 1, 3, 3, 4, 2, 2, 1, 1, 1, 4]
def baseStart_5400727 : Nat := 118140960795 + 5400727 * 2 ^ 59
def prefixEnd_5400727 : Nat := 4983230072969 + 3 ^ 40 * 5400727 * 2
def baseEnd_5400727 : Nat := 2773168834714796364475015

theorem tailTrace_5400727 : CollatzResearch.WordTrace tailWord_5400727 prefixEnd_5400727 2773168834714796364475015 := by
  unfold tailWord_5400727
  simp only [CollatzResearch.WordTrace]
  refine ⟨196980696305095924583024435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131320464203397283055349623 196980696305095924583024435)
  ·
    refine ⟨295471044457643886874536653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196980696305095924583024435 295471044457643886874536653)
    ·
      refine ⟨110801641671616457577951245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295471044457643886874536653 110801641671616457577951245)
      ·
        refine ⟨41550615626856171591731717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110801641671616457577951245 41550615626856171591731717)
        ·
          refine ⟨7790740430035532173449697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41550615626856171591731717 7790740430035532173449697)
          ·
            refine ⟨5843055322526649130087273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7790740430035532173449697 5843055322526649130087273)
            ·
              refine ⟨4382291491894986847565455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5843055322526649130087273 4382291491894986847565455)
              ·
                refine ⟨6573437237842480271348183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4382291491894986847565455 6573437237842480271348183)
                ·
                  refine ⟨9860155856763720407022275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6573437237842480271348183 9860155856763720407022275)
                  ·
                    refine ⟨14790233785145580610533413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9860155856763720407022275 14790233785145580610533413)
                    ·
                      refine ⟨2773168834714796364475015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14790233785145580610533413 2773168834714796364475015)
                      ·
                        rfl

theorem cell23_5400727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_5400727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400727 prefixEnd_5400727 := by exact prefixLift 5400727
  have htrace : WordTrace (prefixWord ++ tailWord_5400727) baseStart_5400727 baseEnd_5400727 := by
    simpa [prefixWord, tailWord_5400727, baseEnd_5400727] using wordTrace_append hprefix tailTrace_5400727
  have hstable : (prefixWord ++ tailWord_5400727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400727).length < 2 ^ (prefixWord ++ tailWord_5400727).sum := by decide
  have hdescent : baseEnd_5400727 < baseStart_5400727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400757 : List Nat := [1, 3, 3, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_5400757 : Nat := 118140960795 + 5400757 * 2 ^ 59
def prefixEnd_5400757 : Nat := 4983230072969 + 3 ^ 40 * 5400757 * 2
def baseEnd_5400757 : Nat := 2773184239134431247099877

theorem tailTrace_5400757 : CollatzResearch.WordTrace tailWord_5400757 prefixEnd_5400757 2773184239134431247099877 := by
  unfold tailWord_5400757
  simp only [CollatzResearch.WordTrace]
  refine ⟨196981790494987239706616525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131321193663324826471077683 196981790494987239706616525)
  ·
    refine ⟨73868171435620214889981197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196981790494987239706616525 73868171435620214889981197)
    ·
      refine ⟨27700564288357580583742949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73868171435620214889981197 27700564288357580583742949)
      ·
        refine ⟨5193855804067046359451803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27700564288357580583742949 5193855804067046359451803)
        ·
          refine ⟨7790783706100569539177705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5193855804067046359451803 7790783706100569539177705)
          ·
            refine ⟨5843087779575427154383279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7790783706100569539177705 5843087779575427154383279)
            ·
              refine ⟨8764631669363140731574919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5843087779575427154383279 8764631669363140731574919)
              ·
                refine ⟨13146947504044711097362379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8764631669363140731574919 13146947504044711097362379)
                ·
                  refine ⟨19720421256067066646043569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13146947504044711097362379 19720421256067066646043569)
                  ·
                    refine ⟨14790315942050299984532677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19720421256067066646043569 14790315942050299984532677)
                    ·
                      refine ⟨2773184239134431247099877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14790315942050299984532677 2773184239134431247099877)
                      ·
                        rfl

theorem cell23_5400757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_5400757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400757 prefixEnd_5400757 := by exact prefixLift 5400757
  have htrace : WordTrace (prefixWord ++ tailWord_5400757) baseStart_5400757 baseEnd_5400757 := by
    simpa [prefixWord, tailWord_5400757, baseEnd_5400757] using wordTrace_append hprefix tailTrace_5400757
  have hstable : (prefixWord ++ tailWord_5400757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400757).length < 2 ^ (prefixWord ++ tailWord_5400757).sum := by decide
  have hdescent : baseEnd_5400757 < baseStart_5400757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400783 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 3, 4, 2]
def baseStart_5400783 : Nat := 118140960795 + 5400783 * 2 ^ 59
def prefixEnd_5400783 : Nat := 4983230072969 + 3 ^ 40 * 5400783 * 2
def baseEnd_5400783 : Nat := 2773197589631448145374757

theorem tailTrace_5400783 : CollatzResearch.WordTrace tailWord_5400783 prefixEnd_5400783 2773197589631448145374757 := by
  unfold tailWord_5400783
  simp only [CollatzResearch.WordTrace]
  refine ⟨196982738792893046147063003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131321825861928697431375335 196982738792893046147063003)
  ·
    refine ⟨295474108189339569220594505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196982738792893046147063003 295474108189339569220594505)
    ·
      refine ⟨221605581142004676915445879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295474108189339569220594505 221605581142004676915445879)
      ·
        refine ⟨332408371713007015373168819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221605581142004676915445879 332408371713007015373168819)
        ·
          refine ⟨498612557569510523059753229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332408371713007015373168819 498612557569510523059753229)
          ·
            refine ⟨186979709088566446147407461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 498612557569510523059753229 186979709088566446147407461)
            ·
              refine ⟨35058695454106208652638899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186979709088566446147407461 35058695454106208652638899)
              ·
                refine ⟨52588043181159312978958349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35058695454106208652638899 52588043181159312978958349)
                ·
                  refine ⟨19720516192934742367109381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52588043181159312978958349 19720516192934742367109381)
                  ·
                    refine ⟨3697596786175264193833009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19720516192934742367109381 3697596786175264193833009)
                    ·
                      refine ⟨2773197589631448145374757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3697596786175264193833009 2773197589631448145374757)
                      ·
                        rfl

theorem cell23_5400783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 4, 2].length) (baseStart_5400783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400783 prefixEnd_5400783 := by exact prefixLift 5400783
  have htrace : WordTrace (prefixWord ++ tailWord_5400783) baseStart_5400783 baseEnd_5400783 := by
    simpa [prefixWord, tailWord_5400783, baseEnd_5400783] using wordTrace_append hprefix tailTrace_5400783
  have hstable : (prefixWord ++ tailWord_5400783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400783).length < 2 ^ (prefixWord ++ tailWord_5400783).sum := by decide
  have hdescent : baseEnd_5400783 < baseStart_5400783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400800 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 4, 2, 2]
def baseStart_5400800 : Nat := 118140960795 + 5400800 * 2 ^ 59
def prefixEnd_5400800 : Nat := 4983230072969 + 3 ^ 40 * 5400800 * 2
def baseEnd_5400800 : Nat := 2773206318802574578862179

theorem tailTrace_5400800 : CollatzResearch.WordTrace tailWord_5400800 prefixEnd_5400800 2773206318802574578862179 := by
  unfold tailWord_5400800
  simp only [CollatzResearch.WordTrace]
  refine ⟨98491679416915729025215927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131322239222554305366954569 98491679416915729025215927)
  ·
    refine ⟨147737519125373593537823891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98491679416915729025215927 147737519125373593537823891)
    ·
      refine ⟨221606278688060390306735837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147737519125373593537823891 221606278688060390306735837)
      ·
        refine ⟨83102354508022646365025939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221606278688060390306735837 83102354508022646365025939)
        ·
          refine ⟨124653531762033969547538909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83102354508022646365025939 124653531762033969547538909)
          ·
            refine ⟨46745074410762738580327091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124653531762033969547538909 46745074410762738580327091)
            ·
              refine ⟨70117611616144107870490637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46745074410762738580327091 70117611616144107870490637)
              ·
                refine ⟨26294104356054040451433989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70117611616144107870490637 26294104356054040451433989)
                ·
                  refine ⟨4930144566760132584643873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26294104356054040451433989 4930144566760132584643873)
                  ·
                    refine ⟨3697608425070099438482905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4930144566760132584643873 3697608425070099438482905)
                    ·
                      refine ⟨2773206318802574578862179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3697608425070099438482905 2773206318802574578862179)
                      ·
                        rfl

theorem cell23_5400800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_5400800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400800 prefixEnd_5400800 := by exact prefixLift 5400800
  have htrace : WordTrace (prefixWord ++ tailWord_5400800) baseStart_5400800 baseEnd_5400800 := by
    simpa [prefixWord, tailWord_5400800, baseEnd_5400800] using wordTrace_append hprefix tailTrace_5400800
  have hstable : (prefixWord ++ tailWord_5400800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400800).length < 2 ^ (prefixWord ++ tailWord_5400800).sum := by decide
  have hdescent : baseEnd_5400800 < baseStart_5400800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400853 : List Nat := [1, 3, 2, 1, 2, 1, 4, 2, 2, 5]
def baseStart_5400853 : Nat := 118140960795 + 5400853 * 2 ^ 59
def prefixEnd_5400853 : Nat := 4983230072969 + 3 ^ 40 * 5400853 * 2
def baseEnd_5400853 : Nat := 924411177759087623833145

theorem tailTrace_5400853 : CollatzResearch.WordTrace tailWord_5400853 prefixEnd_5400853 924411177759087623833145 := by
  unfold tailWord_5400853
  simp only [CollatzResearch.WordTrace]
  refine ⟨196985291902639448102111213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131323527935092965401407475 196985291902639448102111213)
  ·
    refine ⟨73869484463489793038291705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196985291902639448102111213 73869484463489793038291705)
    ·
      refine ⟨55402113347617344778718779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73869484463489793038291705 55402113347617344778718779)
      ·
        refine ⟨83103170021426017168078169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55402113347617344778718779 83103170021426017168078169)
        ·
          refine ⟨62327377516069512876058627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83103170021426017168078169 62327377516069512876058627)
          ·
            refine ⟨93491066274104269314087941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62327377516069512876058627 93491066274104269314087941)
            ·
              refine ⟨17529574926394550496391489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93491066274104269314087941 17529574926394550496391489)
              ·
                refine ⟨13147181194795912872293617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17529574926394550496391489 13147181194795912872293617)
                ·
                  refine ⟨9860385896096934654220213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13147181194795912872293617 9860385896096934654220213)
                  ·
                    refine ⟨924411177759087623833145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9860385896096934654220213 924411177759087623833145)
                    ·
                      rfl

theorem cell23_5400853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_5400853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400853 prefixEnd_5400853 := by exact prefixLift 5400853
  have htrace : WordTrace (prefixWord ++ tailWord_5400853) baseStart_5400853 baseEnd_5400853 := by
    simpa [prefixWord, tailWord_5400853, baseEnd_5400853] using wordTrace_append hprefix tailTrace_5400853
  have hstable : (prefixWord ++ tailWord_5400853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400853).length < 2 ^ (prefixWord ++ tailWord_5400853).sum := by decide
  have hdescent : baseEnd_5400853 < baseStart_5400853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400863 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 5]
def baseStart_5400863 : Nat := 118140960795 + 5400863 * 2 ^ 59
def prefixEnd_5400863 : Nat := 4983230072969 + 3 ^ 40 * 5400863 * 2
def baseEnd_5400863 : Nat := 2773238668083807832374389

theorem tailTrace_5400863 : CollatzResearch.WordTrace tailWord_5400863 prefixEnd_5400863 2773238668083807832374389 := by
  unfold tailWord_5400863
  simp only [CollatzResearch.WordTrace]
  refine ⟨196985656632603219809975243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131323771088402146539983495 196985656632603219809975243)
  ·
    refine ⟨295478484948904829714962865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196985656632603219809975243 295478484948904829714962865)
    ·
      refine ⟨221608863711678622286222149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295478484948904829714962865 221608863711678622286222149)
      ·
        refine ⟨41551661945939741678666653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221608863711678622286222149 41551661945939741678666653)
        ·
          refine ⟨15581873229727403129499995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41551661945939741678666653 15581873229727403129499995)
          ·
            refine ⟨23372809844591104694249993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15581873229727403129499995 23372809844591104694249993)
            ·
              refine ⟨17529607383443328520687495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23372809844591104694249993 17529607383443328520687495)
              ·
                refine ⟨26294411075164992781031243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17529607383443328520687495 26294411075164992781031243)
                ·
                  refine ⟨39441616612747489171546865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26294411075164992781031243 39441616612747489171546865)
                  ·
                    refine ⟨29581212459560616878660149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39441616612747489171546865 29581212459560616878660149)
                    ·
                      refine ⟨2773238668083807832374389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29581212459560616878660149 2773238668083807832374389)
                      ·
                        rfl

theorem cell23_5400863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_5400863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400863 prefixEnd_5400863 := by exact prefixLift 5400863
  have htrace : WordTrace (prefixWord ++ tailWord_5400863) baseStart_5400863 baseEnd_5400863 := by
    simpa [prefixWord, tailWord_5400863, baseEnd_5400863] using wordTrace_append hprefix tailTrace_5400863
  have hstable : (prefixWord ++ tailWord_5400863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400863).length < 2 ^ (prefixWord ++ tailWord_5400863).sum := by decide
  have hdescent : baseEnd_5400863 < baseStart_5400863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400890 : List Nat := [3, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4]
def baseStart_5400890 : Nat := 118140960795 + 5400890 * 2 ^ 59
def prefixEnd_5400890 : Nat := 4983230072969 + 3 ^ 40 * 5400890 * 2
def baseEnd_5400890 : Nat := 2773252532061479226736765

theorem tailTrace_5400890 : CollatzResearch.WordTrace tailWord_5400890 prefixEnd_5400890 2773252532061479226736765 := by
  unfold tailWord_5400890
  simp only [CollatzResearch.WordTrace]
  refine ⟨49246660350876350855302031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131324427602336935614138749 49246660350876350855302031)
  ·
    refine ⟨73869990526314526282953047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49246660350876350855302031 73869990526314526282953047)
    ·
      refine ⟨110804985789471789424429571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73869990526314526282953047 110804985789471789424429571)
      ·
        refine ⟨166207478684207684136644357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110804985789471789424429571 166207478684207684136644357)
        ·
          refine ⟨31163902253288940775620817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166207478684207684136644357 31163902253288940775620817)
          ·
            refine ⟨23372926689966705581715613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31163902253288940775620817 23372926689966705581715613)
            ·
              refine ⟨8764847508737514593143355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23372926689966705581715613 8764847508737514593143355)
              ·
                refine ⟨13147271263106271889715033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8764847508737514593143355 13147271263106271889715033)
                ·
                  refine ⟨9860453447329703917286275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13147271263106271889715033 9860453447329703917286275)
                  ·
                    refine ⟨14790680170994555875929413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9860453447329703917286275 14790680170994555875929413)
                    ·
                      refine ⟨2773252532061479226736765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14790680170994555875929413 2773252532061479226736765)
                      ·
                        rfl

theorem cell23_5400890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_5400890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400890 prefixEnd_5400890 := by exact prefixLift 5400890
  have htrace : WordTrace (prefixWord ++ tailWord_5400890) baseStart_5400890 baseEnd_5400890 := by
    simpa [prefixWord, tailWord_5400890, baseEnd_5400890] using wordTrace_append hprefix tailTrace_5400890
  have hstable : (prefixWord ++ tailWord_5400890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400890).length < 2 ^ (prefixWord ++ tailWord_5400890).sum := by decide
  have hdescent : baseEnd_5400890 < baseStart_5400890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400913 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 8]
def baseStart_5400913 : Nat := 118140960795 + 5400913 * 2 ^ 59
def prefixEnd_5400913 : Nat := 4983230072969 + 3 ^ 40 * 5400913 * 2
def baseEnd_5400913 : Nat := 308140482457392515194351

theorem tailTrace_5400913 : CollatzResearch.WordTrace tailWord_5400913 prefixEnd_5400913 308140482457392515194351 := by
  unfold tailWord_5400913
  simp only [CollatzResearch.WordTrace]
  refine ⟨196987480282422078349295393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131324986854948052232863595 196987480282422078349295393)
  ·
    refine ⟨147740610211816558761971545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196987480282422078349295393 147740610211816558761971545)
    ·
      refine ⟨110805457658862419071478659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147740610211816558761971545 110805457658862419071478659)
      ·
        refine ⟨166208186488293628607217989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110805457658862419071478659 166208186488293628607217989)
        ·
          refine ⟨31164034966555055363853373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166208186488293628607217989 31164034966555055363853373)
          ·
            refine ⟨11686513112458145761445015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31164034966555055363853373 11686513112458145761445015)
            ·
              refine ⟨17529769668687218642167523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11686513112458145761445015 17529769668687218642167523)
              ·
                refine ⟨26294654503030827963251285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17529769668687218642167523 26294654503030827963251285)
                ·
                  refine ⟨308140482457392515194351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26294654503030827963251285 308140482457392515194351)
                  ·
                    rfl

theorem cell23_5400913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 8].length) (baseStart_5400913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400913 prefixEnd_5400913 := by exact prefixLift 5400913
  have htrace : WordTrace (prefixWord ++ tailWord_5400913) baseStart_5400913 baseEnd_5400913 := by
    simpa [prefixWord, tailWord_5400913, baseEnd_5400913] using wordTrace_append hprefix tailTrace_5400913
  have hstable : (prefixWord ++ tailWord_5400913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400913).length < 2 ^ (prefixWord ++ tailWord_5400913).sum := by decide
  have hdescent : baseEnd_5400913 < baseStart_5400913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400917 : List Nat := [1, 3, 2, 2, 4, 1, 2, 1, 3, 4]
def baseStart_5400917 : Nat := 118140960795 + 5400917 * 2 ^ 59
def prefixEnd_5400917 : Nat := 4983230072969 + 3 ^ 40 * 5400917 * 2
def baseEnd_5400917 : Nat := 924422132013050207033047

theorem tailTrace_5400917 : CollatzResearch.WordTrace tailWord_5400917 prefixEnd_5400917 924422132013050207033047 := by
  unfold tailWord_5400917
  simp only [CollatzResearch.WordTrace]
  refine ⟨196987626174407587032441005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131325084116271724688294003 196987626174407587032441005)
  ·
    refine ⟨73870359815402845137165377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196987626174407587032441005 73870359815402845137165377)
    ·
      refine ⟨55402769861552133852874033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73870359815402845137165377 55402769861552133852874033)
      ·
        refine ⟨41552077396164100389655525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55402769861552133852874033 41552077396164100389655525)
        ·
          refine ⟨7791014511780768823060411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41552077396164100389655525 7791014511780768823060411)
          ·
            refine ⟨11686521767671153234590617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7791014511780768823060411 11686521767671153234590617)
            ·
              refine ⟨8764891325753364925942963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11686521767671153234590617 8764891325753364925942963)
              ·
                refine ⟨13147336988630047388914445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8764891325753364925942963 13147336988630047388914445)
                ·
                  refine ⟨4930251370736267770842917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13147336988630047388914445 4930251370736267770842917)
                  ·
                    refine ⟨924422132013050207033047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4930251370736267770842917 924422132013050207033047)
                    ·
                      rfl

theorem cell23_5400917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_5400917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400917 prefixEnd_5400917 := by exact prefixLift 5400917
  have htrace : WordTrace (prefixWord ++ tailWord_5400917) baseStart_5400917 baseEnd_5400917 := by
    simpa [prefixWord, tailWord_5400917, baseEnd_5400917] using wordTrace_append hprefix tailTrace_5400917
  have hstable : (prefixWord ++ tailWord_5400917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400917).length < 2 ^ (prefixWord ++ tailWord_5400917).sum := by decide
  have hdescent : baseEnd_5400917 < baseStart_5400917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400967 : List Nat := [1, 1, 4, 2, 2, 1, 3, 2, 2, 3, 2]
def baseStart_5400967 : Nat := 118140960795 + 5400967 * 2 ^ 59
def prefixEnd_5400967 : Nat := 4983230072969 + 3 ^ 40 * 5400967 * 2
def baseEnd_5400967 : Nat := 2773292070071875425473911

theorem tailTrace_5400967 : CollatzResearch.WordTrace tailWord_5400967 prefixEnd_5400967 2773292070071875425473911 := by
  unfold tailWord_5400967
  simp only [CollatzResearch.WordTrace]
  refine ⟨196989449824226445571761155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131326299882817630381174103 196989449824226445571761155)
  ·
    refine ⟨295484174736339668357641733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196989449824226445571761155 295484174736339668357641733)
    ·
      refine ⟨55403282763063687817057825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 295484174736339668357641733 55403282763063687817057825)
      ·
        refine ⟨41552462072297765862793369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55403282763063687817057825 41552462072297765862793369)
        ·
          refine ⟨31164346554223324397095027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41552462072297765862793369 31164346554223324397095027)
          ·
            refine ⟨46746519831334986595642541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31164346554223324397095027 46746519831334986595642541)
            ·
              refine ⟨17529944936750619973365953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46746519831334986595642541 17529944936750619973365953)
              ·
                refine ⟨13147458702562964980024465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17529944936750619973365953 13147458702562964980024465)
                ·
                  refine ⟨9860594026922223735018349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13147458702562964980024465 9860594026922223735018349)
                  ·
                    refine ⟨3697722760095833900631881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9860594026922223735018349 3697722760095833900631881)
                    ·
                      refine ⟨2773292070071875425473911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3697722760095833900631881 2773292070071875425473911)
                      ·
                        rfl

theorem cell23_5400967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_5400967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400967 prefixEnd_5400967 := by exact prefixLift 5400967
  have htrace : WordTrace (prefixWord ++ tailWord_5400967) baseStart_5400967 baseEnd_5400967 := by
    simpa [prefixWord, tailWord_5400967, baseEnd_5400967] using wordTrace_append hprefix tailTrace_5400967
  have hstable : (prefixWord ++ tailWord_5400967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400967).length < 2 ^ (prefixWord ++ tailWord_5400967).sum := by decide
  have hdescent : baseEnd_5400967 < baseStart_5400967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400974 : List Nat := [4, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3]
def baseStart_5400974 : Nat := 118140960795 + 5400974 * 2 ^ 59
def prefixEnd_5400974 : Nat := 4983230072969 + 3 ^ 40 * 5400974 * 2
def baseEnd_5400974 : Nat := 2773295664436456898086379

theorem tailTrace_5400974 : CollatzResearch.WordTrace tailWord_5400974 prefixEnd_5400974 2773295664436456898086379 := by
  unfold tailWord_5400974
  simp only [CollatzResearch.WordTrace]
  refine ⟨24623713141900135720908247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131326470090134057178177317 24623713141900135720908247)
  ·
    refine ⟨36935569712850203581362371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24623713141900135720908247 36935569712850203581362371)
    ·
      refine ⟨55403354569275305372043557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36935569712850203581362371 55403354569275305372043557)
      ·
        refine ⟨10388128981739119757258167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55403354569275305372043557 10388128981739119757258167)
        ·
          refine ⟨15582193472608679635887251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10388128981739119757258167 15582193472608679635887251)
          ·
            refine ⟨23373290208913019453830877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15582193472608679635887251 23373290208913019453830877)
            ·
              refine ⟨8764983828342382295186579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23373290208913019453830877 8764983828342382295186579)
              ·
                refine ⟨13147475742513573442779869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8764983828342382295186579 13147475742513573442779869)
                ·
                  refine ⟨4930303403442590041042451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13147475742513573442779869 4930303403442590041042451)
                  ·
                    refine ⟨7395455105163885061563677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4930303403442590041042451 7395455105163885061563677)
                    ·
                      refine ⟨2773295664436456898086379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7395455105163885061563677 2773295664436456898086379)
                      ·
                        rfl

theorem cell23_5400974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_5400974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400974 prefixEnd_5400974 := by exact prefixLift 5400974
  have htrace : WordTrace (prefixWord ++ tailWord_5400974) baseStart_5400974 baseEnd_5400974 := by
    simpa [prefixWord, tailWord_5400974, baseEnd_5400974] using wordTrace_append hprefix tailTrace_5400974
  have hstable : (prefixWord ++ tailWord_5400974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400974).length < 2 ^ (prefixWord ++ tailWord_5400974).sum := by decide
  have hdescent : baseEnd_5400974 < baseStart_5400974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5400997 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 5, 2, 2]
def baseStart_5400997 : Nat := 118140960795 + 5400997 * 2 ^ 59
def prefixEnd_5400997 : Nat := 4983230072969 + 3 ^ 40 * 5400997 * 2
def baseEnd_5400997 : Nat := 2773307474491510308098773

theorem tailTrace_5400997 : CollatzResearch.WordTrace tailWord_5400997 prefixEnd_5400997 2773307474491510308098773 := by
  unfold tailWord_5400997
  simp only [CollatzResearch.WordTrace]
  refine ⟨196990544014117760695353245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131327029342745173796902163 196990544014117760695353245)
  ·
    refine ⟨73871454005294160260757467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196990544014117760695353245 73871454005294160260757467)
    ·
      refine ⟨110807181007941240391136201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73871454005294160260757467 110807181007941240391136201)
      ·
        refine ⟨83105385755955930293352151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110807181007941240391136201 83105385755955930293352151)
        ·
          refine ⟨124658078633933895440028227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83105385755955930293352151 124658078633933895440028227)
          ·
            refine ⟨186987117950900843160042341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124658078633933895440028227 186987117950900843160042341)
            ·
              refine ⟨35060084615793908092507939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186987117950900843160042341 35060084615793908092507939)
              ·
                refine ⟨52590126923690862138761909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35060084615793908092507939 52590126923690862138761909)
                ·
                  refine ⟨4930324399096018325508929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52590126923690862138761909 4930324399096018325508929)
                  ·
                    refine ⟨3697743299322013744131697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4930324399096018325508929 3697743299322013744131697)
                    ·
                      refine ⟨2773307474491510308098773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3697743299322013744131697 2773307474491510308098773)
                      ·
                        rfl

theorem cell23_5400997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_5400997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5400997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5400997 prefixEnd_5400997 := by exact prefixLift 5400997
  have htrace : WordTrace (prefixWord ++ tailWord_5400997) baseStart_5400997 baseEnd_5400997 := by
    simpa [prefixWord, tailWord_5400997, baseEnd_5400997] using wordTrace_append hprefix tailTrace_5400997
  have hstable : (prefixWord ++ tailWord_5400997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5400997).length < 2 ^ (prefixWord ++ tailWord_5400997).sum := by decide
  have hdescent : baseEnd_5400997 < baseStart_5400997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5400997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401010 : List Nat := [3, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_5401010 : Nat := 118140960795 + 5401010 * 2 ^ 59
def prefixEnd_5401010 : Nat := 4983230072969 + 3 ^ 40 * 5401010 * 2
def baseEnd_5401010 : Nat := 2773314149740018757236213

theorem tailTrace_5401010 : CollatzResearch.WordTrace tailWord_5401010 prefixEnd_5401010 2773314149740018757236213 := by
  unfold tailWord_5401010
  simp only [CollatzResearch.WordTrace]
  refine ⟨49247754540767665978894121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131327345442047109277050989 49247754540767665978894121)
  ·
    refine ⟨36935815905575749484170591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49247754540767665978894121 36935815905575749484170591)
    ·
      refine ⟨55403723858363624226255887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36935815905575749484170591 55403723858363624226255887)
      ·
        refine ⟨83105585787545436339383831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55403723858363624226255887 83105585787545436339383831)
        ·
          refine ⟨124658378681318154509075747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83105585787545436339383831 124658378681318154509075747)
          ·
            refine ⟨186987568021977231763613621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124658378681318154509075747 186987568021977231763613621)
            ·
              refine ⟨17530084502060365477838777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 186987568021977231763613621 17530084502060365477838777)
              ·
                refine ⟨13147563376545274108379083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17530084502060365477838777 13147563376545274108379083)
                ·
                  refine ⟨19721345064817911162568625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13147563376545274108379083 19721345064817911162568625)
                  ·
                    refine ⟨14791008798613433371926469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19721345064817911162568625 14791008798613433371926469)
                    ·
                      refine ⟨2773314149740018757236213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14791008798613433371926469 2773314149740018757236213)
                      ·
                        rfl

theorem cell23_5401010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_5401010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401010 prefixEnd_5401010 := by exact prefixLift 5401010
  have htrace : WordTrace (prefixWord ++ tailWord_5401010) baseStart_5401010 baseEnd_5401010 := by
    simpa [prefixWord, tailWord_5401010, baseEnd_5401010] using wordTrace_append hprefix tailTrace_5401010
  have hstable : (prefixWord ++ tailWord_5401010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401010).length < 2 ^ (prefixWord ++ tailWord_5401010).sum := by decide
  have hdescent : baseEnd_5401010 < baseStart_5401010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401017 : List Nat := [1, 2, 1, 4, 3, 3, 1, 1, 1, 1, 5]
def baseStart_5401017 : Nat := 118140960795 + 5401017 * 2 ^ 59
def prefixEnd_5401017 : Nat := 4983230072969 + 3 ^ 40 * 5401017 * 2
def baseEnd_5401017 : Nat := 2773317744104600229848681

theorem tailTrace_5401017 : CollatzResearch.WordTrace tailWord_5401017 prefixEnd_5401017 2773317744104600229848681 := by
  unfold tailWord_5401017
  simp only [CollatzResearch.WordTrace]
  refine ⟨196991273474045304111081305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131327515649363536074054203 196991273474045304111081305)
  ·
    refine ⟨147743455105533978083310979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196991273474045304111081305 147743455105533978083310979)
    ·
      refine ⟨221615182658300967124966469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147743455105533978083310979 221615182658300967124966469)
      ·
        refine ⟨41552846748431431335931213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221615182658300967124966469 41552846748431431335931213)
        ·
          refine ⟨15582317530661786750974205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41552846748431431335931213 15582317530661786750974205)
          ·
            refine ⟨5843369073998170031615327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15582317530661786750974205 5843369073998170031615327)
            ·
              refine ⟨8765053610997255047422991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5843369073998170031615327 8765053610997255047422991)
              ·
                refine ⟨13147580416495882571134487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8765053610997255047422991 13147580416495882571134487)
                ·
                  refine ⟨19721370624743823856701731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13147580416495882571134487 19721370624743823856701731)
                  ·
                    refine ⟨29582055937115735785052597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19721370624743823856701731 29582055937115735785052597)
                    ·
                      refine ⟨2773317744104600229848681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29582055937115735785052597 2773317744104600229848681)
                      ·
                        rfl

theorem cell23_5401017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_5401017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401017 prefixEnd_5401017 := by exact prefixLift 5401017
  have htrace : WordTrace (prefixWord ++ tailWord_5401017) baseStart_5401017 baseEnd_5401017 := by
    simpa [prefixWord, tailWord_5401017, baseEnd_5401017] using wordTrace_append hprefix tailTrace_5401017
  have hstable : (prefixWord ++ tailWord_5401017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401017).length < 2 ^ (prefixWord ++ tailWord_5401017).sum := by decide
  have hdescent : baseEnd_5401017 < baseStart_5401017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401025 : List Nat := [1, 2, 7, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_5401025 : Nat := 118140960795 + 5401025 * 2 ^ 59
def prefixEnd_5401025 : Nat := 4983230072969 + 3 ^ 40 * 5401025 * 2
def baseEnd_5401025 : Nat := 2773321851949836198548645

theorem tailTrace_5401025 : CollatzResearch.WordTrace tailWord_5401025 prefixEnd_5401025 2773321851949836198548645 := by
  unfold tailWord_5401025
  simp only [CollatzResearch.WordTrace]
  refine ⟨196991565258016321477372529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131327710172010880984915019 196991565258016321477372529)
  ·
    refine ⟨147743673943512241108029397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196991565258016321477372529 147743673943512241108029397)
    ·
      refine ⟨3462742358051068150969439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 147743673943512241108029397 3462742358051068150969439)
      ·
        refine ⟨5194113537076602226454159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3462742358051068150969439 5194113537076602226454159)
        ·
          refine ⟨7791170305614903339681239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5194113537076602226454159 7791170305614903339681239)
          ·
            refine ⟨11686755458422355009521859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7791170305614903339681239 11686755458422355009521859)
            ·
              refine ⟨17530133187633532514282789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11686755458422355009521859 17530133187633532514282789)
              ·
                refine ⟨3286899972681287346428023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17530133187633532514282789 3286899972681287346428023)
                ·
                  refine ⟨4930349959021931019642035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3286899972681287346428023 4930349959021931019642035)
                  ·
                    refine ⟨7395524938532896529463053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4930349959021931019642035 7395524938532896529463053)
                    ·
                      refine ⟨2773321851949836198548645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7395524938532896529463053 2773321851949836198548645)
                      ·
                        rfl

theorem cell23_5401025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_5401025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401025 prefixEnd_5401025 := by exact prefixLift 5401025
  have htrace : WordTrace (prefixWord ++ tailWord_5401025) baseStart_5401025 baseEnd_5401025 := by
    simpa [prefixWord, tailWord_5401025, baseEnd_5401025] using wordTrace_append hprefix tailTrace_5401025
  have hstable : (prefixWord ++ tailWord_5401025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401025).length < 2 ^ (prefixWord ++ tailWord_5401025).sum := by decide
  have hdescent : baseEnd_5401025 < baseStart_5401025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401031 : List Nat := [1, 1, 4, 1, 1, 5, 1, 4, 1, 2, 2]
def baseStart_5401031 : Nat := 118140960795 + 5401031 * 2 ^ 59
def prefixEnd_5401031 : Nat := 4983230072969 + 3 ^ 40 * 5401031 * 2
def baseEnd_5401031 : Nat := 2773324932833763175073617

theorem tailTrace_5401031 : CollatzResearch.WordTrace tailWord_5401031 prefixEnd_5401031 2773324932833763175073617 := by
  unfold tailWord_5401031
  simp only [CollatzResearch.WordTrace]
  refine ⟨196991784095994584502090947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131327856063996389668060631 196991784095994584502090947)
  ·
    refine ⟨295487676143991876753136421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196991784095994584502090947 295487676143991876753136421)
    ·
      refine ⟨55403939276998476891213079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 295487676143991876753136421 55403939276998476891213079)
      ·
        refine ⟨83105908915497715336819619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55403939276998476891213079 83105908915497715336819619)
        ·
          refine ⟨124658863373246573005229429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83105908915497715336819619 124658863373246573005229429)
          ·
            refine ⟨11686768441241866219240259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124658863373246573005229429 11686768441241866219240259)
            ·
              refine ⟨17530152661862799328860389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11686768441241866219240259 17530152661862799328860389)
              ·
                refine ⟨3286903624099274874161323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17530152661862799328860389 3286903624099274874161323)
                ·
                  refine ⟨4930355436148912311241985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3286903624099274874161323 4930355436148912311241985)
                  ·
                    refine ⟨3697766577111684233431489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4930355436148912311241985 3697766577111684233431489)
                    ·
                      refine ⟨2773324932833763175073617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3697766577111684233431489 2773324932833763175073617)
                      ·
                        rfl

theorem cell23_5401031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 1, 2, 2].length) (baseStart_5401031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401031 prefixEnd_5401031 := by exact prefixLift 5401031
  have htrace : WordTrace (prefixWord ++ tailWord_5401031) baseStart_5401031 baseEnd_5401031 := by
    simpa [prefixWord, tailWord_5401031, baseEnd_5401031] using wordTrace_append hprefix tailTrace_5401031
  have hstable : (prefixWord ++ tailWord_5401031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401031).length < 2 ^ (prefixWord ++ tailWord_5401031).sum := by decide
  have hdescent : baseEnd_5401031 < baseStart_5401031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401033 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 2, 7]
def baseStart_5401033 : Nat := 118140960795 + 5401033 * 2 ^ 59
def prefixEnd_5401033 : Nat := 4983230072969 + 3 ^ 40 * 5401033 * 2
def baseEnd_5401033 : Nat := 924441986598357389082869

theorem tailTrace_5401033 : CollatzResearch.WordTrace tailWord_5401033 prefixEnd_5401033 924441986598357389082869 := by
  unfold tailWord_5401033
  simp only [CollatzResearch.WordTrace]
  refine ⟨196991857041987338843663753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131327904694658225895775835 196991857041987338843663753)
  ·
    refine ⟨147743892781490504132747815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196991857041987338843663753 147743892781490504132747815)
    ·
      refine ⟨221615839172235756199121723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147743892781490504132747815 221615839172235756199121723)
      ·
        refine ⟨332423758758353634298682585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221615839172235756199121723 332423758758353634298682585)
        ·
          refine ⟨249317819068765225724011939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332423758758353634298682585 249317819068765225724011939)
          ·
            refine ⟨373976728603147838586017909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249317819068765225724011939 373976728603147838586017909)
            ·
              refine ⟨35060318306545109867439179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 373976728603147838586017909 35060318306545109867439179)
              ·
                refine ⟨52590477459817664801158769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35060318306545109867439179 52590477459817664801158769)
                ·
                  refine ⟨39442858094863248600869077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52590477459817664801158769 39442858094863248600869077)
                  ·
                    refine ⟨924441986598357389082869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39442858094863248600869077 924441986598357389082869)
                    ·
                      rfl

theorem cell23_5401033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 7].length) (baseStart_5401033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401033 prefixEnd_5401033 := by exact prefixLift 5401033
  have htrace : WordTrace (prefixWord ++ tailWord_5401033) baseStart_5401033 baseEnd_5401033 := by
    simpa [prefixWord, tailWord_5401033, baseEnd_5401033] using wordTrace_append hprefix tailTrace_5401033
  have hstable : (prefixWord ++ tailWord_5401033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401033).length < 2 ^ (prefixWord ++ tailWord_5401033).sum := by decide
  have hdescent : baseEnd_5401033 < baseStart_5401033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401040 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 1, 9, 2]
def baseStart_5401040 : Nat := 118140960795 + 5401040 * 2 ^ 59
def prefixEnd_5401040 : Nat := 4983230072969 + 3 ^ 40 * 5401040 * 2
def baseEnd_5401040 : Nat := 2773329554159653639861075

theorem tailTrace_5401040 : CollatzResearch.WordTrace tailWord_5401040 prefixEnd_5401040 2773329554159653639861075 := by
  unfold tailWord_5401040
  simp only [CollatzResearch.WordTrace]
  refine ⟨98496056176480989519584287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131328074901974652692779049 98496056176480989519584287)
  ·
    refine ⟨147744084264721484279376431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98496056176480989519584287 147744084264721484279376431)
    ·
      refine ⟨221616126397082226419064647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147744084264721484279376431 221616126397082226419064647)
      ·
        refine ⟨332424189595623339628596971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221616126397082226419064647 332424189595623339628596971)
        ·
          refine ⟨498636284393435009442895457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332424189595623339628596971 498636284393435009442895457)
          ·
            refine ⟨373977213295076257082171593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 498636284393435009442895457 373977213295076257082171593)
            ·
              refine ⟨280482909971307192811628695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373977213295076257082171593 280482909971307192811628695)
              ·
                refine ⟨420724364956960789217443043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280482909971307192811628695 420724364956960789217443043)
                ·
                  refine ⟨631086547435441183826164565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 420724364956960789217443043 631086547435441183826164565)
                  ·
                    refine ⟨3697772738879538186481433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 631086547435441183826164565 3697772738879538186481433)
                    ·
                      refine ⟨2773329554159653639861075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3697772738879538186481433 2773329554159653639861075)
                      ·
                        rfl

theorem cell23_5401040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 9, 2].length) (baseStart_5401040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401040 prefixEnd_5401040 := by exact prefixLift 5401040
  have htrace : WordTrace (prefixWord ++ tailWord_5401040) baseStart_5401040 baseEnd_5401040 := by
    simpa [prefixWord, tailWord_5401040, baseEnd_5401040] using wordTrace_append hprefix tailTrace_5401040
  have hstable : (prefixWord ++ tailWord_5401040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401040).length < 2 ^ (prefixWord ++ tailWord_5401040).sum := by decide
  have hdescent : baseEnd_5401040 < baseStart_5401040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401057 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 3, 3, 2]
def baseStart_5401057 : Nat := 118140960795 + 5401057 * 2 ^ 59
def prefixEnd_5401057 : Nat := 4983230072969 + 3 ^ 40 * 5401057 * 2
def baseEnd_5401057 : Nat := 2773338283330780073348497

theorem tailTrace_5401057 : CollatzResearch.WordTrace tailWord_5401057 prefixEnd_5401057 2773338283330780073348497 := by
  unfold tailWord_5401057
  simp only [CollatzResearch.WordTrace]
  refine ⟨196992732393900390942537425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131328488262600260628358283 196992732393900390942537425)
  ·
    refine ⟨147744549295425293206903069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196992732393900390942537425 147744549295425293206903069)
    ·
      refine ⟨55404205985784484952588651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147744549295425293206903069 55404205985784484952588651)
      ·
        refine ⟨83106308978676727428882977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55404205985784484952588651 83106308978676727428882977)
        ·
          refine ⟨62329731734007545571662233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83106308978676727428882977 62329731734007545571662233)
          ·
            refine ⟨46747298800505659178746675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62329731734007545571662233 46747298800505659178746675)
            ·
              refine ⟨70120948200758488768120013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46747298800505659178746675 70120948200758488768120013)
              ·
                refine ⟨26295355575284433288045005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70120948200758488768120013 26295355575284433288045005)
                ·
                  refine ⟨9860758340731662483016877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26295355575284433288045005 9860758340731662483016877)
                  ·
                    refine ⟨3697784377774373431131329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9860758340731662483016877 3697784377774373431131329)
                    ·
                      refine ⟨2773338283330780073348497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3697784377774373431131329 2773338283330780073348497)
                      ·
                        rfl

theorem cell23_5401057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_5401057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401057 prefixEnd_5401057 := by exact prefixLift 5401057
  have htrace : WordTrace (prefixWord ++ tailWord_5401057) baseStart_5401057 baseEnd_5401057 := by
    simpa [prefixWord, tailWord_5401057, baseEnd_5401057] using wordTrace_append hprefix tailTrace_5401057
  have hstable : (prefixWord ++ tailWord_5401057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401057).length < 2 ^ (prefixWord ++ tailWord_5401057).sum := by decide
  have hdescent : baseEnd_5401057 < baseStart_5401057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401083 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 6]
def baseStart_5401083 : Nat := 118140960795 + 5401083 * 2 ^ 59
def prefixEnd_5401083 : Nat := 4983230072969 + 3 ^ 40 * 5401083 * 2
def baseEnd_5401083 : Nat := 2773351633827796971623377

theorem tailTrace_5401083 : CollatzResearch.WordTrace tailWord_5401083 prefixEnd_5401083 2773351633827796971623377 := by
  unfold tailWord_5401083
  simp only [CollatzResearch.WordTrace]
  refine ⟨196993680691806197382983903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131329120461204131588655935 196993680691806197382983903)
  ·
    refine ⟨295490521037709296074475855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196993680691806197382983903 295490521037709296074475855)
    ·
      refine ⟨443235781556563944111713783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295490521037709296074475855 443235781556563944111713783)
      ·
        refine ⟨664853672334845916167570675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443235781556563944111713783 664853672334845916167570675)
        ·
          refine ⟨997280508502268874251356013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 664853672334845916167570675 997280508502268874251356013)
          ·
            refine ⟨373980190688350827844258505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 997280508502268874251356013 373980190688350827844258505)
            ·
              refine ⟨280485143016263120883193879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373980190688350827844258505 280485143016263120883193879)
              ·
                refine ⟨420727714524394681324790819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280485143016263120883193879 420727714524394681324790819)
                ·
                  refine ⟨631091571786592021987186229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 420727714524394681324790819 631091571786592021987186229)
                  ·
                    refine ⟨59164834854993002061298709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 631091571786592021987186229 59164834854993002061298709)
                    ·
                      refine ⟨2773351633827796971623377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59164834854993002061298709 2773351633827796971623377)
                      ·
                        rfl

theorem cell23_5401083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 6].length) (baseStart_5401083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401083 prefixEnd_5401083 := by exact prefixLift 5401083
  have htrace : WordTrace (prefixWord ++ tailWord_5401083) baseStart_5401083 baseEnd_5401083 := by
    simpa [prefixWord, tailWord_5401083, baseEnd_5401083] using wordTrace_append hprefix tailTrace_5401083
  have hstable : (prefixWord ++ tailWord_5401083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401083).length < 2 ^ (prefixWord ++ tailWord_5401083).sum := by decide
  have hdescent : baseEnd_5401083 < baseStart_5401083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401108 : List Nat := [2, 4, 3, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_5401108 : Nat := 118140960795 + 5401108 * 2 ^ 59
def prefixEnd_5401108 : Nat := 4983230072969 + 3 ^ 40 * 5401108 * 2
def baseEnd_5401108 : Nat := 2773364470844159373810763

theorem tailTrace_5401108 : CollatzResearch.WordTrace tailWord_5401108 prefixEnd_5401108 2773364470844159373810763 := by
  unfold tailWord_5401108
  simp only [CollatzResearch.WordTrace]
  refine ⟨98497296258357813326321989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131329728344477084435095985 98497296258357813326321989)
  ·
    refine ⟨18468243048442089998685373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98497296258357813326321989 18468243048442089998685373)
    ·
      refine ⟨6925591143165783749507015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18468243048442089998685373 6925591143165783749507015)
      ·
        refine ⟨10388386714748675624260523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6925591143165783749507015 10388386714748675624260523)
        ·
          refine ⟨15582580072123013436390785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10388386714748675624260523 15582580072123013436390785)
          ·
            refine ⟨11686935054092260077293089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15582580072123013436390785 11686935054092260077293089)
            ·
              refine ⟨8765201290569195057969817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11686935054092260077293089 8765201290569195057969817)
              ·
                refine ⟨6573900967926896293477363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8765201290569195057969817 6573900967926896293477363)
                ·
                  refine ⟨9860851451890344440216045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6573900967926896293477363 9860851451890344440216045)
                  ·
                    refine ⟨3697819294458879165081017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9860851451890344440216045 3697819294458879165081017)
                    ·
                      refine ⟨2773364470844159373810763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3697819294458879165081017 2773364470844159373810763)
                      ·
                        rfl

theorem cell23_5401108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_5401108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401108 prefixEnd_5401108 := by exact prefixLift 5401108
  have htrace : WordTrace (prefixWord ++ tailWord_5401108) baseStart_5401108 baseEnd_5401108 := by
    simpa [prefixWord, tailWord_5401108, baseEnd_5401108] using wordTrace_append hprefix tailTrace_5401108
  have hstable : (prefixWord ++ tailWord_5401108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401108).length < 2 ^ (prefixWord ++ tailWord_5401108).sum := by decide
  have hdescent : baseEnd_5401108 < baseStart_5401108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401124 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 2, 1, 5]
def baseStart_5401124 : Nat := 118140960795 + 5401124 * 2 ^ 59
def prefixEnd_5401124 : Nat := 4983230072969 + 3 ^ 40 * 5401124 * 2
def baseEnd_5401124 : Nat := 2773372686534631311210689

theorem tailTrace_5401124 : CollatzResearch.WordTrace tailWord_5401124 prefixEnd_5401124 2773372686534631311210689 := by
  unfold tailWord_5401124
  simp only [CollatzResearch.WordTrace]
  refine ⟨98497588042328830692613213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131330117389771774256817617 98497588042328830692613213)
  ·
    refine ⟨36936595515873311509729955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98497588042328830692613213 36936595515873311509729955)
    ·
      refine ⟨55404893273809967264594933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36936595515873311509729955 55404893273809967264594933)
      ·
        refine ⟨5194208744419684431055775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55404893273809967264594933 5194208744419684431055775)
        ·
          refine ⟨7791313116629526646583663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5194208744419684431055775 7791313116629526646583663)
          ·
            refine ⟨11686969674944289969875495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7791313116629526646583663 11686969674944289969875495)
            ·
              refine ⟨17530454512416434954813243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11686969674944289969875495 17530454512416434954813243)
              ·
                refine ⟨26295681768624652432219865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17530454512416434954813243 26295681768624652432219865)
                ·
                  refine ⟨19721761326468489324164899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26295681768624652432219865 19721761326468489324164899)
                  ·
                    refine ⟨29582641989702733986247349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19721761326468489324164899 29582641989702733986247349)
                    ·
                      refine ⟨2773372686534631311210689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29582641989702733986247349 2773372686534631311210689)
                      ·
                        rfl

theorem cell23_5401124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_5401124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401124 prefixEnd_5401124 := by exact prefixLift 5401124
  have htrace : WordTrace (prefixWord ++ tailWord_5401124) baseStart_5401124 baseEnd_5401124 := by
    simpa [prefixWord, tailWord_5401124, baseEnd_5401124] using wordTrace_append hprefix tailTrace_5401124
  have hstable : (prefixWord ++ tailWord_5401124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401124).length < 2 ^ (prefixWord ++ tailWord_5401124).sum := by decide
  have hdescent : baseEnd_5401124 < baseStart_5401124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401144 : List Nat := [2, 1, 2, 1, 4, 1, 5, 2, 5]
def baseStart_5401144 : Nat := 118140960795 + 5401144 * 2 ^ 59
def prefixEnd_5401144 : Nat := 4983230072969 + 3 ^ 40 * 5401144 * 2
def baseEnd_5401144 : Nat := 308153661794191248106733

theorem tailTrace_5401144 : CollatzResearch.WordTrace tailWord_5401144 prefixEnd_5401144 308153661794191248106733 := by
  unfold tailWord_5401144
  simp only [CollatzResearch.WordTrace]
  refine ⟨98497952772292602400477243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131330603696390136533969657 98497952772292602400477243)
  ·
    refine ⟨147746929158438903600715865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98497952772292602400477243 147746929158438903600715865)
    ·
      refine ⟨110810196868829177700536899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147746929158438903600715865 110810196868829177700536899)
      ·
        refine ⟨166215295303243766550805349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110810196868829177700536899 166215295303243766550805349)
        ·
          refine ⟨31165367869358206228276003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166215295303243766550805349 31165367869358206228276003)
          ·
            refine ⟨46748051804037309342414005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31165367869358206228276003 46748051804037309342414005)
            ·
              refine ⟨4382629856628497750851313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46748051804037309342414005 4382629856628497750851313)
              ·
                refine ⟨3286972392471373313138485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4382629856628497750851313 3286972392471373313138485)
                ·
                  refine ⟨308153661794191248106733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3286972392471373313138485 308153661794191248106733)
                  ·
                    rfl

theorem cell23_5401144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 5].length) (baseStart_5401144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401144 prefixEnd_5401144 := by exact prefixLift 5401144
  have htrace : WordTrace (prefixWord ++ tailWord_5401144) baseStart_5401144 baseEnd_5401144 := by
    simpa [prefixWord, tailWord_5401144, baseEnd_5401144] using wordTrace_append hprefix tailTrace_5401144
  have hstable : (prefixWord ++ tailWord_5401144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401144).length < 2 ^ (prefixWord ++ tailWord_5401144).sum := by decide
  have hdescent : baseEnd_5401144 < baseStart_5401144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401160 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_5401160 : Nat := 118140960795 + 5401160 * 2 ^ 59
def prefixEnd_5401160 : Nat := 4983230072969 + 3 ^ 40 * 5401160 * 2
def baseEnd_5401160 : Nat := 2773391171838193170360523

theorem tailTrace_5401160 : CollatzResearch.WordTrace tailWord_5401160 prefixEnd_5401160 2773391171838193170360523 := by
  unfold tailWord_5401160
  simp only [CollatzResearch.WordTrace]
  refine ⟨98498244556263619766768467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131330992741684826355691289 98498244556263619766768467)
  ·
    refine ⟨147747366834395429650152701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98498244556263619766768467 147747366834395429650152701)
    ·
      refine ⟨55405262562898286118807263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147747366834395429650152701 55405262562898286118807263)
      ·
        refine ⟨83107893844347429178210895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55405262562898286118807263 83107893844347429178210895)
        ·
          refine ⟨124661840766521143767316343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83107893844347429178210895 124661840766521143767316343)
          ·
            refine ⟨186992761149781715650974515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124661840766521143767316343 186992761149781715650974515)
            ·
              refine ⟨280489141724672573476461773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186992761149781715650974515 280489141724672573476461773)
              ·
                refine ⟨105183428146752215053673165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 280489141724672573476461773 105183428146752215053673165)
                ·
                  refine ⟨39443785555032080645127437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105183428146752215053673165 39443785555032080645127437)
                  ·
                    refine ⟨14791419583137030241922789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39443785555032080645127437 14791419583137030241922789)
                    ·
                      refine ⟨2773391171838193170360523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14791419583137030241922789 2773391171838193170360523)
                      ·
                        rfl

theorem cell23_5401160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_5401160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401160 prefixEnd_5401160 := by exact prefixLift 5401160
  have htrace : WordTrace (prefixWord ++ tailWord_5401160) baseStart_5401160 baseEnd_5401160 := by
    simpa [prefixWord, tailWord_5401160, baseEnd_5401160] using wordTrace_append hprefix tailTrace_5401160
  have hstable : (prefixWord ++ tailWord_5401160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401160).length < 2 ^ (prefixWord ++ tailWord_5401160).sum := by decide
  have hdescent : baseEnd_5401160 < baseStart_5401160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401177 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 6, 4, 2]
def baseStart_5401177 : Nat := 118140960795 + 5401177 * 2 ^ 59
def prefixEnd_5401177 : Nat := 4983230072969 + 3 ^ 40 * 5401177 * 2
def baseEnd_5401177 : Nat := 2773399901009319603847945

theorem tailTrace_5401177 : CollatzResearch.WordTrace tailWord_5401177 prefixEnd_5401177 2773399901009319603847945 := by
  unfold tailWord_5401177
  simp only [CollatzResearch.WordTrace]
  refine ⟨196997109153465651436905785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131331406102310434291270523 196997109153465651436905785)
  ·
    refine ⟨147747831865099238577679339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196997109153465651436905785 147747831865099238577679339)
    ·
      refine ⟨221621747797648857866519009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147747831865099238577679339 221621747797648857866519009)
      ·
        refine ⟨166216310848236643399889257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221621747797648857866519009 166216310848236643399889257)
        ·
          refine ⟨124662233136177482549916943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166216310848236643399889257 124662233136177482549916943)
          ·
            refine ⟨186993349704266223824875415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124662233136177482549916943 186993349704266223824875415)
            ·
              refine ⟨280490024556399335737313123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186993349704266223824875415 280490024556399335737313123)
              ·
                refine ⟨420735036834599003605969685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280490024556399335737313123 420735036834599003605969685)
                ·
                  refine ⟨19721954851621828294029829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 420735036834599003605969685 19721954851621828294029829)
                  ·
                    refine ⟨3697866534679092805130593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19721954851621828294029829 3697866534679092805130593)
                    ·
                      refine ⟨2773399901009319603847945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3697866534679092805130593 2773399901009319603847945)
                      ·
                        rfl

theorem cell23_5401177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 4, 2].length) (baseStart_5401177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401177 prefixEnd_5401177 := by exact prefixLift 5401177
  have htrace : WordTrace (prefixWord ++ tailWord_5401177) baseStart_5401177 baseEnd_5401177 := by
    simpa [prefixWord, tailWord_5401177, baseEnd_5401177] using wordTrace_append hprefix tailTrace_5401177
  have hstable : (prefixWord ++ tailWord_5401177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401177).length < 2 ^ (prefixWord ++ tailWord_5401177).sum := by decide
  have hdescent : baseEnd_5401177 < baseStart_5401177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401194 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 2, 4, 2]
def baseStart_5401194 : Nat := 118140960795 + 5401194 * 2 ^ 59
def prefixEnd_5401194 : Nat := 4983230072969 + 3 ^ 40 * 5401194 * 2
def baseEnd_5401194 : Nat := 2773408630180446037335367

theorem tailTrace_5401194 : CollatzResearch.WordTrace tailWord_5401194 prefixEnd_5401194 2773408630180446037335367 := by
  unfold tailWord_5401194
  simp only [CollatzResearch.WordTrace]
  refine ⟨49249432298601015835068659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131331819462936042226849757 49249432298601015835068659)
  ·
    refine ⟨73874148447901523752602989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49249432298601015835068659 73874148447901523752602989)
    ·
      refine ⟨27702805667963071407226121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73874148447901523752602989 27702805667963071407226121)
      ·
        refine ⟨20777104250972303555419591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27702805667963071407226121 20777104250972303555419591)
        ·
          refine ⟨31165656376458455333129387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20777104250972303555419591 31165656376458455333129387)
          ·
            refine ⟨46748484564687682999694081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31165656376458455333129387 46748484564687682999694081)
            ·
              refine ⟨35061363423515762249770561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46748484564687682999694081 35061363423515762249770561)
              ·
                refine ⟨26296022567636821687327921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35061363423515762249770561 26296022567636821687327921)
                ·
                  refine ⟨19722016925727616265495941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26296022567636821687327921 19722016925727616265495941)
                  ·
                    refine ⟨3697878173573928049780489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19722016925727616265495941 3697878173573928049780489)
                    ·
                      refine ⟨2773408630180446037335367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3697878173573928049780489 2773408630180446037335367)
                      ·
                        rfl

theorem cell23_5401194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_5401194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401194 prefixEnd_5401194 := by exact prefixLift 5401194
  have htrace : WordTrace (prefixWord ++ tailWord_5401194) baseStart_5401194 baseEnd_5401194 := by
    simpa [prefixWord, tailWord_5401194, baseEnd_5401194] using wordTrace_append hprefix tailTrace_5401194
  have hstable : (prefixWord ++ tailWord_5401194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401194).length < 2 ^ (prefixWord ++ tailWord_5401194).sum := by decide
  have hdescent : baseEnd_5401194 < baseStart_5401194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401217 : List Nat := [1, 2, 4, 2, 1, 1, 1, 5, 6]
def baseStart_5401217 : Nat := 118140960795 + 5401217 * 2 ^ 59
def prefixEnd_5401217 : Nat := 4983230072969 + 3 ^ 40 * 5401217 * 2
def baseEnd_5401217 : Nat := 308157826692833271927529

theorem tailTrace_5401217 : CollatzResearch.WordTrace tailWord_5401217 prefixEnd_5401217 308157826692833271927529 := by
  unfold tailWord_5401217
  simp only [CollatzResearch.WordTrace]
  refine ⟨196998568073320738268361905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131332378715547158845574603 196998568073320738268361905)
  ·
    refine ⟨147748926054990553701271429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196998568073320738268361905 147748926054990553701271429)
    ·
      refine ⟨27702923635310728818988393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147748926054990553701271429 27702923635310728818988393)
      ·
        refine ⟨20777192726483046614241295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27702923635310728818988393 20777192726483046614241295)
        ·
          refine ⟨31165789089724569921361943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20777192726483046614241295 31165789089724569921361943)
          ·
            refine ⟨46748683634586854882042915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31165789089724569921361943 46748683634586854882042915)
            ·
              refine ⟨70123025451880282323064373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46748683634586854882042915 70123025451880282323064373)
              ·
                refine ⟨6574033636113776467787285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70123025451880282323064373 6574033636113776467787285)
                ·
                  refine ⟨308157826692833271927529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6574033636113776467787285 308157826692833271927529)
                  ·
                    rfl

theorem cell23_5401217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 6].length) (baseStart_5401217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401217 prefixEnd_5401217 := by exact prefixLift 5401217
  have htrace : WordTrace (prefixWord ++ tailWord_5401217) baseStart_5401217 baseEnd_5401217 := by
    simpa [prefixWord, tailWord_5401217, baseEnd_5401217] using wordTrace_append hprefix tailTrace_5401217
  have hstable : (prefixWord ++ tailWord_5401217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401217).length < 2 ^ (prefixWord ++ tailWord_5401217).sum := by decide
  have hdescent : baseEnd_5401217 < baseStart_5401217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401260 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 1, 12]
def baseStart_5401260 : Nat := 118140960795 + 5401260 * 2 ^ 59
def prefixEnd_5401260 : Nat := 4983230072969 + 3 ^ 40 * 5401260 * 2
def baseEnd_5401260 : Nat := 924480839967880926370021

theorem tailTrace_5401260 : CollatzResearch.WordTrace tailWord_5401260 prefixEnd_5401260 924480839967880926370021 := by
  unfold tailWord_5401260
  simp only [CollatzResearch.WordTrace]
  refine ⟨98500068206082478306088617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131333424274776637741451489 98500068206082478306088617)
  ·
    refine ⟨73875051154561858729566463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98500068206082478306088617 73875051154561858729566463)
    ·
      refine ⟨110812576731842788094349695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73875051154561858729566463 110812576731842788094349695)
      ·
        refine ⟨166218865097764182141524543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110812576731842788094349695 166218865097764182141524543)
        ·
          refine ⟨249328297646646273212286815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166218865097764182141524543 249328297646646273212286815)
          ·
            refine ⟨373992446469969409818430223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249328297646646273212286815 373992446469969409818430223)
            ·
              refine ⟨560988669704954114727645335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373992446469969409818430223 560988669704954114727645335)
              ·
                refine ⟨841483004557431172091468003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560988669704954114727645335 841483004557431172091468003)
                ·
                  refine ⟨1262224506836146758137202005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841483004557431172091468003 1262224506836146758137202005)
                  ·
                    refine ⟨924480839967880926370021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1262224506836146758137202005 924480839967880926370021)
                    ·
                      rfl

theorem cell23_5401260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_5401260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401260 prefixEnd_5401260 := by exact prefixLift 5401260
  have htrace : WordTrace (prefixWord ++ tailWord_5401260) baseStart_5401260 baseEnd_5401260 := by
    simpa [prefixWord, tailWord_5401260, baseEnd_5401260] using wordTrace_append hprefix tailTrace_5401260
  have hstable : (prefixWord ++ tailWord_5401260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401260).length < 2 ^ (prefixWord ++ tailWord_5401260).sum := by decide
  have hdescent : baseEnd_5401260 < baseStart_5401260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401261 : List Nat := [1, 5, 2, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_5401261 : Nat := 118140960795 + 5401261 * 2 ^ 59
def prefixEnd_5401261 : Nat := 4983230072969 + 3 ^ 40 * 5401261 * 2
def baseEnd_5401261 : Nat := 2773443033384297275197559

theorem tailTrace_5401261 : CollatzResearch.WordTrace tailWord_5401261 prefixEnd_5401261 2773443033384297275197559 := by
  unfold tailWord_5401261
  simp only [CollatzResearch.WordTrace]
  refine ⟨197000172885161333782963637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131333448590107555855309091 197000172885161333782963637)
  ·
    refine ⟨18468766207983875042152841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197000172885161333782963637 18468766207983875042152841)
    ·
      refine ⟨13851574655987906281614631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18468766207983875042152841 13851574655987906281614631)
      ·
        refine ⟨20777361983981859422421947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13851574655987906281614631 20777361983981859422421947)
        ·
          refine ⟨31166042975972789133632921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20777361983981859422421947 31166042975972789133632921)
          ·
            refine ⟨23374532231979591850224691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31166042975972789133632921 23374532231979591850224691)
            ·
              refine ⟨35061798347969387775337037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23374532231979591850224691 35061798347969387775337037)
              ·
                refine ⟨13148174380488520415751389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35061798347969387775337037 13148174380488520415751389)
                ·
                  refine ⟨4930565392683195155906771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13148174380488520415751389 4930565392683195155906771)
                  ·
                    refine ⟨7395848089024792733860157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4930565392683195155906771 7395848089024792733860157)
                    ·
                      refine ⟨2773443033384297275197559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7395848089024792733860157 2773443033384297275197559)
                      ·
                        rfl

theorem cell23_5401261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_5401261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401261 prefixEnd_5401261 := by exact prefixLift 5401261
  have htrace : WordTrace (prefixWord ++ tailWord_5401261) baseStart_5401261 baseEnd_5401261 := by
    simpa [prefixWord, tailWord_5401261, baseEnd_5401261] using wordTrace_append hprefix tailTrace_5401261
  have hstable : (prefixWord ++ tailWord_5401261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401261).length < 2 ^ (prefixWord ++ tailWord_5401261).sum := by decide
  have hdescent : baseEnd_5401261 < baseStart_5401261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401294 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 4, 4]
def baseStart_5401294 : Nat := 118140960795 + 5401294 * 2 ^ 59
def prefixEnd_5401294 : Nat := 4983230072969 + 3 ^ 40 * 5401294 * 2
def baseEnd_5401294 : Nat := 924486659415298548694969

theorem tailTrace_5401294 : CollatzResearch.WordTrace tailWord_5401294 prefixEnd_5401294 924486659415298548694969 := by
  unfold tailWord_5401294
  simp only [CollatzResearch.WordTrace]
  refine ⟨24625172061755222552364367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131334250996027853612609957 24625172061755222552364367)
  ·
    refine ⟨36937758092632833828546551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24625172061755222552364367 36937758092632833828546551)
    ·
      refine ⟨55406637138949250742819827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36937758092632833828546551 55406637138949250742819827)
      ·
        refine ⟨83109955708423876114229741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55406637138949250742819827 83109955708423876114229741)
        ·
          refine ⟨31166233390658953542836153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83109955708423876114229741 31166233390658953542836153)
          ·
            refine ⟨23374675042994215157127115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31166233390658953542836153 23374675042994215157127115)
            ·
              refine ⟨35062012564491322735690673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23374675042994215157127115 35062012564491322735690673)
              ·
                refine ⟨26296509423368492051768005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35062012564491322735690673 26296509423368492051768005)
                ·
                  refine ⟨4930595516881592259706501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26296509423368492051768005 4930595516881592259706501)
                  ·
                    refine ⟨924486659415298548694969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4930595516881592259706501 924486659415298548694969)
                    ·
                      rfl

theorem cell23_5401294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_5401294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401294 prefixEnd_5401294 := by exact prefixLift 5401294
  have htrace : WordTrace (prefixWord ++ tailWord_5401294) baseStart_5401294 baseEnd_5401294 := by
    simpa [prefixWord, tailWord_5401294, baseEnd_5401294] using wordTrace_append hprefix tailTrace_5401294
  have hstable : (prefixWord ++ tailWord_5401294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401294).length < 2 ^ (prefixWord ++ tailWord_5401294).sum := by decide
  have hdescent : baseEnd_5401294 < baseStart_5401294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401297 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 3, 2, 4]
def baseStart_5401297 : Nat := 118140960795 + 5401297 * 2 ^ 59
def prefixEnd_5401297 : Nat := 4983230072969 + 3 ^ 40 * 5401297 * 2
def baseEnd_5401297 : Nat := 2773461518687859134347393

theorem tailTrace_5401297 : CollatzResearch.WordTrace tailWord_5401297 prefixEnd_5401297 2773461518687859134347393 := by
  unfold tailWord_5401297
  simp only [CollatzResearch.WordTrace]
  refine ⟨197001485913030911931274145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131334323942020607954182763 197001485913030911931274145)
  ·
    refine ⟨147751114434773183948455609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197001485913030911931274145 147751114434773183948455609)
    ·
      refine ⟨110813335826079887961341707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147751114434773183948455609 110813335826079887961341707)
      ·
        refine ⟨166220003739119831942012561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110813335826079887961341707 166220003739119831942012561)
        ·
          refine ⟨124665002804339873956509421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166220003739119831942012561 124665002804339873956509421)
          ·
            refine ⟨46749376051627452733691033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124665002804339873956509421 46749376051627452733691033)
            ·
              refine ⟨35062032038720589550268275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46749376051627452733691033 35062032038720589550268275)
              ·
                refine ⟨52593048058080884325402413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35062032038720589550268275 52593048058080884325402413)
                ·
                  refine ⟨19722393021780331622025905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52593048058080884325402413 19722393021780331622025905)
                  ·
                    refine ⟨14791794766335248716519429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19722393021780331622025905 14791794766335248716519429)
                    ·
                      refine ⟨2773461518687859134347393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14791794766335248716519429 2773461518687859134347393)
                      ·
                        rfl

theorem cell23_5401297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_5401297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401297 prefixEnd_5401297 := by exact prefixLift 5401297
  have htrace : WordTrace (prefixWord ++ tailWord_5401297) baseStart_5401297 baseEnd_5401297 := by
    simpa [prefixWord, tailWord_5401297, baseEnd_5401297] using wordTrace_append hprefix tailTrace_5401297
  have hstable : (prefixWord ++ tailWord_5401297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401297).length < 2 ^ (prefixWord ++ tailWord_5401297).sum := by decide
  have hdescent : baseEnd_5401297 < baseStart_5401297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401304 : List Nat := [2, 1, 2, 2, 3, 3, 2, 1, 1, 1, 5]
def baseStart_5401304 : Nat := 118140960795 + 5401304 * 2 ^ 59
def prefixEnd_5401304 : Nat := 4983230072969 + 3 ^ 40 * 5401304 * 2
def baseEnd_5401304 : Nat := 2773465113052440606959861

theorem tailTrace_5401304 : CollatzResearch.WordTrace tailWord_5401304 prefixEnd_5401304 2773465113052440606959861 := by
  unfold tailWord_5401304
  simp only [CollatzResearch.WordTrace]
  refine ⟨98500870612002776063389483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131334494149337034751185977 98500870612002776063389483)
  ·
    refine ⟨147751305918004164095084225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98500870612002776063389483 147751305918004164095084225)
    ·
      refine ⟨110813479438503123071313169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147751305918004164095084225 110813479438503123071313169)
      ·
        refine ⟨83110109578877342303484877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110813479438503123071313169 83110109578877342303484877)
        ·
          refine ⟨31166291092079003363806829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83110109578877342303484877 31166291092079003363806829)
          ·
            refine ⟨11687359159529626261427561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31166291092079003363806829 11687359159529626261427561)
            ·
              refine ⟨8765519369647219696070671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11687359159529626261427561 8765519369647219696070671)
              ·
                refine ⟨13148279054470829544106007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8765519369647219696070671 13148279054470829544106007)
                ·
                  refine ⟨19722418581706244316159011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13148279054470829544106007 19722418581706244316159011)
                  ·
                    refine ⟨29583627872559366474238517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19722418581706244316159011 29583627872559366474238517)
                    ·
                      refine ⟨2773465113052440606959861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29583627872559366474238517 2773465113052440606959861)
                      ·
                        rfl

theorem cell23_5401304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_5401304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401304 prefixEnd_5401304 := by exact prefixLift 5401304
  have htrace : WordTrace (prefixWord ++ tailWord_5401304) baseStart_5401304 baseEnd_5401304 := by
    simpa [prefixWord, tailWord_5401304, baseEnd_5401304] using wordTrace_append hprefix tailTrace_5401304
  have hstable : (prefixWord ++ tailWord_5401304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401304).length < 2 ^ (prefixWord ++ tailWord_5401304).sum := by decide
  have hdescent : baseEnd_5401304 < baseStart_5401304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401332 : List Nat := [2, 6, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_5401332 : Nat := 118140960795 + 5401332 * 2 ^ 59
def prefixEnd_5401332 : Nat := 4983230072969 + 3 ^ 40 * 5401332 * 2
def baseEnd_5401332 : Nat := 924493163503588832469911

theorem tailTrace_5401332 : CollatzResearch.WordTrace tailWord_5401332 prefixEnd_5401332 924493163503588832469911 := by
  unfold tailWord_5401332
  simp only [CollatzResearch.WordTrace]
  refine ⟨98501381233952056454399125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131335174978602741939198833 98501381233952056454399125)
  ·
    refine ⟨4617252245341502646299959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 98501381233952056454399125 4617252245341502646299959)
    ·
      refine ⟨6925878368012253969449939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4617252245341502646299959 6925878368012253969449939)
      ·
        refine ⟨10388817552018380954174909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6925878368012253969449939 10388817552018380954174909)
        ·
          refine ⟨3895806582006892857815591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10388817552018380954174909 3895806582006892857815591)
          ·
            refine ⟨5843709873010339286723387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3895806582006892857815591 5843709873010339286723387)
            ·
              refine ⟨8765564809515508930085081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5843709873010339286723387 8765564809515508930085081)
              ·
                refine ⟨6574173607136631697563811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8765564809515508930085081 6574173607136631697563811)
                ·
                  refine ⟨9861260410704947546345717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6574173607136631697563811 9861260410704947546345717)
                  ·
                    refine ⟨924493163503588832469911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9861260410704947546345717 924493163503588832469911)
                    ·
                      rfl

theorem cell23_5401332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_5401332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401332 prefixEnd_5401332 := by exact prefixLift 5401332
  have htrace : WordTrace (prefixWord ++ tailWord_5401332) baseStart_5401332 baseEnd_5401332 := by
    simpa [prefixWord, tailWord_5401332, baseEnd_5401332] using wordTrace_append hprefix tailTrace_5401332
  have hstable : (prefixWord ++ tailWord_5401332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401332).length < 2 ^ (prefixWord ++ tailWord_5401332).sum := by decide
  have hdescent : baseEnd_5401332 < baseStart_5401332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401351 : List Nat := [1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 3]
def baseStart_5401351 : Nat := 118140960795 + 5401351 * 2 ^ 59
def prefixEnd_5401351 : Nat := 4983230072969 + 3 ^ 40 * 5401351 * 2
def baseEnd_5401351 : Nat := 2773489246643201923072145

theorem tailTrace_5401351 : CollatzResearch.WordTrace tailWord_5401351 prefixEnd_5401351 2773489246643201923072145 := by
  unfold tailWord_5401351
  simp only [CollatzResearch.WordTrace]
  refine ⟨197003455454835279153739907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131335636969890186102493271 197003455454835279153739907)
  ·
    refine ⟨295505183182252918730609861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197003455454835279153739907 295505183182252918730609861)
    ·
      refine ⟨55407221846672422261989349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 295505183182252918730609861 55407221846672422261989349)
      ·
        refine ⟨10388854096251079174123003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55407221846672422261989349 10388854096251079174123003)
        ·
          refine ⟨15583281144376618761184505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10388854096251079174123003 15583281144376618761184505)
          ·
            refine ⟨11687460858282464070888379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15583281144376618761184505 11687460858282464070888379)
            ·
              refine ⟨17531191287423696106332569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11687460858282464070888379 17531191287423696106332569)
              ·
                refine ⟨13148393465567772079749427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17531191287423696106332569 13148393465567772079749427)
                ·
                  refine ⟨19722590198351658119624141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13148393465567772079749427 19722590198351658119624141)
                  ·
                    refine ⟨7395971324381871794859053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19722590198351658119624141 7395971324381871794859053)
                    ·
                      refine ⟨2773489246643201923072145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7395971324381871794859053 2773489246643201923072145)
                      ·
                        rfl

theorem cell23_5401351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_5401351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401351 prefixEnd_5401351 := by exact prefixLift 5401351
  have htrace : WordTrace (prefixWord ++ tailWord_5401351) baseStart_5401351 baseEnd_5401351 := by
    simpa [prefixWord, tailWord_5401351, baseEnd_5401351] using wordTrace_append hprefix tailTrace_5401351
  have hstable : (prefixWord ++ tailWord_5401351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401351).length < 2 ^ (prefixWord ++ tailWord_5401351).sum := by decide
  have hdescent : baseEnd_5401351 < baseStart_5401351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401361 : List Nat := [1, 2, 2, 1, 1, 3, 2, 5, 1, 3, 2]
def baseStart_5401361 : Nat := 118140960795 + 5401361 * 2 ^ 59
def prefixEnd_5401361 : Nat := 4983230072969 + 3 ^ 40 * 5401361 * 2
def baseEnd_5401361 : Nat := 2773494381449746883947099

theorem tailTrace_5401361 : CollatzResearch.WordTrace tailWord_5401361 prefixEnd_5401361 2773494381449746883947099 := by
  unfold tailWord_5401361
  simp only [CollatzResearch.WordTrace]
  refine ⟨197003820184799050861603937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131335880123199367241069291 197003820184799050861603937)
  ·
    refine ⟨147752865138599288146202953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197003820184799050861603937 147752865138599288146202953)
    ·
      refine ⟨110814648853949466109652215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147752865138599288146202953 110814648853949466109652215)
      ·
        refine ⟨166221973280924199164478323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110814648853949466109652215 166221973280924199164478323)
        ·
          refine ⟨249332959921386298746717485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166221973280924199164478323 249332959921386298746717485)
          ·
            refine ⟨93499859970519862030019057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249332959921386298746717485 93499859970519862030019057)
            ·
              refine ⟨70124894977889896522514293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93499859970519862030019057 70124894977889896522514293)
              ·
                refine ⟨6574208904177177798985715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70124894977889896522514293 6574208904177177798985715)
                ·
                  refine ⟨9861313356265766698478573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6574208904177177798985715 9861313356265766698478573)
                  ·
                    refine ⟨3697992508599662511929465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9861313356265766698478573 3697992508599662511929465)
                    ·
                      refine ⟨2773494381449746883947099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3697992508599662511929465 2773494381449746883947099)
                      ·
                        rfl

theorem cell23_5401361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 3, 2].length) (baseStart_5401361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401361 prefixEnd_5401361 := by exact prefixLift 5401361
  have htrace : WordTrace (prefixWord ++ tailWord_5401361) baseStart_5401361 baseEnd_5401361 := by
    simpa [prefixWord, tailWord_5401361, baseEnd_5401361] using wordTrace_append hprefix tailTrace_5401361
  have hstable : (prefixWord ++ tailWord_5401361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401361).length < 2 ^ (prefixWord ++ tailWord_5401361).sum := by decide
  have hdescent : baseEnd_5401361 < baseStart_5401361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401384 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 2, 6]
def baseStart_5401384 : Nat := 118140960795 + 5401384 * 2 ^ 59
def prefixEnd_5401384 : Nat := 4983230072969 + 3 ^ 40 * 5401384 * 2
def baseEnd_5401384 : Nat := 924502063834933431319831

theorem tailTrace_5401384 : CollatzResearch.WordTrace tailWord_5401384 prefixEnd_5401384 924502063834933431319831 := by
  unfold tailWord_5401384
  simp only [CollatzResearch.WordTrace]
  refine ⟨98502329531857862894845603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131336439375810483859794137 98502329531857862894845603)
  ·
    refine ⟨147753494297786794342268405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98502329531857862894845603 147753494297786794342268405)
    ·
      refine ⟨13851890090417511969587663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147753494297786794342268405 13851890090417511969587663)
      ·
        refine ⟨20777835135626267954381495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13851890090417511969587663 20777835135626267954381495)
        ·
          refine ⟨31166752703439401931572243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20777835135626267954381495 31166752703439401931572243)
          ·
            refine ⟨46750129055159102897358365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31166752703439401931572243 46750129055159102897358365)
            ·
              refine ⟨17531298395684663586509387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46750129055159102897358365 17531298395684663586509387)
              ·
                refine ⟨26296947593526995379764081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17531298395684663586509387 26296947593526995379764081)
                ·
                  refine ⟨19722710695145246534823061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26296947593526995379764081 19722710695145246534823061)
                  ·
                    refine ⟨924502063834933431319831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19722710695145246534823061 924502063834933431319831)
                    ·
                      rfl

theorem cell23_5401384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_5401384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401384 prefixEnd_5401384 := by exact prefixLift 5401384
  have htrace : WordTrace (prefixWord ++ tailWord_5401384) baseStart_5401384 baseEnd_5401384 := by
    simpa [prefixWord, tailWord_5401384, baseEnd_5401384] using wordTrace_append hprefix tailTrace_5401384
  have hstable : (prefixWord ++ tailWord_5401384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401384).length < 2 ^ (prefixWord ++ tailWord_5401384).sum := by decide
  have hdescent : baseEnd_5401384 < baseStart_5401384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401387 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 4]
def baseStart_5401387 : Nat := 118140960795 + 5401387 * 2 ^ 59
def prefixEnd_5401387 : Nat := 4983230072969 + 3 ^ 40 * 5401387 * 2
def baseEnd_5401387 : Nat := 2773507731946763782221979

theorem tailTrace_5401387 : CollatzResearch.WordTrace tailWord_5401387 prefixEnd_5401387 2773507731946763782221979 := by
  unfold tailWord_5401387
  simp only [CollatzResearch.WordTrace]
  refine ⟨197004768482704857302050415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131336512321803238201366943 197004768482704857302050415)
  ·
    refine ⟨295507152724057285953075623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197004768482704857302050415 295507152724057285953075623)
    ·
      refine ⟨443260729086085928929613435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295507152724057285953075623 443260729086085928929613435)
      ·
        refine ⟨664891093629128893394420153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443260729086085928929613435 664891093629128893394420153)
        ·
          refine ⟨498668320221846670045815115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 664891093629128893394420153 498668320221846670045815115)
          ·
            refine ⟨748002480332770005068722673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498668320221846670045815115 748002480332770005068722673)
            ·
              refine ⟨561001860249577503801542005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 748002480332770005068722673 561001860249577503801542005)
              ·
                refine ⟨52593924398397890981394563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 561001860249577503801542005 52593924398397890981394563)
                ·
                  refine ⟨78890886597596836472091845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52593924398397890981394563 78890886597596836472091845)
                  ·
                    refine ⟨14792041237049406838517221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78890886597596836472091845 14792041237049406838517221)
                    ·
                      refine ⟨2773507731946763782221979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14792041237049406838517221 2773507731946763782221979)
                      ·
                        rfl

theorem cell23_5401387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 4].length) (baseStart_5401387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401387 prefixEnd_5401387 := by exact prefixLift 5401387
  have htrace : WordTrace (prefixWord ++ tailWord_5401387) baseStart_5401387 baseEnd_5401387 := by
    simpa [prefixWord, tailWord_5401387, baseEnd_5401387] using wordTrace_append hprefix tailTrace_5401387
  have hstable : (prefixWord ++ tailWord_5401387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401387).length < 2 ^ (prefixWord ++ tailWord_5401387).sum := by decide
  have hdescent : baseEnd_5401387 < baseStart_5401387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401394 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3]
def baseStart_5401394 : Nat := 118140960795 + 5401394 * 2 ^ 59
def prefixEnd_5401394 : Nat := 4983230072969 + 3 ^ 40 * 5401394 * 2
def baseEnd_5401394 : Nat := 2773511326311345254834447

theorem tailTrace_5401394 : CollatzResearch.WordTrace tailWord_5401394 prefixEnd_5401394 2773511326311345254834447 := by
  unfold tailWord_5401394
  simp only [CollatzResearch.WordTrace]
  refine ⟨49251255948419874374388809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131336682529119664998370157 49251255948419874374388809)
  ·
    refine ⟨36938441961314905780791607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49251255948419874374388809 36938441961314905780791607)
    ·
      refine ⟨55407662941972358671187411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36938441961314905780791607 55407662941972358671187411)
      ·
        refine ⟨83111494412958538006781117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55407662941972358671187411 83111494412958538006781117)
        ·
          refine ⟨31166810404859451752542919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83111494412958538006781117 31166810404859451752542919)
          ·
            refine ⟨46750215607289177628814379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31166810404859451752542919 46750215607289177628814379)
            ·
              refine ⟨70125323410933766443221569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46750215607289177628814379 70125323410933766443221569)
              ·
                refine ⟨52593992558200324832416177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70125323410933766443221569 52593992558200324832416177)
                ·
                  refine ⟨39445494418650243624312133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52593992558200324832416177 39445494418650243624312133)
                  ·
                    refine ⟨7396030203496920679558525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39445494418650243624312133 7396030203496920679558525)
                    ·
                      refine ⟨2773511326311345254834447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7396030203496920679558525 2773511326311345254834447)
                      ·
                        rfl

theorem cell23_5401394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_5401394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401394 prefixEnd_5401394 := by exact prefixLift 5401394
  have htrace : WordTrace (prefixWord ++ tailWord_5401394) baseStart_5401394 baseEnd_5401394 := by
    simpa [prefixWord, tailWord_5401394, baseEnd_5401394] using wordTrace_append hprefix tailTrace_5401394
  have hstable : (prefixWord ++ tailWord_5401394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401394).length < 2 ^ (prefixWord ++ tailWord_5401394).sum := by decide
  have hdescent : baseEnd_5401394 < baseStart_5401394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401412 : List Nat := [2, 3, 4, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_5401412 : Nat := 118140960795 + 5401412 * 2 ^ 59
def prefixEnd_5401412 : Nat := 4983230072969 + 3 ^ 40 * 5401412 * 2
def baseEnd_5401412 : Nat := 2773520568963126184409365

theorem tailTrace_5401412 : CollatzResearch.WordTrace tailWord_5401412 prefixEnd_5401412 2773520568963126184409365 := by
  unfold tailWord_5401412
  simp only [CollatzResearch.WordTrace]
  refine ⟨98502840153807143285855245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131337120205076191047806993 98502840153807143285855245)
  ·
    refine ⟨36938565057677678732195717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98502840153807143285855245 36938565057677678732195717)
    ·
      refine ⟨6925980948314564762286697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36938565057677678732195717 6925980948314564762286697)
      ·
        refine ⟨5194485711235923571715023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6925980948314564762286697 5194485711235923571715023)
        ·
          refine ⟨7791728566853885357572535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5194485711235923571715023 7791728566853885357572535)
          ·
            refine ⟨11687592850280828036358803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7791728566853885357572535 11687592850280828036358803)
            ·
              refine ⟨17531389275421242054538205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11687592850280828036358803 17531389275421242054538205)
              ·
                refine ⟨6574270978282965770451827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17531389275421242054538205 6574270978282965770451827)
                ·
                  refine ⟨9861406467424448655677741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6574270978282965770451827 9861406467424448655677741)
                  ·
                    refine ⟨3698027425284168245879153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9861406467424448655677741 3698027425284168245879153)
                    ·
                      refine ⟨2773520568963126184409365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3698027425284168245879153 2773520568963126184409365)
                      ·
                        rfl

theorem cell23_5401412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_5401412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401412 prefixEnd_5401412 := by exact prefixLift 5401412
  have htrace : WordTrace (prefixWord ++ tailWord_5401412) baseStart_5401412 baseEnd_5401412 := by
    simpa [prefixWord, tailWord_5401412, baseEnd_5401412] using wordTrace_append hprefix tailTrace_5401412
  have hstable : (prefixWord ++ tailWord_5401412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401412).length < 2 ^ (prefixWord ++ tailWord_5401412).sum := by decide
  have hdescent : baseEnd_5401412 < baseStart_5401412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401424 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 3]
def baseStart_5401424 : Nat := 118140960795 + 5401424 * 2 ^ 59
def prefixEnd_5401424 : Nat := 4983230072969 + 3 ^ 40 * 5401424 * 2
def baseEnd_5401424 : Nat := 2773526730730980137459309

theorem tailTrace_5401424 : CollatzResearch.WordTrace tailWord_5401424 prefixEnd_5401424 2773526730730980137459309 := by
  unfold tailWord_5401424
  simp only [CollatzResearch.WordTrace]
  refine ⟨98503058991785406310573663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131337411989047208414098217 98503058991785406310573663)
  ·
    refine ⟨147754588487678109465860495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98503058991785406310573663 147754588487678109465860495)
    ·
      refine ⟨221631882731517164198790743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147754588487678109465860495 221631882731517164198790743)
      ·
        refine ⟨332447824097275746298186115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221631882731517164198790743 332447824097275746298186115)
        ·
          refine ⟨498671736145913619447279173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332447824097275746298186115 498671736145913619447279173)
          ·
            refine ⟨93500950527358803646364845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 498671736145913619447279173 93500950527358803646364845)
            ·
              refine ⟨35062856447759551367386817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93500950527358803646364845 35062856447759551367386817)
              ·
                refine ⟨26297142335819663525540113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35062856447759551367386817 26297142335819663525540113)
                ·
                  refine ⟨19722856751864747644155085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26297142335819663525540113 19722856751864747644155085)
                  ·
                    refine ⟨7396071281949280366558157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19722856751864747644155085 7396071281949280366558157)
                    ·
                      refine ⟨2773526730730980137459309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7396071281949280366558157 2773526730730980137459309)
                      ·
                        rfl

theorem cell23_5401424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 3].length) (baseStart_5401424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401424 prefixEnd_5401424 := by exact prefixLift 5401424
  have htrace : WordTrace (prefixWord ++ tailWord_5401424) baseStart_5401424 baseEnd_5401424 := by
    simpa [prefixWord, tailWord_5401424, baseEnd_5401424] using wordTrace_append hprefix tailTrace_5401424
  have hstable : (prefixWord ++ tailWord_5401424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401424).length < 2 ^ (prefixWord ++ tailWord_5401424).sum := by decide
  have hdescent : baseEnd_5401424 < baseStart_5401424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401431 : List Nat := [1, 1, 3, 2, 4, 1, 2, 4, 5]
def baseStart_5401431 : Nat := 118140960795 + 5401431 * 2 ^ 59
def prefixEnd_5401431 : Nat := 4983230072969 + 3 ^ 40 * 5401431 * 2
def baseEnd_5401431 : Nat := 308170036121729067785753

theorem tailTrace_5401431 : CollatzResearch.WordTrace tailWord_5401431 prefixEnd_5401431 308170036121729067785753 := by
  unfold tailWord_5401431
  simp only [CollatzResearch.WordTrace]
  refine ⟨197006373294545452816652147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131337582196363635211101431 197006373294545452816652147)
  ·
    refine ⟨295509559941818179224978221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197006373294545452816652147 295509559941818179224978221)
    ·
      refine ⟨110816084978181817209366833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295509559941818179224978221 110816084978181817209366833)
      ·
        refine ⟨83112063733636362907025125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110816084978181817209366833 83112063733636362907025125)
        ·
          refine ⟨15583511950056818045067211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83112063733636362907025125 15583511950056818045067211)
          ·
            refine ⟨23375267925085227067600817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15583511950056818045067211 23375267925085227067600817)
            ·
              refine ⟨17531450943813920300700613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23375267925085227067600817 17531450943813920300700613)
              ·
                refine ⟨3287147051965110056381365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17531450943813920300700613 3287147051965110056381365)
                ·
                  refine ⟨308170036121729067785753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3287147051965110056381365 308170036121729067785753)
                  ·
                    rfl

theorem cell23_5401431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 5].length) (baseStart_5401431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401431 prefixEnd_5401431 := by exact prefixLift 5401431
  have htrace : WordTrace (prefixWord ++ tailWord_5401431) baseStart_5401431 baseEnd_5401431 := by
    simpa [prefixWord, tailWord_5401431, baseEnd_5401431] using wordTrace_append hprefix tailTrace_5401431
  have hstable : (prefixWord ++ tailWord_5401431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401431).length < 2 ^ (prefixWord ++ tailWord_5401431).sum := by decide
  have hdescent : baseEnd_5401431 < baseStart_5401431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401442 : List Nat := [3, 3, 2, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_5401442 : Nat := 118140960795 + 5401442 * 2 ^ 59
def prefixEnd_5401442 : Nat := 4983230072969 + 3 ^ 40 * 5401442 * 2
def baseEnd_5401442 : Nat := 2773535973382761067034227

theorem tailTrace_5401442 : CollatzResearch.WordTrace tailWord_5401442 prefixEnd_5401442 2773535973382761067034227 := by
  unfold tailWord_5401442
  simp only [CollatzResearch.WordTrace]
  refine ⟨49251693624376400423825645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131337849665003734463535053 49251693624376400423825645)
  ·
    refine ⟨18469385109141150158934617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49251693624376400423825645 18469385109141150158934617)
    ·
      refine ⟨13852038831855862619200963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18469385109141150158934617 13852038831855862619200963)
      ·
        refine ⟨20778058247783793928801445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13852038831855862619200963 20778058247783793928801445)
        ·
          refine ⟨3895885921459461361650271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20778058247783793928801445 3895885921459461361650271)
          ·
            refine ⟨5843828882189192042475407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3895885921459461361650271 5843828882189192042475407)
            ·
              refine ⟨8765743323283788063713111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5843828882189192042475407 8765743323283788063713111)
              ·
                refine ⟨13148614984925682095569667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8765743323283788063713111 13148614984925682095569667)
                ·
                  refine ⟨19722922477388523143354501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13148614984925682095569667 19722922477388523143354501)
                  ·
                    refine ⟨3698047964510348089378969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19722922477388523143354501 3698047964510348089378969)
                    ·
                      refine ⟨2773535973382761067034227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3698047964510348089378969 2773535973382761067034227)
                      ·
                        rfl

theorem cell23_5401442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_5401442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401442 prefixEnd_5401442 := by exact prefixLift 5401442
  have htrace : WordTrace (prefixWord ++ tailWord_5401442) baseStart_5401442 baseEnd_5401442 := by
    simpa [prefixWord, tailWord_5401442, baseEnd_5401442] using wordTrace_append hprefix tailTrace_5401442
  have hstable : (prefixWord ++ tailWord_5401442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401442).length < 2 ^ (prefixWord ++ tailWord_5401442).sum := by decide
  have hdescent : baseEnd_5401442 < baseStart_5401442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401444 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 1, 7]
def baseStart_5401444 : Nat := 118140960795 + 5401444 * 2 ^ 59
def prefixEnd_5401444 : Nat := 4983230072969 + 3 ^ 40 * 5401444 * 2
def baseEnd_5401444 : Nat := 924512333448023353069739

theorem tailTrace_5401444 : CollatzResearch.WordTrace tailWord_5401444 prefixEnd_5401444 924512333448023353069739 := by
  unfold tailWord_5401444
  simp only [CollatzResearch.WordTrace]
  refine ⟨98503423721749178018437693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131337898295665570691250257 98503423721749178018437693)
  ·
    refine ⟨36938783895655941756914135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98503423721749178018437693 36938783895655941756914135)
    ·
      refine ⟨55408175843483912635371203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36938783895655941756914135 55408175843483912635371203)
      ·
        refine ⟨83112263765225868953056805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55408175843483912635371203 83112263765225868953056805)
        ·
          refine ⟨15583549455979850428698151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83112263765225868953056805 15583549455979850428698151)
          ·
            refine ⟨23375324183969775643047227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15583549455979850428698151 23375324183969775643047227)
            ·
              refine ⟨35062986275954663464570841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23375324183969775643047227 35062986275954663464570841)
              ·
                refine ⟨26297239706965997598428131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35062986275954663464570841 26297239706965997598428131)
                ·
                  refine ⟨39445859560448996397642197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26297239706965997598428131 39445859560448996397642197)
                  ·
                    refine ⟨924512333448023353069739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39445859560448996397642197 924512333448023353069739)
                    ·
                      rfl

theorem cell23_5401444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_5401444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401444 prefixEnd_5401444 := by exact prefixLift 5401444
  have htrace : WordTrace (prefixWord ++ tailWord_5401444) baseStart_5401444 baseEnd_5401444 := by
    simpa [prefixWord, tailWord_5401444, baseEnd_5401444] using wordTrace_append hprefix tailTrace_5401444
  have hstable : (prefixWord ++ tailWord_5401444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401444).length < 2 ^ (prefixWord ++ tailWord_5401444).sum := by decide
  have hdescent : baseEnd_5401444 < baseStart_5401444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401481 : List Nat := [1, 2, 1, 1, 5, 3, 1, 2, 2, 1, 4]
def baseStart_5401481 : Nat := 118140960795 + 5401481 * 2 ^ 59
def prefixEnd_5401481 : Nat := 4983230072969 + 3 ^ 40 * 5401481 * 2
def baseEnd_5401481 : Nat := 2773555999128286414446547

theorem tailTrace_5401481 : CollatzResearch.WordTrace tailWord_5401481 prefixEnd_5401481 2773555999128286414446547 := by
  unfold tailWord_5401481
  simp only [CollatzResearch.WordTrace]
  refine ⟨197008196944364311355972297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131338797962909540903981531 197008196944364311355972297)
  ·
    refine ⟨147756147708273233516979223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197008196944364311355972297 147756147708273233516979223)
    ·
      refine ⟨221634221562409850275468835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147756147708273233516979223 221634221562409850275468835)
      ·
        refine ⟨332451332343614775413203253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221634221562409850275468835 332451332343614775413203253)
        ·
          refine ⟨31167312407213885194987805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 332451332343614775413203253 31167312407213885194987805)
          ·
            refine ⟨11687742152705206948120427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31167312407213885194987805 11687742152705206948120427)
            ·
              refine ⟨17531613229057810422180641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11687742152705206948120427 17531613229057810422180641)
              ·
                refine ⟨13148709921793357816635481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17531613229057810422180641 13148709921793357816635481)
                ·
                  refine ⟨9861532441345018362476611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13148709921793357816635481 9861532441345018362476611)
                  ·
                    refine ⟨14792298662017527543714917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9861532441345018362476611 14792298662017527543714917)
                    ·
                      refine ⟨2773555999128286414446547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14792298662017527543714917 2773555999128286414446547)
                      ·
                        rfl

theorem cell23_5401481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 1, 4].length) (baseStart_5401481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401481 prefixEnd_5401481 := by exact prefixLift 5401481
  have htrace : WordTrace (prefixWord ++ tailWord_5401481) baseStart_5401481 baseEnd_5401481 := by
    simpa [prefixWord, tailWord_5401481, baseEnd_5401481] using wordTrace_append hprefix tailTrace_5401481
  have hstable : (prefixWord ++ tailWord_5401481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401481).length < 2 ^ (prefixWord ++ tailWord_5401481).sum := by decide
  have hdescent : baseEnd_5401481 < baseStart_5401481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401501 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_5401501 : Nat := 118140960795 + 5401501 * 2 ^ 59
def prefixEnd_5401501 : Nat := 4983230072969 + 3 ^ 40 * 5401501 * 2
def baseEnd_5401501 : Nat := 2773566268741376336196455

theorem tailTrace_5401501 : CollatzResearch.WordTrace tailWord_5401501 prefixEnd_5401501 2773566268741376336196455 := by
  unfold tailWord_5401501
  simp only [CollatzResearch.WordTrace]
  refine ⟨197008926404291854771700357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131339284269527903181133571 197008926404291854771700357)
  ·
    refine ⟨36939173700804722769693817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197008926404291854771700357 36939173700804722769693817)
    ·
      refine ⟨27704380275603542077270363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36939173700804722769693817 27704380275603542077270363)
      ·
        refine ⟨41556570413405313115905545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27704380275603542077270363 41556570413405313115905545)
        ·
          refine ⟨31167427810053984836929159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41556570413405313115905545 31167427810053984836929159)
          ·
            refine ⟨46751141715080977255393739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31167427810053984836929159 46751141715080977255393739)
            ·
              refine ⟨70126712572621465883090609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46751141715080977255393739 70126712572621465883090609)
              ·
                refine ⟨52595034429466099412317957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70126712572621465883090609 52595034429466099412317957)
                ·
                  refine ⟨9861568955524893639809617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52595034429466099412317957 9861568955524893639809617)
                  ·
                    refine ⟨7396176716643670229857213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9861568955524893639809617 7396176716643670229857213)
                    ·
                      refine ⟨2773566268741376336196455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7396176716643670229857213 2773566268741376336196455)
                      ·
                        rfl

theorem cell23_5401501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_5401501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401501 prefixEnd_5401501 := by exact prefixLift 5401501
  have htrace : WordTrace (prefixWord ++ tailWord_5401501) baseStart_5401501 baseEnd_5401501 := by
    simpa [prefixWord, tailWord_5401501, baseEnd_5401501] using wordTrace_append hprefix tailTrace_5401501
  have hstable : (prefixWord ++ tailWord_5401501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401501).length < 2 ^ (prefixWord ++ tailWord_5401501).sum := by decide
  have hdescent : baseEnd_5401501 < baseStart_5401501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401548 : List Nat := [2, 2, 1, 4, 1, 1, 2, 3, 3, 1, 3]
def baseStart_5401548 : Nat := 118140960795 + 5401548 * 2 ^ 59
def prefixEnd_5401548 : Nat := 4983230072969 + 3 ^ 40 * 5401548 * 2
def baseEnd_5401548 : Nat := 2773590402332137652308739

theorem tailTrace_5401548 : CollatzResearch.WordTrace tailWord_5401548 prefixEnd_5401548 2773590402332137652308739 := by
  unfold tailWord_5401548
  simp only [CollatzResearch.WordTrace]
  refine ⟨98505320317560790899330649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131340427090081054532440865 98505320317560790899330649)
  ·
    refine ⟨73878990238170593174497987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98505320317560790899330649 73878990238170593174497987)
    ·
      refine ⟨110818485357255889761746981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73878990238170593174497987 110818485357255889761746981)
      ·
        refine ⟨20778466004485479330327559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110818485357255889761746981 20778466004485479330327559)
        ·
          refine ⟨31167699006728218995491339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20778466004485479330327559 31167699006728218995491339)
          ·
            refine ⟨46751548510092328493237009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31167699006728218995491339 46751548510092328493237009)
            ·
              refine ⟨35063661382569246369927757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46751548510092328493237009 35063661382569246369927757)
              ·
                refine ⟨13148873018463467388722909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35063661382569246369927757 13148873018463467388722909)
                ·
                  refine ⟨4930827381923800270771091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13148873018463467388722909 4930827381923800270771091)
                  ·
                    refine ⟨7396241072885700406156637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4930827381923800270771091 7396241072885700406156637)
                    ·
                      refine ⟨2773590402332137652308739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7396241072885700406156637 2773590402332137652308739)
                      ·
                        rfl

theorem cell23_5401548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_5401548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401548 prefixEnd_5401548 := by exact prefixLift 5401548
  have htrace : WordTrace (prefixWord ++ tailWord_5401548) baseStart_5401548 baseEnd_5401548 := by
    simpa [prefixWord, tailWord_5401548, baseEnd_5401548] using wordTrace_append hprefix tailTrace_5401548
  have hstable : (prefixWord ++ tailWord_5401548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401548).length < 2 ^ (prefixWord ++ tailWord_5401548).sum := by decide
  have hdescent : baseEnd_5401548 < baseStart_5401548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401549 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_5401549 : Nat := 118140960795 + 5401549 * 2 ^ 59
def prefixEnd_5401549 : Nat := 4983230072969 + 3 ^ 40 * 5401549 * 2
def baseEnd_5401549 : Nat := 2773590915812792148396235

theorem tailTrace_5401549 : CollatzResearch.WordTrace tailWord_5401549 prefixEnd_5401549 2773590915812792148396235 := by
  unfold tailWord_5401549
  simp only [CollatzResearch.WordTrace]
  refine ⟨197010677108117958969447701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131340451405411972646298467 197010677108117958969447701)
  ·
    refine ⟨9234875489443029326692861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 197010677108117958969447701 9234875489443029326692861)
    ·
      refine ⟨3463078308541135997509823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9234875489443029326692861 3463078308541135997509823)
      ·
        refine ⟨5194617462811703996264735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3463078308541135997509823 5194617462811703996264735)
        ·
          refine ⟨7791926194217555994397103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5194617462811703996264735 7791926194217555994397103)
          ·
            refine ⟨11687889291326333991595655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7791926194217555994397103 11687889291326333991595655)
            ·
              refine ⟨17531833936989500987393483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11687889291326333991595655 17531833936989500987393483)
              ·
                refine ⟨26297750905484251481090225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17531833936989500987393483 26297750905484251481090225)
                ·
                  refine ⟨19723313179113188610817669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26297750905484251481090225 19723313179113188610817669)
                  ·
                    refine ⟨3698121221083722864528313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19723313179113188610817669 3698121221083722864528313)
                    ·
                      refine ⟨2773590915812792148396235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3698121221083722864528313 2773590915812792148396235)
                      ·
                        rfl

theorem cell23_5401549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_5401549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401549 prefixEnd_5401549 := by exact prefixLift 5401549
  have htrace : WordTrace (prefixWord ++ tailWord_5401549) baseStart_5401549 baseEnd_5401549 := by
    simpa [prefixWord, tailWord_5401549, baseEnd_5401549] using wordTrace_append hprefix tailTrace_5401549
  have hstable : (prefixWord ++ tailWord_5401549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401549).length < 2 ^ (prefixWord ++ tailWord_5401549).sum := by decide
  have hdescent : baseEnd_5401549 < baseStart_5401549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401565 : List Nat := [1, 4, 3, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_5401565 : Nat := 118140960795 + 5401565 * 2 ^ 59
def prefixEnd_5401565 : Nat := 4983230072969 + 3 ^ 40 * 5401565 * 2
def baseEnd_5401565 : Nat := 2773599131503264085796161

theorem tailTrace_5401565 : CollatzResearch.WordTrace tailWord_5401565 prefixEnd_5401565 2773599131503264085796161 := by
  unfold tailWord_5401565
  simp only [CollatzResearch.WordTrace]
  refine ⟨197011260676059993702030149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131340840450706662468020099 197011260676059993702030149)
  ·
    refine ⟨36939611376761248819130653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197011260676059993702030149 36939611376761248819130653)
    ·
      refine ⟨13852354266285468307173995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36939611376761248819130653 13852354266285468307173995)
      ·
        refine ⟨20778531399428202460760993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13852354266285468307173995 20778531399428202460760993)
        ·
          refine ⟨15583898549571151845570745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20778531399428202460760993 15583898549571151845570745)
          ·
            refine ⟨11687923912178363884178059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15583898549571151845570745 11687923912178363884178059)
            ·
              refine ⟨17531885868267545826267089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11687923912178363884178059 17531885868267545826267089)
              ·
                refine ⟨13148914401200659369700317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17531885868267545826267089 13148914401200659369700317)
                ·
                  refine ⟨4930842900450247263637619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13148914401200659369700317 4930842900450247263637619)
                  ·
                    refine ⟨7396264350675370895456429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4930842900450247263637619 7396264350675370895456429)
                    ·
                      refine ⟨2773599131503264085796161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7396264350675370895456429 2773599131503264085796161)
                      ·
                        rfl

theorem cell23_5401565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_5401565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401565 prefixEnd_5401565 := by exact prefixLift 5401565
  have htrace : WordTrace (prefixWord ++ tailWord_5401565) baseStart_5401565 baseEnd_5401565 := by
    simpa [prefixWord, tailWord_5401565, baseEnd_5401565] using wordTrace_append hprefix tailTrace_5401565
  have hstable : (prefixWord ++ tailWord_5401565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401565).length < 2 ^ (prefixWord ++ tailWord_5401565).sum := by decide
  have hdescent : baseEnd_5401565 < baseStart_5401565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401571 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 4]
def baseStart_5401571 : Nat := 118140960795 + 5401571 * 2 ^ 59
def prefixEnd_5401571 : Nat := 4983230072969 + 3 ^ 40 * 5401571 * 2
def baseEnd_5401571 : Nat := 2773602212387191062321133

theorem tailTrace_5401571 : CollatzResearch.WordTrace tailWord_5401571 prefixEnd_5401571 2773602212387191062321133 := by
  unfold tailWord_5401571
  simp only [CollatzResearch.WordTrace]
  refine ⟨197011479514038256726748567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131340986342692171151165711 197011479514038256726748567)
  ·
    refine ⟨295517219271057385090122851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197011479514038256726748567 295517219271057385090122851)
    ·
      refine ⟨443275828906586077635184277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295517219271057385090122851 443275828906586077635184277)
      ·
        refine ⟨20778554479996222389149263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 443275828906586077635184277 20778554479996222389149263)
        ·
          refine ⟨31167831719994333583723895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20778554479996222389149263 31167831719994333583723895)
          ·
            refine ⟨46751747579991500375585843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31167831719994333583723895 46751747579991500375585843)
            ·
              refine ⟨70127621369987250563378765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46751747579991500375585843 70127621369987250563378765)
              ·
                refine ⟨26297858013745218961267037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70127621369987250563378765 26297858013745218961267037)
                ·
                  refine ⟨9861696755154457110475139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26297858013745218961267037 9861696755154457110475139)
                  ·
                    refine ⟨14792545132731685665712709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9861696755154457110475139 14792545132731685665712709)
                    ·
                      refine ⟨2773602212387191062321133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14792545132731685665712709 2773602212387191062321133)
                      ·
                        rfl

theorem cell23_5401571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_5401571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401571 prefixEnd_5401571 := by exact prefixLift 5401571
  have htrace : WordTrace (prefixWord ++ tailWord_5401571) baseStart_5401571 baseEnd_5401571 := by
    simpa [prefixWord, tailWord_5401571, baseEnd_5401571] using wordTrace_append hprefix tailTrace_5401571
  have hstable : (prefixWord ++ tailWord_5401571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401571).length < 2 ^ (prefixWord ++ tailWord_5401571).sum := by decide
  have hdescent : baseEnd_5401571 < baseStart_5401571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401575 : List Nat := [1, 1, 5, 2, 2, 1, 3, 1, 2, 3, 2]
def baseStart_5401575 : Nat := 118140960795 + 5401575 * 2 ^ 59
def prefixEnd_5401575 : Nat := 4983230072969 + 3 ^ 40 * 5401575 * 2
def baseEnd_5401575 : Nat := 2773604266309809046671115

theorem tailTrace_5401575 : CollatzResearch.WordTrace tailWord_5401575 prefixEnd_5401575 2773604266309809046671115 := by
  unfold tailWord_5401575
  simp only [CollatzResearch.WordTrace]
  refine ⟨197011625406023765409894179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131341083604015843606596119 197011625406023765409894179)
  ·
    refine ⟨295517438109035648114841269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197011625406023765409894179 295517438109035648114841269)
    ·
      refine ⟨27704759822722092010766369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 295517438109035648114841269 27704759822722092010766369)
      ·
        refine ⟨20778569867041569008074777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27704759822722092010766369 20778569867041569008074777)
        ·
          refine ⟨15583927400281176756056083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20778569867041569008074777 15583927400281176756056083)
          ·
            refine ⟨23375891100421765134084125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15583927400281176756056083 23375891100421765134084125)
            ·
              refine ⟨8765959162658161925281547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23375891100421765134084125 8765959162658161925281547)
              ·
                refine ⟨13148938743987242887922321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8765959162658161925281547 13148938743987242887922321)
                ·
                  refine ⟨9861704057990432165941741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13148938743987242887922321 9861704057990432165941741)
                  ·
                    refine ⟨3698139021746412062228153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9861704057990432165941741 3698139021746412062228153)
                    ·
                      refine ⟨2773604266309809046671115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3698139021746412062228153 2773604266309809046671115)
                      ·
                        rfl

theorem cell23_5401575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_5401575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401575 prefixEnd_5401575 := by exact prefixLift 5401575
  have htrace : WordTrace (prefixWord ++ tailWord_5401575) baseStart_5401575 baseEnd_5401575 := by
    simpa [prefixWord, tailWord_5401575, baseEnd_5401575] using wordTrace_append hprefix tailTrace_5401575
  have hstable : (prefixWord ++ tailWord_5401575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401575).length < 2 ^ (prefixWord ++ tailWord_5401575).sum := by decide
  have hdescent : baseEnd_5401575 < baseStart_5401575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401584 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 6]
def baseStart_5401584 : Nat := 118140960795 + 5401584 * 2 ^ 59
def prefixEnd_5401584 : Nat := 4983230072969 + 3 ^ 40 * 5401584 * 2
def baseEnd_5401584 : Nat := 2773608887635699511458573

theorem tailTrace_5401584 : CollatzResearch.WordTrace tailWord_5401584 prefixEnd_5401584 2773608887635699511458573 := by
  unfold tailWord_5401584
  simp only [CollatzResearch.WordTrace]
  refine ⟨98505976831495579973485903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131341302441994106631314537 98505976831495579973485903)
  ·
    refine ⟨147758965247243369960228855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98505976831495579973485903 147758965247243369960228855)
    ·
      refine ⟨221638447870865054940343283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147758965247243369960228855 221638447870865054940343283)
      ·
        refine ⟨332457671806297582410514925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221638447870865054940343283 332457671806297582410514925)
        ·
          refine ⟨124671626927361593403943097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332457671806297582410514925 124671626927361593403943097)
          ·
            refine ⟨93503720195521195052957323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124671626927361593403943097 93503720195521195052957323)
            ·
              refine ⟨140255580293281792579435985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93503720195521195052957323 140255580293281792579435985)
              ·
                refine ⟨105191685219961344434576989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140255580293281792579435985 105191685219961344434576989)
                ·
                  refine ⟨39446881957485504162966371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105191685219961344434576989 39446881957485504162966371)
                  ·
                    refine ⟨59170322936228256244449557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39446881957485504162966371 59170322936228256244449557)
                    ·
                      refine ⟨2773608887635699511458573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59170322936228256244449557 2773608887635699511458573)
                      ·
                        rfl

theorem cell23_5401584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_5401584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401584 prefixEnd_5401584 := by exact prefixLift 5401584
  have htrace : WordTrace (prefixWord ++ tailWord_5401584) baseStart_5401584 baseEnd_5401584 := by
    simpa [prefixWord, tailWord_5401584, baseEnd_5401584] using wordTrace_append hprefix tailTrace_5401584
  have hstable : (prefixWord ++ tailWord_5401584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401584).length < 2 ^ (prefixWord ++ tailWord_5401584).sum := by decide
  have hdescent : baseEnd_5401584 < baseStart_5401584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401585 : List Nat := [1, 2, 2, 2, 4, 3, 2, 1, 1, 5]
def baseStart_5401585 : Nat := 118140960795 + 5401585 * 2 ^ 59
def prefixEnd_5401585 : Nat := 4983230072969 + 3 ^ 40 * 5401585 * 2
def baseEnd_5401585 : Nat := 924536467038784669182023

theorem tailTrace_5401585 : CollatzResearch.WordTrace tailWord_5401585 prefixEnd_5401585 924536467038784669182023 := by
  unfold tailWord_5401585
  simp only [CollatzResearch.WordTrace]
  refine ⟨197011990135987537117758209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131341326757325024745172139 197011990135987537117758209)
  ·
    refine ⟨147758992601990652838318657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197011990135987537117758209 147758992601990652838318657)
    ·
      refine ⟨110819244451492989628738993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147758992601990652838318657 110819244451492989628738993)
      ·
        refine ⟨83114433338619742221554245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110819244451492989628738993 83114433338619742221554245)
        ·
          refine ⟨15583956250991201666541421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83114433338619742221554245 15583956250991201666541421)
          ·
            refine ⟨5843983594121700624953033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15583956250991201666541421 5843983594121700624953033)
            ·
              refine ⟨4382987695591275468714775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5843983594121700624953033 4382987695591275468714775)
              ·
                refine ⟨6574481543386913203072163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4382987695591275468714775 6574481543386913203072163)
                ·
                  refine ⟨9861722315080369804608245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6574481543386913203072163 9861722315080369804608245)
                  ·
                    refine ⟨924536467038784669182023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9861722315080369804608245 924536467038784669182023)
                    ·
                      rfl

theorem cell23_5401585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 1, 5].length) (baseStart_5401585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401585 prefixEnd_5401585 := by exact prefixLift 5401585
  have htrace : WordTrace (prefixWord ++ tailWord_5401585) baseStart_5401585 baseEnd_5401585 := by
    simpa [prefixWord, tailWord_5401585, baseEnd_5401585] using wordTrace_append hprefix tailTrace_5401585
  have hstable : (prefixWord ++ tailWord_5401585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401585).length < 2 ^ (prefixWord ++ tailWord_5401585).sum := by decide
  have hdescent : baseEnd_5401585 < baseStart_5401585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401605 : List Nat := [1, 3, 1, 1, 2, 3, 4, 1, 3, 2, 2]
def baseStart_5401605 : Nat := 118140960795 + 5401605 * 2 ^ 59
def prefixEnd_5401605 : Nat := 4983230072969 + 3 ^ 40 * 5401605 * 2
def baseEnd_5401605 : Nat := 2773619670729443929295977

theorem tailTrace_5401605 : CollatzResearch.WordTrace tailWord_5401605 prefixEnd_5401605 2773619670729443929295977 := by
  unfold tailWord_5401605
  simp only [CollatzResearch.WordTrace]
  refine ⟨197012719595915080533486269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131341813063943387022324179 197012719595915080533486269)
  ·
    refine ⟨73879769848468155200057351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197012719595915080533486269 73879769848468155200057351)
    ·
      refine ⟨110819654772702232800086027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73879769848468155200057351 110819654772702232800086027)
      ·
        refine ⟨166229482159053349200129041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110819654772702232800086027 166229482159053349200129041)
        ·
          refine ⟨124672111619290011900096781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166229482159053349200129041 124672111619290011900096781)
          ·
            refine ⟨46752041857233754462536293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124672111619290011900096781 46752041857233754462536293)
            ·
              refine ⟨8766007848231328961725555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46752041857233754462536293 8766007848231328961725555)
              ·
                refine ⟨13149011772346993442588333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8766007848231328961725555 13149011772346993442588333)
                ·
                  refine ⟨4930879414630122540970625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13149011772346993442588333 4930879414630122540970625)
                  ·
                    refine ⟨3698159560972591905727969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4930879414630122540970625 3698159560972591905727969)
                    ·
                      refine ⟨2773619670729443929295977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3698159560972591905727969 2773619670729443929295977)
                      ·
                        rfl

theorem cell23_5401605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 2, 2].length) (baseStart_5401605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401605 prefixEnd_5401605 := by exact prefixLift 5401605
  have htrace : WordTrace (prefixWord ++ tailWord_5401605) baseStart_5401605 baseEnd_5401605 := by
    simpa [prefixWord, tailWord_5401605, baseEnd_5401605] using wordTrace_append hprefix tailTrace_5401605
  have hstable : (prefixWord ++ tailWord_5401605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401605).length < 2 ^ (prefixWord ++ tailWord_5401605).sum := by decide
  have hdescent : baseEnd_5401605 < baseStart_5401605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401681 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 2, 1, 5]
def baseStart_5401681 : Nat := 118140960795 + 5401681 * 2 ^ 59
def prefixEnd_5401681 : Nat := 4983230072969 + 3 ^ 40 * 5401681 * 2
def baseEnd_5401681 : Nat := 2773658695259185631945627

theorem tailTrace_5401681 : CollatzResearch.WordTrace tailWord_5401681 prefixEnd_5401681 2773658695259185631945627 := by
  unfold tailWord_5401681
  simp only [CollatzResearch.WordTrace]
  refine ⟨197015491543639745513252897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131343661029093163675501931 197015491543639745513252897)
  ·
    refine ⟨147761618657729809134939673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197015491543639745513252897 147761618657729809134939673)
    ·
      refine ⟨110821213993297356851204755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147761618657729809134939673 110821213993297356851204755)
      ·
        refine ⟨166231820989946035276807133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110821213993297356851204755 166231820989946035276807133)
        ·
          refine ⟨62336932871229763228802675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166231820989946035276807133 62336932871229763228802675)
          ·
            refine ⟨93505399306844644843204013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62336932871229763228802675 93505399306844644843204013)
            ·
              refine ⟨35064524740066741816201505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93505399306844644843204013 35064524740066741816201505)
              ·
                refine ⟨26298393555050056362151129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35064524740066741816201505 26298393555050056362151129)
                ·
                  refine ⟨19723795166287542271613347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26298393555050056362151129 19723795166287542271613347)
                  ·
                    refine ⟨29585692749431313407420021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19723795166287542271613347 29585692749431313407420021)
                    ·
                      refine ⟨2773658695259185631945627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29585692749431313407420021 2773658695259185631945627)
                      ·
                        rfl

theorem cell23_5401681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_5401681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401681 prefixEnd_5401681 := by exact prefixLift 5401681
  have htrace : WordTrace (prefixWord ++ tailWord_5401681) baseStart_5401681 baseEnd_5401681 := by
    simpa [prefixWord, tailWord_5401681, baseEnd_5401681] using wordTrace_append hprefix tailTrace_5401681
  have hstable : (prefixWord ++ tailWord_5401681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401681).length < 2 ^ (prefixWord ++ tailWord_5401681).sum := by decide
  have hdescent : baseEnd_5401681 < baseStart_5401681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401682 : List Nat := [3, 2, 2, 1, 3, 1, 3, 2, 1, 3, 2]
def baseStart_5401682 : Nat := 118140960795 + 5401682 * 2 ^ 59
def prefixEnd_5401682 : Nat := 4983230072969 + 3 ^ 40 * 5401682 * 2
def baseEnd_5401682 : Nat := 2773659208739840128033123

theorem tailTrace_5401682 : CollatzResearch.WordTrace tailWord_5401682 prefixEnd_5401682 2773659208739840128033123 := by
  unfold tailWord_5401682
  simp only [CollatzResearch.WordTrace]
  refine ⟨49253882004159030671009825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131343685344424081789359533 49253882004159030671009825)
  ·
    refine ⟨36940411503119273003257369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49253882004159030671009825 36940411503119273003257369)
    ·
      refine ⟨27705308627339454752443027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36940411503119273003257369 27705308627339454752443027)
      ·
        refine ⟨41557962941009182128664541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27705308627339454752443027 41557962941009182128664541)
        ·
          refine ⟨15584236102878443298249203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41557962941009182128664541 15584236102878443298249203)
          ·
            refine ⟨23376354154317664947373805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15584236102878443298249203 23376354154317664947373805)
            ·
              refine ⟨8766132807869124355265177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23376354154317664947373805 8766132807869124355265177)
              ·
                refine ⟨6574599605901843266448883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8766132807869124355265177 6574599605901843266448883)
                ·
                  refine ⟨9861899408852764899673325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6574599605901843266448883 9861899408852764899673325)
                  ·
                    refine ⟨3698212278319786837377497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9861899408852764899673325 3698212278319786837377497)
                    ·
                      refine ⟨2773659208739840128033123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3698212278319786837377497 2773659208739840128033123)
                      ·
                        rfl

theorem cell23_5401682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_5401682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401682 prefixEnd_5401682 := by exact prefixLift 5401682
  have htrace : WordTrace (prefixWord ++ tailWord_5401682) baseStart_5401682 baseEnd_5401682 := by
    simpa [prefixWord, tailWord_5401682, baseEnd_5401682] using wordTrace_append hprefix tailTrace_5401682
  have hstable : (prefixWord ++ tailWord_5401682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401682).length < 2 ^ (prefixWord ++ tailWord_5401682).sum := by decide
  have hdescent : baseEnd_5401682 < baseStart_5401682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401712 : List Nat := [2, 1, 1, 1, 5, 1, 4, 2, 2, 2, 2]
def baseStart_5401712 : Nat := 118140960795 + 5401712 * 2 ^ 59
def prefixEnd_5401712 : Nat := 4983230072969 + 3 ^ 40 * 5401712 * 2
def baseEnd_5401712 : Nat := 2773674613159475010657985

theorem tailTrace_5401712 : CollatzResearch.WordTrace tailWord_5401712 prefixEnd_5401712 2773674613159475010657985 := by
  unfold tailWord_5401712
  simp only [CollatzResearch.WordTrace]
  refine ⟨98508311103263718903815695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131344414804351625205087593 98508311103263718903815695)
  ·
    refine ⟨147762466654895578355723543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98508311103263718903815695 147762466654895578355723543)
    ·
      refine ⟨221643699982343367533585315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147762466654895578355723543 221643699982343367533585315)
      ·
        refine ⟨332465549973515051300377973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221643699982343367533585315 332465549973515051300377973)
        ·
          refine ⟨31168645310017036059410435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 332465549973515051300377973 31168645310017036059410435)
          ·
            refine ⟨46752967965025554089115653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31168645310017036059410435 46752967965025554089115653)
            ·
              refine ⟨8766181493442291391709185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46752967965025554089115653 8766181493442291391709185)
              ·
                refine ⟨6574636120081718543781889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8766181493442291391709185 6574636120081718543781889)
                ·
                  refine ⟨4930977090061288907836417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6574636120081718543781889 4930977090061288907836417)
                  ·
                    refine ⟨3698232817545966680877313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4930977090061288907836417 3698232817545966680877313)
                    ·
                      refine ⟨2773674613159475010657985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3698232817545966680877313 2773674613159475010657985)
                      ·
                        rfl

theorem cell23_5401712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 2, 2, 2].length) (baseStart_5401712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401712 prefixEnd_5401712 := by exact prefixLift 5401712
  have htrace : WordTrace (prefixWord ++ tailWord_5401712) baseStart_5401712 baseEnd_5401712 := by
    simpa [prefixWord, tailWord_5401712, baseEnd_5401712] using wordTrace_append hprefix tailTrace_5401712
  have hstable : (prefixWord ++ tailWord_5401712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401712).length < 2 ^ (prefixWord ++ tailWord_5401712).sum := by decide
  have hdescent : baseEnd_5401712 < baseStart_5401712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401718 : List Nat := [5, 1, 1, 2, 1, 1, 2, 3, 7]
def baseStart_5401718 : Nat := 118140960795 + 5401718 * 2 ^ 59
def prefixEnd_5401718 : Nat := 4983230072969 + 3 ^ 40 * 5401718 * 2
def baseEnd_5401718 : Nat := 308186410449266887464773

theorem tailTrace_5401718 : CollatzResearch.WordTrace tailWord_5401718 prefixEnd_5401718 308186410449266887464773 := by
  unfold tailWord_5401718
  simp only [CollatzResearch.WordTrace]
  refine ⟨12313552565281606302021863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131344560696337133888233205 12313552565281606302021863)
  ·
    refine ⟨18470328847922409453032795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12313552565281606302021863 18470328847922409453032795)
    ·
      refine ⟨27705493271883614179549193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18470328847922409453032795 27705493271883614179549193)
      ·
        refine ⟨20779119953912710634661895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27705493271883614179549193 20779119953912710634661895)
        ·
          refine ⟨31168679930869065951992843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20779119953912710634661895 31168679930869065951992843)
          ·
            refine ⟨46753019896303598927989265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31168679930869065951992843 46753019896303598927989265)
            ·
              refine ⟨35064764922227699195991949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46753019896303598927989265 35064764922227699195991949)
              ·
                refine ⟨13149286845835387198496981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35064764922227699195991949 13149286845835387198496981)
                ·
                  refine ⟨308186410449266887464773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13149286845835387198496981 308186410449266887464773)
                  ·
                    rfl

theorem cell23_5401718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_5401718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401718 prefixEnd_5401718 := by exact prefixLift 5401718
  have htrace : WordTrace (prefixWord ++ tailWord_5401718) baseStart_5401718 baseEnd_5401718 := by
    simpa [prefixWord, tailWord_5401718, baseEnd_5401718] using wordTrace_append hprefix tailTrace_5401718
  have hstable : (prefixWord ++ tailWord_5401718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401718).length < 2 ^ (prefixWord ++ tailWord_5401718).sum := by decide
  have hdescent : baseEnd_5401718 < baseStart_5401718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401731 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 1, 7]
def baseStart_5401731 : Nat := 118140960795 + 5401731 * 2 ^ 59
def prefixEnd_5401731 : Nat := 4983230072969 + 3 ^ 40 * 5401731 * 2
def baseEnd_5401731 : Nat := 924561456430636812106799

theorem tailTrace_5401731 : CollatzResearch.WordTrace tailWord_5401731 prefixEnd_5401731 924561456430636812106799 := by
  unfold tailWord_5401731
  simp only [CollatzResearch.WordTrace]
  refine ⟨197017315193458604052573047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131344876795639069368382031 197017315193458604052573047)
  ·
    refine ⟨295525972790187906078859571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197017315193458604052573047 295525972790187906078859571)
    ·
      refine ⟨443288959185281859118289357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295525972790187906078859571 443288959185281859118289357)
      ·
        refine ⟨166233359694480697169358509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 443288959185281859118289357 166233359694480697169358509)
        ·
          refine ⟨62337509885430261438509441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166233359694480697169358509 62337509885430261438509441)
          ·
            refine ⟨46753132414072696078882081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62337509885430261438509441 46753132414072696078882081)
            ·
              refine ⟨35064849310554522059161561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46753132414072696078882081 35064849310554522059161561)
              ·
                refine ⟨26298636982915891544371171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35064849310554522059161561 26298636982915891544371171)
                ·
                  refine ⟨39447955474373837316556757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26298636982915891544371171 39447955474373837316556757)
                  ·
                    refine ⟨924561456430636812106799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39447955474373837316556757 924561456430636812106799)
                    ·
                      rfl

theorem cell23_5401731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 7].length) (baseStart_5401731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401731 prefixEnd_5401731 := by exact prefixLift 5401731
  have htrace : WordTrace (prefixWord ++ tailWord_5401731) baseStart_5401731 baseEnd_5401731 := by
    simpa [prefixWord, tailWord_5401731, baseEnd_5401731] using wordTrace_append hprefix tailTrace_5401731
  have hstable : (prefixWord ++ tailWord_5401731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401731).length < 2 ^ (prefixWord ++ tailWord_5401731).sum := by decide
  have hdescent : baseEnd_5401731 < baseStart_5401731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401785 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 2, 4, 2]
def baseStart_5401785 : Nat := 118140960795 + 5401785 * 2 ^ 59
def prefixEnd_5401785 : Nat := 4983230072969 + 3 ^ 40 * 5401785 * 2
def baseEnd_5401785 : Nat := 2773712097247253225045149

theorem tailTrace_5401785 : CollatzResearch.WordTrace tailWord_5401785 prefixEnd_5401785 2773712097247253225045149 := by
  unfold tailWord_5401785
  simp only [CollatzResearch.WordTrace]
  refine ⟨197019284735262971275038809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131346189823508647516692539 197019284735262971275038809)
  ·
    refine ⟨147764463551447228456279107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197019284735262971275038809 147764463551447228456279107)
    ·
      refine ⟨221646695327170842684418661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147764463551447228456279107 221646695327170842684418661)
      ·
        refine ⟨41558755373844533003328499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221646695327170842684418661 41558755373844533003328499)
        ·
          refine ⟨62338133060766799504992749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41558755373844533003328499 62338133060766799504992749)
          ·
            refine ⟨23376799897787549814372281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62338133060766799504992749 23376799897787549814372281)
            ·
              refine ⟨17532599923340662360779211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23376799897787549814372281 17532599923340662360779211)
              ·
                refine ⟨26298899885010993541168817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17532599923340662360779211 26298899885010993541168817)
                ·
                  refine ⟨19724174913758245155876613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26298899885010993541168817 19724174913758245155876613)
                  ·
                    refine ⟨3698282796329670966726865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19724174913758245155876613 3698282796329670966726865)
                    ·
                      refine ⟨2773712097247253225045149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3698282796329670966726865 2773712097247253225045149)
                      ·
                        rfl

theorem cell23_5401785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_5401785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401785 prefixEnd_5401785 := by exact prefixLift 5401785
  have htrace : WordTrace (prefixWord ++ tailWord_5401785) baseStart_5401785 baseEnd_5401785 := by
    simpa [prefixWord, tailWord_5401785, baseEnd_5401785] using wordTrace_append hprefix tailTrace_5401785
  have hstable : (prefixWord ++ tailWord_5401785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401785).length < 2 ^ (prefixWord ++ tailWord_5401785).sum := by decide
  have hdescent : baseEnd_5401785 < baseStart_5401785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401811 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 6]
def baseStart_5401811 : Nat := 118140960795 + 5401811 * 2 ^ 59
def prefixEnd_5401811 : Nat := 4983230072969 + 3 ^ 40 * 5401811 * 2
def baseEnd_5401811 : Nat := 2773725447744270123320029

theorem tailTrace_5401811 : CollatzResearch.WordTrace tailWord_5401811 prefixEnd_5401811 2773725447744270123320029 := by
  unfold tailWord_5401811
  simp only [CollatzResearch.WordTrace]
  refine ⟨197020233033168777715485287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131346822022112518476990191 197020233033168777715485287)
  ·
    refine ⟨295530349549753166573227931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197020233033168777715485287 295530349549753166573227931)
    ·
      refine ⟨443295524324629749859841897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295530349549753166573227931 443295524324629749859841897)
      ·
        refine ⟨332471643243472312394881423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 443295524324629749859841897 332471643243472312394881423)
        ·
          refine ⟨498707464865208468592322135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332471643243472312394881423 498707464865208468592322135)
          ·
            refine ⟨748061197297812702888483203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498707464865208468592322135 748061197297812702888483203)
            ·
              refine ⟨1122091795946719054332724805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748061197297812702888483203 1122091795946719054332724805)
              ·
                refine ⟨210392211740009822687385901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1122091795946719054332724805 210392211740009822687385901)
                ·
                  refine ⟨78897079402503683507769713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210392211740009822687385901 78897079402503683507769713)
                  ·
                    refine ⟨59172809551877762630827285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78897079402503683507769713 59172809551877762630827285)
                    ·
                      refine ⟨2773725447744270123320029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59172809551877762630827285 2773725447744270123320029)
                      ·
                        rfl

theorem cell23_5401811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_5401811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401811 prefixEnd_5401811 := by exact prefixLift 5401811
  have htrace : WordTrace (prefixWord ++ tailWord_5401811) baseStart_5401811 baseEnd_5401811 := by
    simpa [prefixWord, tailWord_5401811, baseEnd_5401811] using wordTrace_append hprefix tailTrace_5401811
  have hstable : (prefixWord ++ tailWord_5401811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401811).length < 2 ^ (prefixWord ++ tailWord_5401811).sum := by decide
  have hdescent : baseEnd_5401811 < baseStart_5401811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401829 : List Nat := [1, 3, 1, 4, 4, 1, 1, 1, 3, 4]
def baseStart_5401829 : Nat := 118140960795 + 5401829 * 2 ^ 59
def prefixEnd_5401829 : Nat := 4983230072969 + 3 ^ 40 * 5401829 * 2
def baseEnd_5401829 : Nat := 924578230132017017631649

theorem tailTrace_5401829 : CollatzResearch.WordTrace tailWord_5401829 prefixEnd_5401829 924578230132017017631649 := by
  unfold tailWord_5401829
  simp only [CollatzResearch.WordTrace]
  refine ⟨197020889547103566789640541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131347259698069044526427027 197020889547103566789640541)
  ·
    refine ⟨73882833580163837546115203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197020889547103566789640541 73882833580163837546115203)
    ·
      refine ⟨110824250370245756319172805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73882833580163837546115203 110824250370245756319172805)
      ·
        refine ⟨20779546944421079309844901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110824250370245756319172805 20779546944421079309844901)
        ·
          refine ⟨3896165052078952370595919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20779546944421079309844901 3896165052078952370595919)
          ·
            refine ⟨5844247578118428555893879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3896165052078952370595919 5844247578118428555893879)
            ·
              refine ⟨8766371367177642833840819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5844247578118428555893879 8766371367177642833840819)
              ·
                refine ⟨13149557050766464250761229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8766371367177642833840819 13149557050766464250761229)
                ·
                  refine ⟨4931083894037424094035461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13149557050766464250761229 4931083894037424094035461)
                  ·
                    refine ⟨924578230132017017631649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4931083894037424094035461 924578230132017017631649)
                    ·
                      rfl

theorem cell23_5401829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 3, 4].length) (baseStart_5401829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401829 prefixEnd_5401829 := by exact prefixLift 5401829
  have htrace : WordTrace (prefixWord ++ tailWord_5401829) baseStart_5401829 baseEnd_5401829 := by
    simpa [prefixWord, tailWord_5401829, baseEnd_5401829] using wordTrace_append hprefix tailTrace_5401829
  have hstable : (prefixWord ++ tailWord_5401829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401829).length < 2 ^ (prefixWord ++ tailWord_5401829).sum := by decide
  have hdescent : baseEnd_5401829 < baseStart_5401829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401855 : List Nat := [1, 1, 2, 2, 1, 5, 3, 2, 1, 5]
def baseStart_5401855 : Nat := 118140960795 + 5401855 * 2 ^ 59
def prefixEnd_5401855 : Nat := 4983230072969 + 3 ^ 40 * 5401855 * 2
def baseEnd_5401855 : Nat := 924582680297689317056609

theorem tailTrace_5401855 : CollatzResearch.WordTrace tailWord_5401855 prefixEnd_5401855 924582680297689317056609 := by
  unfold tailWord_5401855
  simp only [CollatzResearch.WordTrace]
  refine ⟨197021837845009373230087019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131347891896672915486724679 197021837845009373230087019)
  ·
    refine ⟨295532756767514059845130529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197021837845009373230087019 295532756767514059845130529)
    ·
      refine ⟨221649567575635544883847897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295532756767514059845130529 221649567575635544883847897)
      ·
        refine ⟨166237175681726658662885923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221649567575635544883847897 166237175681726658662885923)
        ·
          refine ⟨249355763522589987994328885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166237175681726658662885923 249355763522589987994328885)
          ·
            refine ⟨23377102830242811374468333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 249355763522589987994328885 23377102830242811374468333)
            ·
              refine ⟨8766413561341054265425625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23377102830242811374468333 8766413561341054265425625)
              ·
                refine ⟨6574810171005790699069219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8766413561341054265425625 6574810171005790699069219)
                ·
                  refine ⟨9862215256508686048603829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6574810171005790699069219 9862215256508686048603829)
                  ·
                    refine ⟨924582680297689317056609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9862215256508686048603829 924582680297689317056609)
                    ·
                      rfl

theorem cell23_5401855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 5].length) (baseStart_5401855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401855 prefixEnd_5401855 := by exact prefixLift 5401855
  have htrace : WordTrace (prefixWord ++ tailWord_5401855) baseStart_5401855 baseEnd_5401855 := by
    simpa [prefixWord, tailWord_5401855, baseEnd_5401855] using wordTrace_append hprefix tailTrace_5401855
  have hstable : (prefixWord ++ tailWord_5401855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401855).length < 2 ^ (prefixWord ++ tailWord_5401855).sum := by decide
  have hdescent : baseEnd_5401855 < baseStart_5401855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401868 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 3, 6]
def baseStart_5401868 : Nat := 118140960795 + 5401868 * 2 ^ 59
def prefixEnd_5401868 : Nat := 4983230072969 + 3 ^ 40 * 5401868 * 2
def baseEnd_5401868 : Nat := 924584905380525466769089

theorem tailTrace_5401868 : CollatzResearch.WordTrace tailWord_5401868 prefixEnd_5401868 924584905380525466769089 := by
  unfold tailWord_5401868
  simp only [CollatzResearch.WordTrace]
  refine ⟨98511155996981138225155129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131348207995974850966873505 98511155996981138225155129)
  ·
    refine ⟨73883366997735853668866347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98511155996981138225155129 73883366997735853668866347)
    ·
      refine ⟨110825050496603780503299521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73883366997735853668866347 110825050496603780503299521)
      ·
        refine ⟨83118787872452835377474641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110825050496603780503299521 83118787872452835377474641)
        ·
          refine ⟨62339090904339626533105981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83118787872452835377474641 62339090904339626533105981)
          ·
            refine ⟨23377159089127359949914743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62339090904339626533105981 23377159089127359949914743)
            ·
              refine ⟨35065738633691039924872115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23377159089127359949914743 35065738633691039924872115)
              ·
                refine ⟨52598607950536559887308173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35065738633691039924872115 52598607950536559887308173)
                ·
                  refine ⟨19724477981451209957740565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52598607950536559887308173 19724477981451209957740565)
                  ·
                    refine ⟨924584905380525466769089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19724477981451209957740565 924584905380525466769089)
                    ·
                      rfl

theorem cell23_5401868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_5401868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401868 prefixEnd_5401868 := by exact prefixLift 5401868
  have htrace : WordTrace (prefixWord ++ tailWord_5401868) baseStart_5401868 baseEnd_5401868 := by
    simpa [prefixWord, tailWord_5401868, baseEnd_5401868] using wordTrace_append hprefix tailTrace_5401868
  have hstable : (prefixWord ++ tailWord_5401868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401868).length < 2 ^ (prefixWord ++ tailWord_5401868).sum := by decide
  have hdescent : baseEnd_5401868 < baseStart_5401868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401905 : List Nat := [1, 2, 2, 3, 3, 1, 1, 3, 1, 2, 4]
def baseStart_5401905 : Nat := 118140960795 + 5401905 * 2 ^ 59
def prefixEnd_5401905 : Nat := 4983230072969 + 3 ^ 40 * 5401905 * 2
def baseEnd_5401905 : Nat := 2773773714925792755544597

theorem tailTrace_5401905 : CollatzResearch.WordTrace tailWord_5401905 prefixEnd_5401905 2773773714925792755544597 := by
  unfold tailWord_5401905
  simp only [CollatzResearch.WordTrace]
  refine ⟨197023661494828231769407169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131349107663218821179604779 197023661494828231769407169)
  ·
    refine ⟨147767746121121173827055377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197023661494828231769407169 147767746121121173827055377)
    ·
      refine ⟨110825809590840880370291533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147767746121121173827055377 110825809590840880370291533)
      ·
        refine ⟨41559678596565330138859325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110825809590840880370291533 41559678596565330138859325)
        ·
          refine ⟨15584879473711998802072247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41559678596565330138859325 15584879473711998802072247)
          ·
            refine ⟨23377319210567998203108371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15584879473711998802072247 23377319210567998203108371)
            ·
              refine ⟨35065978815851997304662557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23377319210567998203108371 35065978815851997304662557)
              ·
                refine ⟨13149742055944498989248459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35065978815851997304662557 13149742055944498989248459)
                ·
                  refine ⟨19724613083916748483872689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13149742055944498989248459 19724613083916748483872689)
                  ·
                    refine ⟨14793459812937561362904517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19724613083916748483872689 14793459812937561362904517)
                    ·
                      refine ⟨2773773714925792755544597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14793459812937561362904517 2773773714925792755544597)
                      ·
                        rfl

theorem cell23_5401905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_5401905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401905 prefixEnd_5401905 := by exact prefixLift 5401905
  have htrace : WordTrace (prefixWord ++ tailWord_5401905) baseStart_5401905 baseEnd_5401905 := by
    simpa [prefixWord, tailWord_5401905, baseEnd_5401905] using wordTrace_append hprefix tailTrace_5401905
  have hstable : (prefixWord ++ tailWord_5401905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401905).length < 2 ^ (prefixWord ++ tailWord_5401905).sum := by decide
  have hdescent : baseEnd_5401905 < baseStart_5401905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401909 : List Nat := [1, 3, 3, 1, 2, 3, 1, 2, 3, 2, 2]
def baseStart_5401909 : Nat := 118140960795 + 5401909 * 2 ^ 59
def prefixEnd_5401909 : Nat := 4983230072969 + 3 ^ 40 * 5401909 * 2
def baseEnd_5401909 : Nat := 2773775768848410739894579

theorem tailTrace_5401909 : CollatzResearch.WordTrace tailWord_5401909 prefixEnd_5401909 2773775768848410739894579 := by
  unfold tailWord_5401909
  simp only [CollatzResearch.WordTrace]
  refine ⟨197023807386813740452552781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131349204924542493635035187 197023807386813740452552781)
  ·
    refine ⟨73883927770055152669707293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197023807386813740452552781 73883927770055152669707293)
    ·
      refine ⟨27706472913770682251140235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73883927770055152669707293 27706472913770682251140235)
      ·
        refine ⟨41559709370656023376710353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27706472913770682251140235 41559709370656023376710353)
        ·
          refine ⟨31169782027992017532532765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41559709370656023376710353 31169782027992017532532765)
          ·
            refine ⟨11688668260497006574699787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31169782027992017532532765 11688668260497006574699787)
            ·
              refine ⟨17533002390745509862049681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11688668260497006574699787 17533002390745509862049681)
              ·
                refine ⟨13149751793059132396537261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17533002390745509862049681 13149751793059132396537261)
                ·
                  refine ⟨4931156922397174648701473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13149751793059132396537261 4931156922397174648701473)
                  ·
                    refine ⟨3698367691797880986526105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4931156922397174648701473 3698367691797880986526105)
                    ·
                      refine ⟨2773775768848410739894579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3698367691797880986526105 2773775768848410739894579)
                      ·
                        rfl

theorem cell23_5401909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_5401909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401909 prefixEnd_5401909 := by exact prefixLift 5401909
  have htrace : WordTrace (prefixWord ++ tailWord_5401909) baseStart_5401909 baseEnd_5401909 := by
    simpa [prefixWord, tailWord_5401909, baseEnd_5401909] using wordTrace_append hprefix tailTrace_5401909
  have hstable : (prefixWord ++ tailWord_5401909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401909).length < 2 ^ (prefixWord ++ tailWord_5401909).sum := by decide
  have hdescent : baseEnd_5401909 < baseStart_5401909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401959 : List Nat := [1, 1, 5, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_5401959 : Nat := 118140960795 + 5401959 * 2 ^ 59
def prefixEnd_5401959 : Nat := 4983230072969 + 3 ^ 40 * 5401959 * 2
def baseEnd_5401959 : Nat := 2773801442881135544269349

theorem tailTrace_5401959 : CollatzResearch.WordTrace tailWord_5401959 prefixEnd_5401959 2773801442881135544269349 := by
  unfold tailWord_5401959
  simp only [CollatzResearch.WordTrace]
  refine ⟨197025631036632598991872931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131350420691088399327915287 197025631036632598991872931)
  ·
    refine ⟨295538446554948898487809397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197025631036632598991872931 295538446554948898487809397)
    ·
      refine ⟨27706729364526459233232131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 295538446554948898487809397 27706729364526459233232131)
      ·
        refine ⟨41560094046789688849848197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27706729364526459233232131 41560094046789688849848197)
        ·
          refine ⟨7792517633773066659346537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41560094046789688849848197 7792517633773066659346537)
          ·
            refine ⟨5844388225329799994509903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7792517633773066659346537 5844388225329799994509903)
            ·
              refine ⟨8766582337994699991764855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5844388225329799994509903 8766582337994699991764855)
              ·
                refine ⟨13149873506992049987647283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8766582337994699991764855 13149873506992049987647283)
                ·
                  refine ⟨19724810260488074981470925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13149873506992049987647283 19724810260488074981470925)
                  ·
                    refine ⟨7396803847683028118051597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19724810260488074981470925 7396803847683028118051597)
                    ·
                      refine ⟨2773801442881135544269349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7396803847683028118051597 2773801442881135544269349)
                      ·
                        rfl

theorem cell23_5401959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_5401959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401959 prefixEnd_5401959 := by exact prefixLift 5401959
  have htrace : WordTrace (prefixWord ++ tailWord_5401959) baseStart_5401959 baseEnd_5401959 := by
    simpa [prefixWord, tailWord_5401959, baseEnd_5401959] using wordTrace_append hprefix tailTrace_5401959
  have hstable : (prefixWord ++ tailWord_5401959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401959).length < 2 ^ (prefixWord ++ tailWord_5401959).sum := by decide
  have hdescent : baseEnd_5401959 < baseStart_5401959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5401966 : List Nat := [4, 1, 2, 4, 2, 1, 2, 7]
def baseStart_5401966 : Nat := 118140960795 + 5401966 * 2 ^ 59
def prefixEnd_5401966 : Nat := 4983230072969 + 3 ^ 40 * 5401966 * 2
def baseEnd_5401966 : Nat := 102733519897989519143771

theorem tailTrace_5401966 : CollatzResearch.WordTrace tailWord_5401966 prefixEnd_5401966 102733519897989519143771 := by
  unfold tailWord_5401966
  simp only [CollatzResearch.WordTrace]
  refine ⟨24628235793450904898422219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131350590898404826124918501 24628235793450904898422219)
  ·
    refine ⟨36942353690176357347633329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24628235793450904898422219 36942353690176357347633329)
    ·
      refine ⟨27706765267632268010724997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36942353690176357347633329 27706765267632268010724997)
      ·
        refine ⟨5195018487681050252010937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27706765267632268010724997 5195018487681050252010937)
        ·
          refine ⟨3896263865760787689008203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5195018487681050252010937 3896263865760787689008203)
          ·
            refine ⟨5844395798641181533512305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3896263865760787689008203 5844395798641181533512305)
            ·
              refine ⟨4383296848980886150134229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5844395798641181533512305 4383296848980886150134229)
              ·
                refine ⟨102733519897989519143771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4383296848980886150134229 102733519897989519143771)
                ·
                  rfl

theorem cell23_5401966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 7].length) (baseStart_5401966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5401966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5401966 prefixEnd_5401966 := by exact prefixLift 5401966
  have htrace : WordTrace (prefixWord ++ tailWord_5401966) baseStart_5401966 baseEnd_5401966 := by
    simpa [prefixWord, tailWord_5401966, baseEnd_5401966] using wordTrace_append hprefix tailTrace_5401966
  have hstable : (prefixWord ++ tailWord_5401966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5401966).length < 2 ^ (prefixWord ++ tailWord_5401966).sum := by decide
  have hdescent : baseEnd_5401966 < baseStart_5401966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5401966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402005 : List Nat := [1, 3, 2, 1, 1, 2, 5, 1, 7]
def baseStart_5402005 : Nat := 118140960795 + 5402005 * 2 ^ 59
def prefixEnd_5402005 : Nat := 4983230072969 + 3 ^ 40 * 5402005 * 2
def baseEnd_5402005 : Nat := 308202784776804707143793

theorem tailTrace_5402005 : CollatzResearch.WordTrace tailWord_5402005 prefixEnd_5402005 308202784776804707143793 := by
  unfold tailWord_5402005
  simp only [CollatzResearch.WordTrace]
  refine ⟨197027308794465948848047469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131351539196310632565364979 197027308794465948848047469)
  ·
    refine ⟨73885240797924730818017801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197027308794465948848047469 73885240797924730818017801)
    ·
      refine ⟨55413930598443548113513351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73885240797924730818017801 55413930598443548113513351)
      ·
        refine ⟨83120895897665322170270027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55413930598443548113513351 83120895897665322170270027)
        ·
          refine ⟨124681343846497983255405041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83120895897665322170270027 124681343846497983255405041)
          ·
            refine ⟨93511007884873487441553781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124681343846497983255405041 93511007884873487441553781)
            ·
              refine ⟨8766656989206889447645667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93511007884873487441553781 8766656989206889447645667)
              ·
                refine ⟨13149985483810334171468501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8766656989206889447645667 13149985483810334171468501)
                ·
                  refine ⟨308202784776804707143793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13149985483810334171468501 308202784776804707143793)
                  ·
                    rfl

theorem cell23_5402005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 7].length) (baseStart_5402005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402005 prefixEnd_5402005 := by exact prefixLift 5402005
  have htrace : WordTrace (prefixWord ++ tailWord_5402005) baseStart_5402005 baseEnd_5402005 := by
    simpa [prefixWord, tailWord_5402005, baseEnd_5402005] using wordTrace_append hprefix tailTrace_5402005
  have hstable : (prefixWord ++ tailWord_5402005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402005).length < 2 ^ (prefixWord ++ tailWord_5402005).sum := by decide
  have hdescent : baseEnd_5402005 < baseStart_5402005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402045 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_5402045 : Nat := 118140960795 + 5402045 * 2 ^ 59
def prefixEnd_5402045 : Nat := 4983230072969 + 3 ^ 40 * 5402045 * 2
def baseEnd_5402045 : Nat := 2773845602217422207793953

theorem tailTrace_5402045 : CollatzResearch.WordTrace tailWord_5402045 prefixEnd_5402045 2773845602217422207793953 := by
  unfold tailWord_5402045
  simp only [CollatzResearch.WordTrace]
  refine ⟨197028767714321035679503589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131352511809547357119669059 197028767714321035679503589)
  ·
    refine ⟨36942893946435194189906923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197028767714321035679503589 36942893946435194189906923)
    ·
      refine ⟨55414340919652791284860385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36942893946435194189906923 55414340919652791284860385)
      ·
        refine ⟨41560755689739593463645289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55414340919652791284860385 41560755689739593463645289)
        ·
          refine ⟨31170566767304695097733967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41560755689739593463645289 31170566767304695097733967)
          ·
            refine ⟨46755850150957042646600951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31170566767304695097733967 46755850150957042646600951)
            ·
              refine ⟨70133775226435563969901427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46755850150957042646600951 70133775226435563969901427)
              ·
                refine ⟨105200662839653345954852141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70133775226435563969901427 105200662839653345954852141)
                ·
                  refine ⟨39450248564870004733069553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105200662839653345954852141 39450248564870004733069553)
                  ·
                    refine ⟨29587686423652503549802165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39450248564870004733069553 29587686423652503549802165)
                    ·
                      refine ⟨2773845602217422207793953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29587686423652503549802165 2773845602217422207793953)
                      ·
                        rfl

theorem cell23_5402045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_5402045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402045 prefixEnd_5402045 := by exact prefixLift 5402045
  have htrace : WordTrace (prefixWord ++ tailWord_5402045) baseStart_5402045 baseEnd_5402045 := by
    simpa [prefixWord, tailWord_5402045, baseEnd_5402045] using wordTrace_append hprefix tailTrace_5402045
  have hstable : (prefixWord ++ tailWord_5402045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402045).length < 2 ^ (prefixWord ++ tailWord_5402045).sum := by decide
  have hdescent : baseEnd_5402045 < baseStart_5402045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402072 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 1, 6, 2]
def baseStart_5402072 : Nat := 118140960795 + 5402072 * 2 ^ 59
def prefixEnd_5402072 : Nat := 4983230072969 + 3 ^ 40 * 5402072 * 2
def baseEnd_5402072 : Nat := 2773859466195093602156329

theorem tailTrace_5402072 : CollatzResearch.WordTrace tailWord_5402072 prefixEnd_5402072 2773859466195093602156329 := by
  unfold tailWord_5402072
  simp only [CollatzResearch.WordTrace]
  refine ⟨98514876242611609645368235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131353168323482146193824313 98514876242611609645368235)
  ·
    refine ⟨147772314363917414468052353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98514876242611609645368235 147772314363917414468052353)
    ·
      refine ⟨110829235772938060851039265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147772314363917414468052353 110829235772938060851039265)
      ·
        refine ⟨83121926829703545638279449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110829235772938060851039265 83121926829703545638279449)
        ·
          refine ⟨62341445122277659228709587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83121926829703545638279449 62341445122277659228709587)
          ·
            refine ⟨93512167683416488843064381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62341445122277659228709587 93512167683416488843064381)
            ·
              refine ⟨35067062881281183316149143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93512167683416488843064381 35067062881281183316149143)
              ·
                refine ⟨52600594321921774974223715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35067062881281183316149143 52600594321921774974223715)
                ·
                  refine ⟨78900891482882662461335573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52600594321921774974223715 78900891482882662461335573)
                  ·
                    refine ⟨3698479288260124802875105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78900891482882662461335573 3698479288260124802875105)
                    ·
                      refine ⟨2773859466195093602156329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3698479288260124802875105 2773859466195093602156329)
                      ·
                        rfl

theorem cell23_5402072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_5402072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402072 prefixEnd_5402072 := by exact prefixLift 5402072
  have htrace : WordTrace (prefixWord ++ tailWord_5402072) baseStart_5402072 baseEnd_5402072 := by
    simpa [prefixWord, tailWord_5402072, baseEnd_5402072] using wordTrace_append hprefix tailTrace_5402072
  have hstable : (prefixWord ++ tailWord_5402072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402072).length < 2 ^ (prefixWord ++ tailWord_5402072).sum := by decide
  have hdescent : baseEnd_5402072 < baseStart_5402072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402075 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 3]
def baseStart_5402075 : Nat := 118140960795 + 5402075 * 2 ^ 59
def prefixEnd_5402075 : Nat := 4983230072969 + 3 ^ 40 * 5402075 * 2
def baseEnd_5402075 : Nat := 2773861006637057090418815

theorem tailTrace_5402075 : CollatzResearch.WordTrace tailWord_5402075 prefixEnd_5402075 2773861006637057090418815 := by
  unfold tailWord_5402075
  simp only [CollatzResearch.WordTrace]
  refine ⟨197029861904212350803095679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131353241269474900535397119 197029861904212350803095679)
  ·
    refine ⟨295544792856318526204643519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197029861904212350803095679 295544792856318526204643519)
    ·
      refine ⟨443317189284477789306965279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295544792856318526204643519 443317189284477789306965279)
      ·
        refine ⟨664975783926716683960447919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443317189284477789306965279 664975783926716683960447919)
        ·
          refine ⟨997463675890075025940671879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 664975783926716683960447919 997463675890075025940671879)
          ·
            refine ⟨1496195513835112538911007819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997463675890075025940671879 1496195513835112538911007819)
            ·
              refine ⟨2244293270752668808366511729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496195513835112538911007819 2244293270752668808366511729)
              ·
                refine ⟨1683219953064501606274883797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2244293270752668808366511729 1683219953064501606274883797)
                ·
                  refine ⟨39450467649949256397067589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1683219953064501606274883797 39450467649949256397067589)
                  ·
                    refine ⟨7396962684365485574450173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39450467649949256397067589 7396962684365485574450173)
                    ·
                      refine ⟨2773861006637057090418815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7396962684365485574450173 2773861006637057090418815)
                      ·
                        rfl

theorem cell23_5402075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 3].length) (baseStart_5402075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402075 prefixEnd_5402075 := by exact prefixLift 5402075
  have htrace : WordTrace (prefixWord ++ tailWord_5402075) baseStart_5402075 baseEnd_5402075 := by
    simpa [prefixWord, tailWord_5402075, baseEnd_5402075] using wordTrace_append hprefix tailTrace_5402075
  have hstable : (prefixWord ++ tailWord_5402075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402075).length < 2 ^ (prefixWord ++ tailWord_5402075).sum := by decide
  have hdescent : baseEnd_5402075 < baseStart_5402075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402092 : List Nat := [2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 3]
def baseStart_5402092 : Nat := 118140960795 + 5402092 * 2 ^ 59
def prefixEnd_5402092 : Nat := 4983230072969 + 3 ^ 40 * 5402092 * 2
def baseEnd_5402092 : Nat := 2773869735808183523906237

theorem tailTrace_5402092 : CollatzResearch.WordTrace tailWord_5402092 prefixEnd_5402092 2773869735808183523906237 := by
  unfold tailWord_5402092
  simp only [CollatzResearch.WordTrace]
  refine ⟨98515240972575381353232265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131353654630100508470976353 98515240972575381353232265)
  ·
    refine ⟨73886430729431536014924199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98515240972575381353232265 73886430729431536014924199)
    ·
      refine ⟨110829646094147304022386299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73886430729431536014924199 110829646094147304022386299)
      ·
        refine ⟨166244469141220956033579449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110829646094147304022386299 166244469141220956033579449)
        ·
          refine ⟨124683351855915717025184587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166244469141220956033579449 124683351855915717025184587)
          ·
            refine ⟨187025027783873575537776881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124683351855915717025184587 187025027783873575537776881)
            ·
              refine ⟨140268770837905181653332661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187025027783873575537776881 140268770837905181653332661)
              ·
                refine ⟨13150197266053610779999937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140268770837905181653332661 13150197266053610779999937)
                ·
                  refine ⟨9862647949540208084999953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13150197266053610779999937 9862647949540208084999953)
                  ·
                    refine ⟨7396985962155156063749965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9862647949540208084999953 7396985962155156063749965)
                    ·
                      refine ⟨2773869735808183523906237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7396985962155156063749965 2773869735808183523906237)
                      ·
                        rfl

theorem cell23_5402092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_5402092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402092 prefixEnd_5402092 := by exact prefixLift 5402092
  have htrace : WordTrace (prefixWord ++ tailWord_5402092) baseStart_5402092 baseEnd_5402092 := by
    simpa [prefixWord, tailWord_5402092, baseEnd_5402092] using wordTrace_append hprefix tailTrace_5402092
  have hstable : (prefixWord ++ tailWord_5402092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402092).length < 2 ^ (prefixWord ++ tailWord_5402092).sum := by decide
  have hdescent : baseEnd_5402092 < baseStart_5402092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402102 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_5402102 : Nat := 118140960795 + 5402102 * 2 ^ 59
def prefixEnd_5402102 : Nat := 4983230072969 + 3 ^ 40 * 5402102 * 2
def baseEnd_5402102 : Nat := 2773874870614728484781191

theorem tailTrace_5402102 : CollatzResearch.WordTrace tailWord_5402102 prefixEnd_5402102 2773874870614728484781191 := by
  unfold tailWord_5402102
  simp only [CollatzResearch.WordTrace]
  refine ⟨12314427917194658400895535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131353897783409689609552373 12314427917194658400895535)
  ·
    refine ⟨18471641875791987601343303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12314427917194658400895535 18471641875791987601343303)
    ·
      refine ⟨27707462813687981402014955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18471641875791987601343303 27707462813687981402014955)
      ·
        refine ⟨41561194220531972103022433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27707462813687981402014955 41561194220531972103022433)
        ·
          refine ⟨31170895665398979077266825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41561194220531972103022433 31170895665398979077266825)
          ·
            refine ⟨23378171749049234307950119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31170895665398979077266825 23378171749049234307950119)
            ·
              refine ⟨35067257623573851461925179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23378171749049234307950119 35067257623573851461925179)
              ·
                refine ⟨52600886435360777192887769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35067257623573851461925179 52600886435360777192887769)
                ·
                  refine ⟨39450664826520582894665827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52600886435360777192887769 39450664826520582894665827)
                  ·
                    refine ⟨59175997239780874341998741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39450664826520582894665827 59175997239780874341998741)
                    ·
                      refine ⟨2773874870614728484781191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59175997239780874341998741 2773874870614728484781191)
                      ·
                        rfl

theorem cell23_5402102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_5402102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402102 prefixEnd_5402102 := by exact prefixLift 5402102
  have htrace : WordTrace (prefixWord ++ tailWord_5402102) baseStart_5402102 baseEnd_5402102 := by
    simpa [prefixWord, tailWord_5402102, baseEnd_5402102] using wordTrace_append hprefix tailTrace_5402102
  have hstable : (prefixWord ++ tailWord_5402102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402102).length < 2 ^ (prefixWord ++ tailWord_5402102).sum := by decide
  have hdescent : baseEnd_5402102 < baseStart_5402102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402116 : List Nat := [2, 3, 2, 3, 2, 1, 2, 1, 3, 4]
def baseStart_5402116 : Nat := 118140960795 + 5402116 * 2 ^ 59
def prefixEnd_5402116 : Nat := 4983230072969 + 3 ^ 40 * 5402116 * 2
def baseEnd_5402116 : Nat := 924627353114630476668709

theorem tailTrace_5402116 : CollatzResearch.WordTrace tailWord_5402116 prefixEnd_5402116 924627353114630476668709 := by
  unfold tailWord_5402116
  simp only [CollatzResearch.WordTrace]
  refine ⟨98515678648531907402669101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131354238198042543203558801 98515678648531907402669101)
  ·
    refine ⟨36943379493199465276000913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98515678648531907402669101 36943379493199465276000913)
    ·
      refine ⟨27707534619899598957000685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36943379493199465276000913 27707534619899598957000685)
      ·
        refine ⟨10390325482462349608875257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27707534619899598957000685 10390325482462349608875257)
        ·
          refine ⟨7792744111846762206656443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10390325482462349608875257 7792744111846762206656443)
          ·
            refine ⟨11689116167770143309984665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7792744111846762206656443 11689116167770143309984665)
            ·
              refine ⟨8766837125827607482488499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11689116167770143309984665 8766837125827607482488499)
              ·
                refine ⟨13150255688741411223732749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8766837125827607482488499 13150255688741411223732749)
                ·
                  refine ⟨4931345883278029208899781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13150255688741411223732749 4931345883278029208899781)
                  ·
                    refine ⟨924627353114630476668709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4931345883278029208899781 924627353114630476668709)
                    ·
                      rfl

theorem cell23_5402116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_5402116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402116 prefixEnd_5402116 := by exact prefixLift 5402116
  have htrace : WordTrace (prefixWord ++ tailWord_5402116) baseStart_5402116 baseEnd_5402116 := by
    simpa [prefixWord, tailWord_5402116, baseEnd_5402116] using wordTrace_append hprefix tailTrace_5402116
  have hstable : (prefixWord ++ tailWord_5402116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402116).length < 2 ^ (prefixWord ++ tailWord_5402116).sum := by decide
  have hdescent : baseEnd_5402116 < baseStart_5402116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402149 : List Nat := [1, 3, 1, 2, 2, 1, 1, 5, 2, 3, 2]
def baseStart_5402149 : Nat := 118140960795 + 5402149 * 2 ^ 59
def prefixEnd_5402149 : Nat := 4983230072969 + 3 ^ 40 * 5402149 * 2
def baseEnd_5402149 : Nat := 2773899004205489800893475

theorem tailTrace_5402149 : CollatzResearch.WordTrace tailWord_5402149 prefixEnd_5402149 2773899004205489800893475 := by
  unfold tailWord_5402149
  simp only [CollatzResearch.WordTrace]
  refine ⟨197032560905944261441289501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131355040603962840960859667 197032560905944261441289501)
  ·
    refine ⟨73887210339729098040483563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197032560905944261441289501 73887210339729098040483563)
    ·
      refine ⟨110830815509593647060725345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73887210339729098040483563 110830815509593647060725345)
      ·
        refine ⟨83123111632195235295544009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110830815509593647060725345 83123111632195235295544009)
        ·
          refine ⟨62342333724146426471658007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83123111632195235295544009 62342333724146426471658007)
          ·
            refine ⟨93513500586219639707487011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62342333724146426471658007 93513500586219639707487011)
            ·
              refine ⟨140270250879329459561230517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93513500586219639707487011 140270250879329459561230517)
              ·
                refine ⟨13150336019937136833865361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140270250879329459561230517 13150336019937136833865361)
                ·
                  refine ⟨9862752014952852625399021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13150336019937136833865361 9862752014952852625399021)
                  ·
                    refine ⟨3698532005607319734524633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9862752014952852625399021 3698532005607319734524633)
                    ·
                      refine ⟨2773899004205489800893475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3698532005607319734524633 2773899004205489800893475)
                      ·
                        rfl

theorem cell23_5402149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_5402149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402149 prefixEnd_5402149 := by exact prefixLift 5402149
  have htrace : WordTrace (prefixWord ++ tailWord_5402149) baseStart_5402149 baseEnd_5402149 := by
    simpa [prefixWord, tailWord_5402149, baseEnd_5402149] using wordTrace_append hprefix tailTrace_5402149
  have hstable : (prefixWord ++ tailWord_5402149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402149).length < 2 ^ (prefixWord ++ tailWord_5402149).sum := by decide
  have hdescent : baseEnd_5402149 < baseStart_5402149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402162 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_5402162 : Nat := 118140960795 + 5402162 * 2 ^ 59
def prefixEnd_5402162 : Nat := 4983230072969 + 3 ^ 40 * 5402162 * 2
def baseEnd_5402162 : Nat := 2773905679453998250030915

theorem tailTrace_5402162 : CollatzResearch.WordTrace tailWord_5402162 prefixEnd_5402162 2773905679453998250030915 := by
  unfold tailWord_5402162
  simp only [CollatzResearch.WordTrace]
  refine ⟨49258258763724291165378185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131355356703264776441008493 49258258763724291165378185)
  ·
    refine ⟨36943694072793218374033639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49258258763724291165378185 36943694072793218374033639)
    ·
      refine ⟨55415541109189827561050459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36943694072793218374033639 55415541109189827561050459)
      ·
        refine ⟨83123311663784741341575689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55415541109189827561050459 83123311663784741341575689)
        ·
          refine ⟨62342483747838556006181767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83123311663784741341575689 62342483747838556006181767)
          ·
            refine ⟨93513725621757834009272651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62342483747838556006181767 93513725621757834009272651)
            ·
              refine ⟨140270588432636751013908977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93513725621757834009272651 140270588432636751013908977)
              ·
                refine ⟨105202941324477563260431733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140270588432636751013908977 105202941324477563260431733)
                ·
                  refine ⟨9862775749169771555665475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105202941324477563260431733 9862775749169771555665475)
                  ·
                    refine ⟨14794163623754657333498213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9862775749169771555665475 14794163623754657333498213)
                    ·
                      refine ⟨2773905679453998250030915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14794163623754657333498213 2773905679453998250030915)
                      ·
                        rfl

theorem cell23_5402162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_5402162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402162 prefixEnd_5402162 := by exact prefixLift 5402162
  have htrace : WordTrace (prefixWord ++ tailWord_5402162) baseStart_5402162 baseEnd_5402162 := by
    simpa [prefixWord, tailWord_5402162, baseEnd_5402162] using wordTrace_append hprefix tailTrace_5402162
  have hstable : (prefixWord ++ tailWord_5402162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402162).length < 2 ^ (prefixWord ++ tailWord_5402162).sum := by decide
  have hdescent : baseEnd_5402162 < baseStart_5402162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402173 : List Nat := [1, 4, 1, 3, 3, 2, 1, 1, 3, 1, 3]
def baseStart_5402173 : Nat := 118140960795 + 5402173 * 2 ^ 59
def prefixEnd_5402173 : Nat := 4983230072969 + 3 ^ 40 * 5402173 * 2
def baseEnd_5402173 : Nat := 2773911327741197706993365

theorem tailTrace_5402173 : CollatzResearch.WordTrace tailWord_5402173 prefixEnd_5402173 2773911327741197706993365 := by
  unfold tailWord_5402173
  simp only [CollatzResearch.WordTrace]
  refine ⟨197033436257857313540163173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131355624171904875693442115 197033436257857313540163173)
  ·
    refine ⟨36943769298348246288780595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197033436257857313540163173 36943769298348246288780595)
    ·
      refine ⟨55415653947522369433170893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36943769298348246288780595 55415653947522369433170893)
      ·
        refine ⟨20780870230320888537439085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55415653947522369433170893 20780870230320888537439085)
        ·
          refine ⟨7792826336370333201539657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20780870230320888537439085 7792826336370333201539657)
          ·
            refine ⟨5844619752277749901154743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7792826336370333201539657 5844619752277749901154743)
            ·
              refine ⟨8766929628416624851732115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5844619752277749901154743 8766929628416624851732115)
              ·
                refine ⟨13150394442624937277598173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8766929628416624851732115 13150394442624937277598173)
                ·
                  refine ⟨4931397915984351479099315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13150394442624937277598173 4931397915984351479099315)
                  ·
                    refine ⟨7397096873976527218648973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4931397915984351479099315 7397096873976527218648973)
                    ·
                      refine ⟨2773911327741197706993365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7397096873976527218648973 2773911327741197706993365)
                      ·
                        rfl

theorem cell23_5402173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_5402173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402173 prefixEnd_5402173 := by exact prefixLift 5402173
  have htrace : WordTrace (prefixWord ++ tailWord_5402173) baseStart_5402173 baseEnd_5402173 := by
    simpa [prefixWord, tailWord_5402173, baseEnd_5402173] using wordTrace_append hprefix tailTrace_5402173
  have hstable : (prefixWord ++ tailWord_5402173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402173).length < 2 ^ (prefixWord ++ tailWord_5402173).sum := by decide
  have hdescent : baseEnd_5402173 < baseStart_5402173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402192 : List Nat := [2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 4]
def baseStart_5402192 : Nat := 118140960795 + 5402192 * 2 ^ 59
def prefixEnd_5402192 : Nat := 4983230072969 + 3 ^ 40 * 5402192 * 2
def baseEnd_5402192 : Nat := 2773921083873633132655777

theorem tailTrace_5402192 : CollatzResearch.WordTrace tailWord_5402192 prefixEnd_5402192 2773921083873633132655777 := by
  unfold tailWord_5402192
  simp only [CollatzResearch.WordTrace]
  refine ⟨98517064622394239892552415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131356086163192319856736553 98517064622394239892552415)
  ·
    refine ⟨147775596933591359838828623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98517064622394239892552415 147775596933591359838828623)
    ·
      refine ⟨221663395400387039758242935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147775596933591359838828623 221663395400387039758242935)
      ·
        refine ⟨332495093100580559637364403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221663395400387039758242935 332495093100580559637364403)
        ·
          refine ⟨498742639650870839456046605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332495093100580559637364403 498742639650870839456046605)
          ·
            refine ⟨187028489869076564796017477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 498742639650870839456046605 187028489869076564796017477)
            ·
              refine ⟨35067841850451855899253277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187028489869076564796017477 35067841850451855899253277)
              ·
                refine ⟨13150440693919445962219979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35067841850451855899253277 13150440693919445962219979)
                ·
                  refine ⟨19725661040879168943329969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13150440693919445962219979 19725661040879168943329969)
                  ·
                    refine ⟨14794245780659376707497477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19725661040879168943329969 14794245780659376707497477)
                    ·
                      refine ⟨2773921083873633132655777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14794245780659376707497477 2773921083873633132655777)
                      ·
                        rfl

theorem cell23_5402192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 4].length) (baseStart_5402192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402192 prefixEnd_5402192 := by exact prefixLift 5402192
  have htrace : WordTrace (prefixWord ++ tailWord_5402192) baseStart_5402192 baseEnd_5402192 := by
    simpa [prefixWord, tailWord_5402192, baseEnd_5402192] using wordTrace_append hprefix tailTrace_5402192
  have hstable : (prefixWord ++ tailWord_5402192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402192).length < 2 ^ (prefixWord ++ tailWord_5402192).sum := by decide
  have hdescent : baseEnd_5402192 < baseStart_5402192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402195 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 7]
def baseStart_5402195 : Nat := 118140960795 + 5402195 * 2 ^ 59
def prefixEnd_5402195 : Nat := 4983230072969 + 3 ^ 40 * 5402195 * 2
def baseEnd_5402195 : Nat := 2773922624315596620918263

theorem tailTrace_5402195 : CollatzResearch.WordTrace tailWord_5402195 prefixEnd_5402195 2773922624315596620918263 := by
  unfold tailWord_5402195
  simp only [CollatzResearch.WordTrace]
  refine ⟨197034238663777611297464039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131356159109185074198309359 197034238663777611297464039)
  ·
    refine ⟨295551357995666416946196059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197034238663777611297464039 295551357995666416946196059)
    ·
      refine ⟨443327036993499625419294089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295551357995666416946196059 443327036993499625419294089)
      ·
        refine ⟨332495277745124719064470567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 443327036993499625419294089 332495277745124719064470567)
        ·
          refine ⟨498742916617687078596705851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332495277745124719064470567 498742916617687078596705851)
          ·
            refine ⟨748114374926530617895058777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498742916617687078596705851 748114374926530617895058777)
            ·
              refine ⟨561085781194897963421294083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 748114374926530617895058777 561085781194897963421294083)
              ·
                refine ⟨841628671792346945131941125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561085781194897963421294083 841628671792346945131941125)
                ·
                  refine ⟨157805375961065052212238961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 841628671792346945131941125 157805375961065052212238961)
                  ·
                    refine ⟨118354031970798789159179221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 157805375961065052212238961 118354031970798789159179221)
                    ·
                      refine ⟨2773922624315596620918263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118354031970798789159179221 2773922624315596620918263)
                      ·
                        rfl

theorem cell23_5402195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_5402195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402195 prefixEnd_5402195 := by exact prefixLift 5402195
  have htrace : WordTrace (prefixWord ++ tailWord_5402195) baseStart_5402195 baseEnd_5402195 := by
    simpa [prefixWord, tailWord_5402195, baseEnd_5402195] using wordTrace_append hprefix tailTrace_5402195
  have hstable : (prefixWord ++ tailWord_5402195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402195).length < 2 ^ (prefixWord ++ tailWord_5402195).sum := by decide
  have hdescent : baseEnd_5402195 < baseStart_5402195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402196 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 5, 2, 2]
def baseStart_5402196 : Nat := 118140960795 + 5402196 * 2 ^ 59
def prefixEnd_5402196 : Nat := 4983230072969 + 3 ^ 40 * 5402196 * 2
def baseEnd_5402196 : Nat := 2773923137796251117005759

theorem tailTrace_5402196 : CollatzResearch.WordTrace tailWord_5402196 prefixEnd_5402196 2773923137796251117005759 := by
  unfold tailWord_5402196
  simp only [CollatzResearch.WordTrace]
  refine ⟨98517137568386994234125221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131356183424515992312166961 98517137568386994234125221)
  ·
    refine ⟨18471963294072561418898479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98517137568386994234125221 18471963294072561418898479)
    ·
      refine ⟨27707944941108842128347719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18471963294072561418898479 27707944941108842128347719)
      ·
        refine ⟨41561917411663263192521579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27707944941108842128347719 41561917411663263192521579)
        ·
          refine ⟨62342876117494894788782369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41561917411663263192521579 62342876117494894788782369)
          ·
            refine ⟨46757157088121171091586777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62342876117494894788782369 46757157088121171091586777)
            ·
              refine ⟨35067867816090878318690083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46757157088121171091586777 35067867816090878318690083)
              ·
                refine ⟨52601801724136317478035125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35067867816090878318690083 52601801724136317478035125)
                ·
                  refine ⟨4931418911637779763565793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52601801724136317478035125 4931418911637779763565793)
                  ·
                    refine ⟨3698564183728334822674345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4931418911637779763565793 3698564183728334822674345)
                    ·
                      refine ⟨2773923137796251117005759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3698564183728334822674345 2773923137796251117005759)
                      ·
                        rfl

theorem cell23_5402196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_5402196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402196 prefixEnd_5402196 := by exact prefixLift 5402196
  have htrace : WordTrace (prefixWord ++ tailWord_5402196) baseStart_5402196 baseEnd_5402196 := by
    simpa [prefixWord, tailWord_5402196, baseEnd_5402196] using wordTrace_append hprefix tailTrace_5402196
  have hstable : (prefixWord ++ tailWord_5402196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402196).length < 2 ^ (prefixWord ++ tailWord_5402196).sum := by decide
  have hdescent : baseEnd_5402196 < baseStart_5402196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402199 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 3]
def baseStart_5402199 : Nat := 118140960795 + 5402199 * 2 ^ 59
def prefixEnd_5402199 : Nat := 4983230072969 + 3 ^ 40 * 5402199 * 2
def baseEnd_5402199 : Nat := 2773924678238214605268245

theorem tailTrace_5402199 : CollatzResearch.WordTrace tailWord_5402199 prefixEnd_5402199 2773924678238214605268245 := by
  unfold tailWord_5402199
  simp only [CollatzResearch.WordTrace]
  refine ⟨197034384555763119980609651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131356256370508746653739767 197034384555763119980609651)
  ·
    refine ⟨295551576833644679970914477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197034384555763119980609651 295551576833644679970914477)
    ·
      refine ⟨110831841312616754989092929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295551576833644679970914477 110831841312616754989092929)
      ·
        refine ⟨83123880984462566241819697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110831841312616754989092929 83123880984462566241819697)
        ·
          refine ⟨62342910738346924681364773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83123880984462566241819697 62342910738346924681364773)
          ·
            refine ⟨11689295763440048377755895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62342910738346924681364773 11689295763440048377755895)
            ·
              refine ⟨17533943645160072566633843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11689295763440048377755895 17533943645160072566633843)
              ·
                refine ⟨26300915467740108849950765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17533943645160072566633843 26300915467740108849950765)
                ·
                  refine ⟨9862843300402540818731537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26300915467740108849950765 9862843300402540818731537)
                  ·
                    refine ⟨7397132475301905614048653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9862843300402540818731537 7397132475301905614048653)
                    ·
                      refine ⟨2773924678238214605268245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7397132475301905614048653 2773924678238214605268245)
                      ·
                        rfl

theorem cell23_5402199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_5402199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402199 prefixEnd_5402199 := by exact prefixLift 5402199
  have htrace : WordTrace (prefixWord ++ tailWord_5402199) baseStart_5402199 baseEnd_5402199 := by
    simpa [prefixWord, tailWord_5402199, baseEnd_5402199] using wordTrace_append hprefix tailTrace_5402199
  have hstable : (prefixWord ++ tailWord_5402199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402199).length < 2 ^ (prefixWord ++ tailWord_5402199).sum := by decide
  have hdescent : baseEnd_5402199 < baseStart_5402199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402216 : List Nat := [2, 1, 4, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_5402216 : Nat := 118140960795 + 5402216 * 2 ^ 59
def prefixEnd_5402216 : Nat := 4983230072969 + 3 ^ 40 * 5402216 * 2
def baseEnd_5402216 : Nat := 2773933407409341038755667

theorem tailTrace_5402216 : CollatzResearch.WordTrace tailWord_5402216 prefixEnd_5402216 2773933407409341038755667 := by
  unfold tailWord_5402216
  simp only [CollatzResearch.WordTrace]
  refine ⟨98517502298350765941989251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131356669731134354589319001 98517502298350765941989251)
  ·
    refine ⟨147776253447526148912983877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98517502298350765941989251 147776253447526148912983877)
    ·
      refine ⟨27708047521411152921184477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147776253447526148912983877 27708047521411152921184477)
      ·
        refine ⟨10390517820529182345444179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27708047521411152921184477 10390517820529182345444179)
        ·
          refine ⟨15585776730793773518166269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10390517820529182345444179 15585776730793773518166269)
          ·
            refine ⟨5844666274047665069312351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15585776730793773518166269 5844666274047665069312351)
            ·
              refine ⟨8766999411071497603968527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5844666274047665069312351 8766999411071497603968527)
              ·
                refine ⟨13150499116607246405952791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8766999411071497603968527 13150499116607246405952791)
                ·
                  refine ⟨19725748674910869608929187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13150499116607246405952791 19725748674910869608929187)
                  ·
                    refine ⟨29588623012366304413393781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19725748674910869608929187 29588623012366304413393781)
                    ·
                      refine ⟨2773933407409341038755667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29588623012366304413393781 2773933407409341038755667)
                      ·
                        rfl

theorem cell23_5402216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_5402216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402216 prefixEnd_5402216 := by exact prefixLift 5402216
  have htrace : WordTrace (prefixWord ++ tailWord_5402216) baseStart_5402216 baseEnd_5402216 := by
    simpa [prefixWord, tailWord_5402216, baseEnd_5402216] using wordTrace_append hprefix tailTrace_5402216
  have hstable : (prefixWord ++ tailWord_5402216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402216).length < 2 ^ (prefixWord ++ tailWord_5402216).sum := by decide
  have hdescent : baseEnd_5402216 < baseStart_5402216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402252 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 2, 3, 4]
def baseStart_5402252 : Nat := 118140960795 + 5402252 * 2 ^ 59
def prefixEnd_5402252 : Nat := 4983230072969 + 3 ^ 40 * 5402252 * 2
def baseEnd_5402252 : Nat := 2773951892712902897905501

theorem tailTrace_5402252 : CollatzResearch.WordTrace tailWord_5402252 prefixEnd_5402252 2773951892712902897905501 := by
  unfold tailWord_5402252
  simp only [CollatzResearch.WordTrace]
  refine ⟨98518158812285555016144505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131357545083047406688192673 98518158812285555016144505)
  ·
    refine ⟨73888619109214166262108379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98518158812285555016144505 73888619109214166262108379)
    ·
      refine ⟨110832928663821249393162569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73888619109214166262108379 110832928663821249393162569)
      ·
        refine ⟨83124696497865937044871927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110832928663821249393162569 83124696497865937044871927)
        ·
          refine ⟨124687044746798905567307891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83124696497865937044871927 124687044746798905567307891)
          ·
            refine ⟨187030567120198358350961837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124687044746798905567307891 187030567120198358350961837)
            ·
              refine ⟨70136462670074384381610689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187030567120198358350961837 70136462670074384381610689)
              ·
                refine ⟨52602347002555788286208017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70136462670074384381610689 52602347002555788286208017)
                ·
                  refine ⟨39451760251916841214656013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52602347002555788286208017 39451760251916841214656013)
                  ·
                    refine ⟨14794410094468815455496005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39451760251916841214656013 14794410094468815455496005)
                    ·
                      refine ⟨2773951892712902897905501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14794410094468815455496005 2773951892712902897905501)
                      ·
                        rfl

theorem cell23_5402252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_5402252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402252 prefixEnd_5402252 := by exact prefixLift 5402252
  have htrace : WordTrace (prefixWord ++ tailWord_5402252) baseStart_5402252 baseEnd_5402252 := by
    simpa [prefixWord, tailWord_5402252, baseEnd_5402252] using wordTrace_append hprefix tailTrace_5402252
  have hstable : (prefixWord ++ tailWord_5402252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402252).length < 2 ^ (prefixWord ++ tailWord_5402252).sum := by decide
  have hdescent : baseEnd_5402252 < baseStart_5402252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402273 : List Nat := [1, 2, 3, 3, 2, 2, 1, 3, 1, 3, 2]
def baseStart_5402273 : Nat := 118140960795 + 5402273 * 2 ^ 59
def prefixEnd_5402273 : Nat := 4983230072969 + 3 ^ 40 * 5402273 * 2
def baseEnd_5402273 : Nat := 2773962675806647315742905

theorem tailTrace_5402273 : CollatzResearch.WordTrace tailWord_5402273 prefixEnd_5402273 2773962675806647315742905 := by
  unfold tailWord_5402273
  simp only [CollatzResearch.WordTrace]
  refine ⟨197037083557495030618803473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131358055704996687079202315 197037083557495030618803473)
  ·
    refine ⟨147777812668121272964102605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197037083557495030618803473 147777812668121272964102605)
    ·
      refine ⟨55416679750545477361538477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147777812668121272964102605 55416679750545477361538477)
      ·
        refine ⟨20781254906454554010576929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55416679750545477361538477 20781254906454554010576929)
        ·
          refine ⟨15585941179840915507932697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20781254906454554010576929 15585941179840915507932697)
          ·
            refine ⟨11689455884880686630949523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15585941179840915507932697 11689455884880686630949523)
            ·
              refine ⟨17534183827321029946424285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11689455884880686630949523 17534183827321029946424285)
              ·
                refine ⟨6575318935245386229909107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17534183827321029946424285 6575318935245386229909107)
                ·
                  refine ⟨9862978402868079344863661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6575318935245386229909107 9862978402868079344863661)
                  ·
                    refine ⟨3698616901075529754323873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9862978402868079344863661 3698616901075529754323873)
                    ·
                      refine ⟨2773962675806647315742905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3698616901075529754323873 2773962675806647315742905)
                      ·
                        rfl

theorem cell23_5402273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_5402273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402273 prefixEnd_5402273 := by exact prefixLift 5402273
  have htrace : WordTrace (prefixWord ++ tailWord_5402273) baseStart_5402273 baseEnd_5402273 := by
    simpa [prefixWord, tailWord_5402273, baseEnd_5402273] using wordTrace_append hprefix tailTrace_5402273
  have hstable : (prefixWord ++ tailWord_5402273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402273).length < 2 ^ (prefixWord ++ tailWord_5402273).sum := by decide
  have hdescent : baseEnd_5402273 < baseStart_5402273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402343 : List Nat := [1, 1, 5, 4, 1, 2, 1, 1, 7]
def baseStart_5402343 : Nat := 118140960795 + 5402343 * 2 ^ 59
def prefixEnd_5402343 : Nat := 4983230072969 + 3 ^ 40 * 5402343 * 2
def baseEnd_5402343 : Nat := 308222068828051337985287

theorem tailTrace_5402343 : CollatzResearch.WordTrace tailWord_5402343 prefixEnd_5402343 308222068828051337985287 := by
  unfold tailWord_5402343
  simp only [CollatzResearch.WordTrace]
  refine ⟨197039636667241432573851683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131359757778160955049234455 197039636667241432573851683)
  ·
    refine ⟨295559455000862148860777525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197039636667241432573851683 295559455000862148860777525)
    ·
      refine ⟨27708698906330826455697893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 295559455000862148860777525 27708698906330826455697893)
      ·
        refine ⟨5195381044937029960443355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27708698906330826455697893 5195381044937029960443355)
        ·
          refine ⟨7793071567405544940665033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5195381044937029960443355 7793071567405544940665033)
          ·
            refine ⟨5844803675554158705498775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7793071567405544940665033 5844803675554158705498775)
            ·
              refine ⟨8767205513331238058248163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5844803675554158705498775 8767205513331238058248163)
              ·
                refine ⟨13150808269996857087372245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8767205513331238058248163 13150808269996857087372245)
                ·
                  refine ⟨308222068828051337985287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13150808269996857087372245 308222068828051337985287)
                  ·
                    rfl

theorem cell23_5402343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 7].length) (baseStart_5402343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402343 prefixEnd_5402343 := by exact prefixLift 5402343
  have htrace : WordTrace (prefixWord ++ tailWord_5402343) baseStart_5402343 baseEnd_5402343 := by
    simpa [prefixWord, tailWord_5402343, baseEnd_5402343] using wordTrace_append hprefix tailTrace_5402343
  have hstable : (prefixWord ++ tailWord_5402343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402343).length < 2 ^ (prefixWord ++ tailWord_5402343).sum := by decide
  have hdescent : baseEnd_5402343 < baseStart_5402343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402349 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_5402349 : Nat := 118140960795 + 5402349 * 2 ^ 59
def prefixEnd_5402349 : Nat := 4983230072969 + 3 ^ 40 * 5402349 * 2
def baseEnd_5402349 : Nat := 2774001700336389018392555

theorem tailTrace_5402349 : CollatzResearch.WordTrace tailWord_5402349 prefixEnd_5402349 2774001700336389018392555 := by
  unfold tailWord_5402349
  simp only [CollatzResearch.WordTrace]
  refine ⟨197039855505219695598570101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131359903670146463732380067 197039855505219695598570101)
  ·
    refine ⟨18472486453614346462365947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197039855505219695598570101 18472486453614346462365947)
    ·
      refine ⟨27708729680421519693548921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18472486453614346462365947 27708729680421519693548921)
      ·
        refine ⟨20781547260316139770161691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27708729680421519693548921 20781547260316139770161691)
        ·
          refine ⟨31172320890474209655242537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20781547260316139770161691 31172320890474209655242537)
          ·
            refine ⟨23379240667855657241431903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31172320890474209655242537 23379240667855657241431903)
            ·
              refine ⟨35068861001783485862147855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23379240667855657241431903 35068861001783485862147855)
              ·
                refine ⟨52603291502675228793221783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35068861001783485862147855 52603291502675228793221783)
                ·
                  refine ⟨78904937254012843189832675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52603291502675228793221783 78904937254012843189832675)
                  ·
                    refine ⟨118357405881019264784749013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78904937254012843189832675 118357405881019264784749013)
                    ·
                      refine ⟨2774001700336389018392555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118357405881019264784749013 2774001700336389018392555)
                      ·
                        rfl

theorem cell23_5402349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_5402349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402349 prefixEnd_5402349 := by exact prefixLift 5402349
  have htrace : WordTrace (prefixWord ++ tailWord_5402349) baseStart_5402349 baseEnd_5402349 := by
    simpa [prefixWord, tailWord_5402349, baseEnd_5402349] using wordTrace_append hprefix tailTrace_5402349
  have hstable : (prefixWord ++ tailWord_5402349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402349).length < 2 ^ (prefixWord ++ tailWord_5402349).sum := by decide
  have hdescent : baseEnd_5402349 < baseStart_5402349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402352 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 2, 8]
def baseStart_5402352 : Nat := 118140960795 + 5402352 * 2 ^ 59
def prefixEnd_5402352 : Nat := 4983230072969 + 3 ^ 40 * 5402352 * 2
def baseEnd_5402352 : Nat := 924667746926117502218347

theorem tailTrace_5402352 : CollatzResearch.WordTrace tailWord_5402352 prefixEnd_5402352 924667746926117502218347 := by
  unfold tailWord_5402352
  simp only [CollatzResearch.WordTrace]
  refine ⟨98519982462104413555464655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131359976616139218073952873 98519982462104413555464655)
  ·
    refine ⟨147779973693156620333196983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98519982462104413555464655 147779973693156620333196983)
    ·
      refine ⟨221669960539734930499795475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147779973693156620333196983 221669960539734930499795475)
      ·
        refine ⟨332504940809602395749693213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221669960539734930499795475 332504940809602395749693213)
        ·
          refine ⟨124689352803600898406134955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332504940809602395749693213 124689352803600898406134955)
          ·
            refine ⟨187034029205401347609202433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124689352803600898406134955 187034029205401347609202433)
            ·
              refine ⟨140275521904051010706901825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187034029205401347609202433 140275521904051010706901825)
              ·
                refine ⟨105206641428038258030176369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140275521904051010706901825 105206641428038258030176369)
                ·
                  refine ⟨78904981071028693522632277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105206641428038258030176369 78904981071028693522632277)
                  ·
                    refine ⟨924667746926117502218347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78904981071028693522632277 924667746926117502218347)
                    ·
                      rfl

theorem cell23_5402352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 8].length) (baseStart_5402352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402352 prefixEnd_5402352 := by exact prefixLift 5402352
  have htrace : WordTrace (prefixWord ++ tailWord_5402352) baseStart_5402352 baseEnd_5402352 := by
    simpa [prefixWord, tailWord_5402352, baseEnd_5402352] using wordTrace_append hprefix tailTrace_5402352
  have hstable : (prefixWord ++ tailWord_5402352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402352).length < 2 ^ (prefixWord ++ tailWord_5402352).sum := by decide
  have hdescent : baseEnd_5402352 < baseStart_5402352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402376 : List Nat := [2, 1, 3, 2, 2, 1, 4, 1, 2, 1, 4]
def baseStart_5402376 : Nat := 118140960795 + 5402376 * 2 ^ 59
def prefixEnd_5402376 : Nat := 4983230072969 + 3 ^ 40 * 5402376 * 2
def baseEnd_5402376 : Nat := 2774015564314060412754931

theorem tailTrace_5402376 : CollatzResearch.WordTrace tailWord_5402376 prefixEnd_5402376 2774015564314060412754931 := by
  unfold tailWord_5402376
  simp only [CollatzResearch.WordTrace]
  refine ⟨98520420138060939604901491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131360560184081252806535321 98520420138060939604901491)
  ·
    refine ⟨147780630207091409407352237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98520420138060939604901491 147780630207091409407352237)
    ·
      refine ⟨55417736327659278527757089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147780630207091409407352237 55417736327659278527757089)
      ·
        refine ⟨41563302245744458895817817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55417736327659278527757089 41563302245744458895817817)
        ·
          refine ⟨31172476684308344171863363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41563302245744458895817817 31172476684308344171863363)
          ·
            refine ⟨46758715026462516257795045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31172476684308344171863363 46758715026462516257795045)
            ·
              refine ⟨8767259067461721798336571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46758715026462516257795045 8767259067461721798336571)
              ·
                refine ⟨13150888601192582697504857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8767259067461721798336571 13150888601192582697504857)
                ·
                  refine ⟨9863166450894437023128643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13150888601192582697504857 9863166450894437023128643)
                  ·
                    refine ⟨14794749676341655534692965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9863166450894437023128643 14794749676341655534692965)
                    ·
                      refine ⟨2774015564314060412754931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14794749676341655534692965 2774015564314060412754931)
                      ·
                        rfl

theorem cell23_5402376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_5402376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402376 prefixEnd_5402376 := by exact prefixLift 5402376
  have htrace : WordTrace (prefixWord ++ tailWord_5402376) baseStart_5402376 baseEnd_5402376 := by
    simpa [prefixWord, tailWord_5402376, baseEnd_5402376] using wordTrace_append hprefix tailTrace_5402376
  have hstable : (prefixWord ++ tailWord_5402376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402376).length < 2 ^ (prefixWord ++ tailWord_5402376).sum := by decide
  have hdescent : baseEnd_5402376 < baseStart_5402376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402379 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 3]
def baseStart_5402379 : Nat := 118140960795 + 5402379 * 2 ^ 59
def prefixEnd_5402379 : Nat := 4983230072969 + 3 ^ 40 * 5402379 * 2
def baseEnd_5402379 : Nat := 2774017104756023901017417

theorem tailTrace_5402379 : CollatzResearch.WordTrace tailWord_5402379 prefixEnd_5402379 2774017104756023901017417 := by
  unfold tailWord_5402379
  simp only [CollatzResearch.WordTrace]
  refine ⟨197040949695111010722162191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131360633130074007148108127 197040949695111010722162191)
  ·
    refine ⟨295561424542666516083243287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197040949695111010722162191 295561424542666516083243287)
    ·
      refine ⟨443342136813999774124864931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295561424542666516083243287 443342136813999774124864931)
      ·
        refine ⟨665013205220999661187297397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443342136813999774124864931 665013205220999661187297397)
        ·
          refine ⟨62344987989468718236309131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 665013205220999661187297397 62344987989468718236309131)
          ·
            refine ⟨93517481984203077354463697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62344987989468718236309131 93517481984203077354463697)
            ·
              refine ⟨70138111488152308015847773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93517481984203077354463697 70138111488152308015847773)
              ·
                refine ⟨26301791808057115505942915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70138111488152308015847773 26301791808057115505942915)
                ·
                  refine ⟨39452687712085673258914373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26301791808057115505942915 39452687712085673258914373)
                  ·
                    refine ⟨7397378946016063736046445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39452687712085673258914373 7397378946016063736046445)
                    ·
                      refine ⟨2774017104756023901017417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7397378946016063736046445 2774017104756023901017417)
                      ·
                        rfl

theorem cell23_5402379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 3].length) (baseStart_5402379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402379 prefixEnd_5402379 := by exact prefixLift 5402379
  have htrace : WordTrace (prefixWord ++ tailWord_5402379) baseStart_5402379 baseEnd_5402379 := by
    simpa [prefixWord, tailWord_5402379, baseEnd_5402379] using wordTrace_append hprefix tailTrace_5402379
  have hstable : (prefixWord ++ tailWord_5402379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402379).length < 2 ^ (prefixWord ++ tailWord_5402379).sum := by decide
  have hdescent : baseEnd_5402379 < baseStart_5402379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402396 : List Nat := [2, 2, 3, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_5402396 : Nat := 118140960795 + 5402396 * 2 ^ 59
def prefixEnd_5402396 : Nat := 4983230072969 + 3 ^ 40 * 5402396 * 2
def baseEnd_5402396 : Nat := 2774025833927150334504839

theorem tailTrace_5402396 : CollatzResearch.WordTrace tailWord_5402396 prefixEnd_5402396 2774025833927150334504839 := by
  unfold tailWord_5402396
  simp only [CollatzResearch.WordTrace]
  refine ⟨98520784868024711312765521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131361046490699615083687361 98520784868024711312765521)
  ·
    refine ⟨73890588651018533484574141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98520784868024711312765521 73890588651018533484574141)
    ·
      refine ⟨27708970744131950056715303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73890588651018533484574141 27708970744131950056715303)
      ·
        refine ⟨41563456116197925085072955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27708970744131950056715303 41563456116197925085072955)
        ·
          refine ⟨62345184174296887627609433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41563456116197925085072955 62345184174296887627609433)
          ·
            refine ⟨46758888130722665720707075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62345184174296887627609433 46758888130722665720707075)
            ·
              refine ⟨70138332196083998581060613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46758888130722665720707075 70138332196083998581060613)
              ·
                refine ⟨13150937286765749733948865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70138332196083998581060613 13150937286765749733948865)
                ·
                  refine ⟨9863202965074312300461649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13150937286765749733948865 9863202965074312300461649)
                  ·
                    refine ⟨7397402223805734225346237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9863202965074312300461649 7397402223805734225346237)
                    ·
                      refine ⟨2774025833927150334504839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7397402223805734225346237 2774025833927150334504839)
                      ·
                        rfl

theorem cell23_5402396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_5402396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402396 prefixEnd_5402396 := by exact prefixLift 5402396
  have htrace : WordTrace (prefixWord ++ tailWord_5402396) baseStart_5402396 baseEnd_5402396 := by
    simpa [prefixWord, tailWord_5402396, baseEnd_5402396] using wordTrace_append hprefix tailTrace_5402396
  have hstable : (prefixWord ++ tailWord_5402396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402396).length < 2 ^ (prefixWord ++ tailWord_5402396).sum := by decide
  have hdescent : baseEnd_5402396 < baseStart_5402396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402430 : List Nat := [4, 2, 1, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_5402430 : Nat := 118140960795 + 5402430 * 2 ^ 59
def prefixEnd_5402430 : Nat := 4983230072969 + 3 ^ 40 * 5402430 * 2
def baseEnd_5402430 : Nat := 2774043292269403201479683

theorem tailTrace_5402430 : CollatzResearch.WordTrace tailWord_5402430 prefixEnd_5402430 2774043292269403201479683 := by
  unfold tailWord_5402430
  simp only [CollatzResearch.WordTrace]
  refine ⟨24630351227240780804033593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131361873211950830954845829 24630351227240780804033593)
  ·
    refine ⟨18472763420430585603025195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24630351227240780804033593 18472763420430585603025195)
    ·
      refine ⟨27709145130645878404537793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18472763420430585603025195 27709145130645878404537793)
      ·
        refine ⟨20781858847984408803403345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27709145130645878404537793 20781858847984408803403345)
        ·
          refine ⟨15586394135988306602552509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20781858847984408803403345 15586394135988306602552509)
          ·
            refine ⟨5844897800995614975957191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15586394135988306602552509 5844897800995614975957191)
            ·
              refine ⟨8767346701493422463935787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5844897800995614975957191 8767346701493422463935787)
              ·
                refine ⟨13151020052240133695903681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8767346701493422463935787 13151020052240133695903681)
                ·
                  refine ⟨9863265039180100271927761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13151020052240133695903681 9863265039180100271927761)
                  ·
                    refine ⟨7397448779385075203945821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9863265039180100271927761 7397448779385075203945821)
                    ·
                      refine ⟨2774043292269403201479683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7397448779385075203945821 2774043292269403201479683)
                      ·
                        rfl

theorem cell23_5402430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_5402430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402430 prefixEnd_5402430 := by exact prefixLift 5402430
  have htrace : WordTrace (prefixWord ++ tailWord_5402430) baseStart_5402430 baseEnd_5402430 := by
    simpa [prefixWord, tailWord_5402430, baseEnd_5402430] using wordTrace_append hprefix tailTrace_5402430
  have hstable : (prefixWord ++ tailWord_5402430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402430).length < 2 ^ (prefixWord ++ tailWord_5402430).sum := by decide
  have hdescent : baseEnd_5402430 < baseStart_5402430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402476 : List Nat := [2, 2, 1, 1, 4, 2, 3, 1, 1, 6]
def baseStart_5402476 : Nat := 118140960795 + 5402476 * 2 ^ 59
def prefixEnd_5402476 : Nat := 4983230072969 + 3 ^ 40 * 5402476 * 2
def baseEnd_5402476 : Nat := 924688970793170007168157

theorem tailTrace_5402476 : CollatzResearch.WordTrace tailWord_5402476 prefixEnd_5402476 924688970793170007168157 := by
  unfold tailWord_5402476
  simp only [CollatzResearch.WordTrace]
  refine ⟨98522243787879798144221641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131362991717173064192295521 98522243787879798144221641)
  ·
    refine ⟨73891682840909848608166231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98522243787879798144221641 73891682840909848608166231)
    ·
      refine ⟨110837524261364772912249347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73891682840909848608166231 110837524261364772912249347)
      ·
        refine ⟨166256286392047159368374021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110837524261364772912249347 166256286392047159368374021)
        ·
          refine ⟨31173053698508842381570129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166256286392047159368374021 31173053698508842381570129)
          ·
            refine ⟨23379790273881631786177597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31173053698508842381570129 23379790273881631786177597)
            ·
              refine ⟨8767421352705611919816599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23379790273881631786177597 8767421352705611919816599)
              ·
                refine ⟨13151132029058417879724899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8767421352705611919816599 13151132029058417879724899)
                ·
                  refine ⟨19726698043587626819587349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13151132029058417879724899 19726698043587626819587349)
                  ·
                    refine ⟨924688970793170007168157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19726698043587626819587349 924688970793170007168157)
                    ·
                      rfl

theorem cell23_5402476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_5402476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402476 prefixEnd_5402476 := by exact prefixLift 5402476
  have htrace : WordTrace (prefixWord ++ tailWord_5402476) baseStart_5402476 baseEnd_5402476 := by
    simpa [prefixWord, tailWord_5402476, baseEnd_5402476] using wordTrace_append hprefix tailTrace_5402476
  have hstable : (prefixWord ++ tailWord_5402476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402476).length < 2 ^ (prefixWord ++ tailWord_5402476).sum := by decide
  have hdescent : baseEnd_5402476 < baseStart_5402476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402489 : List Nat := [1, 2, 1, 3, 2, 2, 3, 9]
def baseStart_5402489 : Nat := 118140960795 + 5402489 * 2 ^ 59
def prefixEnd_5402489 : Nat := 4983230072969 + 3 ^ 40 * 5402489 * 2
def baseEnd_5402489 : Nat := 102743466208445128542293

theorem tailTrace_5402489 : CollatzResearch.WordTrace tailWord_5402489 prefixEnd_5402489 102743466208445128542293 := by
  unfold tailWord_5402489
  simp only [CollatzResearch.WordTrace]
  refine ⟨197044961724712499508666521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131363307816474999672444347 197044961724712499508666521)
  ·
    refine ⟨147783721293534374631499891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197044961724712499508666521 147783721293534374631499891)
    ·
      refine ⟨221675581940301561947249837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147783721293534374631499891 221675581940301561947249837)
      ·
        refine ⟨83128343227613085730218689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221675581940301561947249837 83128343227613085730218689)
        ·
          refine ⟨62346257420709814297664017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83128343227613085730218689 62346257420709814297664017)
          ·
            refine ⟨46759693065532360723248013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62346257420709814297664017 46759693065532360723248013)
            ·
              refine ⟨17534884899574635271218005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46759693065532360723248013 17534884899574635271218005)
              ·
                refine ⟨102743466208445128542293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17534884899574635271218005 102743466208445128542293)
                ·
                  rfl

theorem cell23_5402489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 9].length) (baseStart_5402489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402489 prefixEnd_5402489 := by exact prefixLift 5402489
  have htrace : WordTrace (prefixWord ++ tailWord_5402489) baseStart_5402489 baseEnd_5402489 := by
    simpa [prefixWord, tailWord_5402489, baseEnd_5402489] using wordTrace_append hprefix tailTrace_5402489
  have hstable : (prefixWord ++ tailWord_5402489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402489).length < 2 ^ (prefixWord ++ tailWord_5402489).sum := by decide
  have hdescent : baseEnd_5402489 < baseStart_5402489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402494 : List Nat := [4, 2, 3, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_5402494 : Nat := 118140960795 + 5402494 * 2 ^ 59
def prefixEnd_5402494 : Nat := 4983230072969 + 3 ^ 40 * 5402494 * 2
def baseEnd_5402494 : Nat := 2774076155031290951079389

theorem tailTrace_5402494 : CollatzResearch.WordTrace tailWord_5402494 prefixEnd_5402494 2774076155031290951079389 := by
  unfold tailWord_5402494
  simp only [CollatzResearch.WordTrace]
  refine ⟨24630643011211798170324817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131363429393129590241732357 24630643011211798170324817)
  ·
    refine ⟨18472982258408848627743613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24630643011211798170324817 18472982258408848627743613)
    ·
      refine ⟨6927368346903318235403855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18472982258408848627743613 6927368346903318235403855)
      ·
        refine ⟨10391052520354977353105783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6927368346903318235403855 10391052520354977353105783)
        ·
          refine ⟨15586578780532466029658675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10391052520354977353105783 15586578780532466029658675)
          ·
            refine ⟨23379868170798699044488013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15586578780532466029658675 23379868170798699044488013)
            ·
              refine ⟨8767450564049512141683005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23379868170798699044488013 8767450564049512141683005)
              ·
                refine ⟨3287793961518567053131127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8767450564049512141683005 3287793961518567053131127)
                ·
                  refine ⟨4931690942277850579696691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3287793961518567053131127 4931690942277850579696691)
                  ·
                    refine ⟨7397536413416775869545037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4931690942277850579696691 7397536413416775869545037)
                    ·
                      refine ⟨2774076155031290951079389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7397536413416775869545037 2774076155031290951079389)
                      ·
                        rfl

theorem cell23_5402494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_5402494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402494 prefixEnd_5402494 := by exact prefixLift 5402494
  have htrace : WordTrace (prefixWord ++ tailWord_5402494) baseStart_5402494 baseEnd_5402494 := by
    simpa [prefixWord, tailWord_5402494, baseEnd_5402494] using wordTrace_append hprefix tailTrace_5402494
  have hstable : (prefixWord ++ tailWord_5402494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402494).length < 2 ^ (prefixWord ++ tailWord_5402494).sum := by decide
  have hdescent : baseEnd_5402494 < baseStart_5402494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402503 : List Nat := [1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 5]
def baseStart_5402503 : Nat := 118140960795 + 5402503 * 2 ^ 59
def prefixEnd_5402503 : Nat := 4983230072969 + 3 ^ 40 * 5402503 * 2
def baseEnd_5402503 : Nat := 2774080776357181415866847

theorem tailTrace_5402503 : CollatzResearch.WordTrace tailWord_5402503 prefixEnd_5402503 2774080776357181415866847 := by
  unfold tailWord_5402503
  simp only [CollatzResearch.WordTrace]
  refine ⟨197045472346661779899676163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131363648231107853266450775 197045472346661779899676163)
  ·
    refine ⟨295568208519992669849514245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197045472346661779899676163 295568208519992669849514245)
    ·
      refine ⟨55419039097498625596783921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 295568208519992669849514245 55419039097498625596783921)
      ·
        refine ⟨41564279323123969197587941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55419039097498625596783921 41564279323123969197587941)
        ·
          refine ⟨7793302373085744224547739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41564279323123969197587941 7793302373085744224547739)
          ·
            refine ⟨11689953559628616336821609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7793302373085744224547739 11689953559628616336821609)
            ·
              refine ⟨8767465169721462252616207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11689953559628616336821609 8767465169721462252616207)
              ·
                refine ⟨13151197754582193378924311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8767465169721462252616207 13151197754582193378924311)
                ·
                  refine ⟨19726796631873290068386467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13151197754582193378924311 19726796631873290068386467)
                  ·
                    refine ⟨29590194947809935102579701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19726796631873290068386467 29590194947809935102579701)
                    ·
                      refine ⟨2774080776357181415866847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29590194947809935102579701 2774080776357181415866847)
                      ·
                        rfl

theorem cell23_5402503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_5402503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402503 prefixEnd_5402503 := by exact prefixLift 5402503
  have htrace : WordTrace (prefixWord ++ tailWord_5402503) baseStart_5402503 baseEnd_5402503 := by
    simpa [prefixWord, tailWord_5402503, baseEnd_5402503] using wordTrace_append hprefix tailTrace_5402503
  have hstable : (prefixWord ++ tailWord_5402503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402503).length < 2 ^ (prefixWord ++ tailWord_5402503).sum := by decide
  have hdescent : baseEnd_5402503 < baseStart_5402503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402527 : List Nat := [1, 1, 2, 5, 3, 2, 2, 1, 2, 4]
def baseStart_5402527 : Nat := 118140960795 + 5402527 * 2 ^ 59
def prefixEnd_5402527 : Nat := 4983230072969 + 3 ^ 40 * 5402527 * 2
def baseEnd_5402527 : Nat := 924697699964296440655579

theorem tailTrace_5402527 : CollatzResearch.WordTrace tailWord_5402527 prefixEnd_5402527 924697699964296440655579 := by
  unfold tailWord_5402527
  simp only [CollatzResearch.WordTrace]
  refine ⟨197046347698574831998549835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131364231799049887999033223 197046347698574831998549835)
  ·
    refine ⟨295569521547862247997824753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197046347698574831998549835 295569521547862247997824753)
    ·
      refine ⟨221677141160896685998368565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295569521547862247997824753 221677141160896685998368565)
      ·
        refine ⟨20782231983834064312347053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 221677141160896685998368565 20782231983834064312347053)
        ·
          refine ⟨7793336993937774117130145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20782231983834064312347053 7793336993937774117130145)
          ·
            refine ⟨5845002745453330587847609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7793336993937774117130145 5845002745453330587847609)
            ·
              refine ⟨4383752059089997940885707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5845002745453330587847609 4383752059089997940885707)
              ·
                refine ⟨6575628088634996911328561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4383752059089997940885707 6575628088634996911328561)
                ·
                  refine ⟨4931721066476247683496421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6575628088634996911328561 4931721066476247683496421)
                  ·
                    refine ⟨924697699964296440655579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4931721066476247683496421 924697699964296440655579)
                    ·
                      rfl

theorem cell23_5402527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 2, 4].length) (baseStart_5402527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402527 prefixEnd_5402527 := by exact prefixLift 5402527
  have htrace : WordTrace (prefixWord ++ tailWord_5402527) baseStart_5402527 baseEnd_5402527 := by
    simpa [prefixWord, tailWord_5402527, baseEnd_5402527] using wordTrace_append hprefix tailTrace_5402527
  have hstable : (prefixWord ++ tailWord_5402527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402527).length < 2 ^ (prefixWord ++ tailWord_5402527).sum := by decide
  have hdescent : baseEnd_5402527 < baseStart_5402527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402543 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 3, 3, 2]
def baseStart_5402543 : Nat := 118140960795 + 5402543 * 2 ^ 59
def prefixEnd_5402543 : Nat := 4983230072969 + 3 ^ 40 * 5402543 * 2
def baseEnd_5402543 : Nat := 2774101315583361259366663

theorem tailTrace_5402543 : CollatzResearch.WordTrace tailWord_5402543 prefixEnd_5402543 2774101315583361259366663 := by
  unfold tailWord_5402543
  simp only [CollatzResearch.WordTrace]
  refine ⟨197046931266516866731132283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131364620844344577820754855 197046931266516866731132283)
  ·
    refine ⟨295570396899775300096698425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197046931266516866731132283 295570396899775300096698425)
    ·
      refine ⟨221677797674831475072523819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295570396899775300096698425 221677797674831475072523819)
      ·
        refine ⟨332516696512247212608785729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221677797674831475072523819 332516696512247212608785729)
        ·
          refine ⟨249387522384185409456589297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332516696512247212608785729 249387522384185409456589297)
          ·
            refine ⟨187040641788139057092441973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249387522384185409456589297 187040641788139057092441973)
            ·
              refine ⟨17535060167638036602416435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 187040641788139057092441973 17535060167638036602416435)
              ·
                refine ⟨26302590251457054903624653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17535060167638036602416435 26302590251457054903624653)
                ·
                  refine ⟨9863471344296395588859245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26302590251457054903624653 9863471344296395588859245)
                  ·
                    refine ⟨3698801754111148345822217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9863471344296395588859245 3698801754111148345822217)
                    ·
                      refine ⟨2774101315583361259366663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3698801754111148345822217 2774101315583361259366663)
                      ·
                        rfl

theorem cell23_5402543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 3, 2].length) (baseStart_5402543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402543 prefixEnd_5402543 := by exact prefixLift 5402543
  have htrace : WordTrace (prefixWord ++ tailWord_5402543) baseStart_5402543 baseEnd_5402543 := by
    simpa [prefixWord, tailWord_5402543, baseEnd_5402543] using wordTrace_append hprefix tailTrace_5402543
  have hstable : (prefixWord ++ tailWord_5402543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402543).length < 2 ^ (prefixWord ++ tailWord_5402543).sum := by decide
  have hdescent : baseEnd_5402543 < baseStart_5402543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402576 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 3]
def baseStart_5402576 : Nat := 118140960795 + 5402576 * 2 ^ 59
def prefixEnd_5402576 : Nat := 4983230072969 + 3 ^ 40 * 5402576 * 2
def baseEnd_5402576 : Nat := 2774118260444959630254011

theorem tailTrace_5402576 : CollatzResearch.WordTrace tailWord_5402576 prefixEnd_5402576 2774118260444959630254011 := by
  unfold tailWord_5402576
  simp only [CollatzResearch.WordTrace]
  refine ⟨98524067437698656683541791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131365423250264875578055721 98524067437698656683541791)
  ·
    refine ⟨147786101156547985025312687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98524067437698656683541791 147786101156547985025312687)
    ·
      refine ⟨221679151734821977537969031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147786101156547985025312687 221679151734821977537969031)
      ·
        refine ⟨332518727602232966306953547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221679151734821977537969031 332518727602232966306953547)
        ·
          refine ⟨498778091403349449460430321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332518727602232966306953547 498778091403349449460430321)
          ·
            refine ⟨374083568552512087095322741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 498778091403349449460430321 374083568552512087095322741)
            ·
              refine ⟨35070334551798008165186507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 374083568552512087095322741 35070334551798008165186507)
              ·
                refine ⟨52605501827697012247779761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35070334551798008165186507 52605501827697012247779761)
                ·
                  refine ⟨39454126370772759185834821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52605501827697012247779761 39454126370772759185834821)
                  ·
                    refine ⟨7397648694519892347344029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39454126370772759185834821 7397648694519892347344029)
                    ·
                      refine ⟨2774118260444959630254011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7397648694519892347344029 2774118260444959630254011)
                      ·
                        rfl

theorem cell23_5402576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 3].length) (baseStart_5402576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402576 prefixEnd_5402576 := by exact prefixLift 5402576
  have htrace : WordTrace (prefixWord ++ tailWord_5402576) baseStart_5402576 baseEnd_5402576 := by
    simpa [prefixWord, tailWord_5402576, baseEnd_5402576] using wordTrace_append hprefix tailTrace_5402576
  have hstable : (prefixWord ++ tailWord_5402576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402576).length < 2 ^ (prefixWord ++ tailWord_5402576).sum := by decide
  have hdescent : baseEnd_5402576 < baseStart_5402576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402596 : List Nat := [2, 3, 1, 1, 1, 1, 5, 2, 7]
def baseStart_5402596 : Nat := 118140960795 + 5402596 * 2 ^ 59
def prefixEnd_5402596 : Nat := 4983230072969 + 3 ^ 40 * 5402596 * 2
def baseEnd_5402596 : Nat := 308236503339783283555991

theorem tailTrace_5402596 : CollatzResearch.WordTrace tailWord_5402596 prefixEnd_5402596 308236503339783283555991 := by
  unfold tailWord_5402596
  simp only [CollatzResearch.WordTrace]
  refine ⟨98524432167662428391405821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131365909556883237855207761 98524432167662428391405821)
  ·
    refine ⟨36946662062873410646777183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98524432167662428391405821 36946662062873410646777183)
    ·
      refine ⟨55419993094310115970165775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36946662062873410646777183 55419993094310115970165775)
      ·
        refine ⟨83129989641465173955248663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55419993094310115970165775 83129989641465173955248663)
        ·
          refine ⟨124694984462197760932872995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83129989641465173955248663 124694984462197760932872995)
          ·
            refine ⟨187042476693296641399309493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124694984462197760932872995 187042476693296641399309493)
            ·
              refine ⟨17535232189996560131185265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 187042476693296641399309493 17535232189996560131185265)
              ·
                refine ⟨13151424142497420098388949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17535232189996560131185265 13151424142497420098388949)
                ·
                  refine ⟨308236503339783283555991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13151424142497420098388949 308236503339783283555991)
                  ·
                    rfl

theorem cell23_5402596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_5402596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402596 prefixEnd_5402596 := by exact prefixLift 5402596
  have htrace : WordTrace (prefixWord ++ tailWord_5402596) baseStart_5402596 baseEnd_5402596 := by
    simpa [prefixWord, tailWord_5402596, baseEnd_5402596] using wordTrace_append hprefix tailTrace_5402596
  have hstable : (prefixWord ++ tailWord_5402596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402596).length < 2 ^ (prefixWord ++ tailWord_5402596).sum := by decide
  have hdescent : baseEnd_5402596 < baseStart_5402596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402636 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 1, 1, 7]
def baseStart_5402636 : Nat := 118140960795 + 5402636 * 2 ^ 59
def prefixEnd_5402636 : Nat := 4983230072969 + 3 ^ 40 * 5402636 * 2
def baseEnd_5402636 : Nat := 2774149069284229395503735

theorem tailTrace_5402636 : CollatzResearch.WordTrace tailWord_5402636 prefixEnd_5402636 2774149069284229395503735 := by
  unfold tailWord_5402636
  simp only [CollatzResearch.WordTrace]
  refine ⟨98525161627589971807133881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131366882170119962409511841 98525161627589971807133881)
  ·
    refine ⟨73893871220692478855350411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98525161627589971807133881 73893871220692478855350411)
    ·
      refine ⟨110840806831038718283025617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73893871220692478855350411 110840806831038718283025617)
      ·
        refine ⟨83130605123279038712269213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110840806831038718283025617 83130605123279038712269213)
        ·
          refine ⟨31173976921229639517100955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83130605123279038712269213 31173976921229639517100955)
          ·
            refine ⟨46760965381844459275651433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31173976921229639517100955 46760965381844459275651433)
            ·
              refine ⟨35070724036383344456738575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46760965381844459275651433 35070724036383344456738575)
              ·
                refine ⟨52606086054575016685107863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35070724036383344456738575 52606086054575016685107863)
                ·
                  refine ⟨78909129081862525027661795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52606086054575016685107863 78909129081862525027661795)
                  ·
                    refine ⟨118363693622793787541492693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78909129081862525027661795 118363693622793787541492693)
                    ·
                      refine ⟨2774149069284229395503735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118363693622793787541492693 2774149069284229395503735)
                      ·
                        rfl

theorem cell23_5402636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_5402636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402636 prefixEnd_5402636 := by exact prefixLift 5402636
  have htrace : WordTrace (prefixWord ++ tailWord_5402636) baseStart_5402636 baseEnd_5402636 := by
    simpa [prefixWord, tailWord_5402636, baseEnd_5402636] using wordTrace_append hprefix tailTrace_5402636
  have hstable : (prefixWord ++ tailWord_5402636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402636).length < 2 ^ (prefixWord ++ tailWord_5402636).sum := by decide
  have hdescent : baseEnd_5402636 < baseStart_5402636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402664 : List Nat := [2, 1, 5, 3, 1, 2, 1, 3, 5]
def baseStart_5402664 : Nat := 118140960795 + 5402664 * 2 ^ 59
def prefixEnd_5402664 : Nat := 4983230072969 + 3 ^ 40 * 5402664 * 2
def baseEnd_5402664 : Nat := 308240382971395031772623

theorem tailTrace_5402664 : CollatzResearch.WordTrace tailWord_5402664 prefixEnd_5402664 308240382971395031772623 := by
  unfold tailWord_5402664
  simp only [CollatzResearch.WordTrace]
  refine ⟨98525672249539252198143523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131367562999385669597524697 98525672249539252198143523)
  ·
    refine ⟨147788508374308878297215285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98525672249539252198143523 147788508374308878297215285)
    ·
      refine ⟨13855172660091457340363933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147788508374308878297215285 13855172660091457340363933)
      ·
        refine ⟨5195689747534296502636475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13855172660091457340363933 5195689747534296502636475)
        ·
          refine ⟨7793534621301444753954713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5195689747534296502636475 7793534621301444753954713)
          ·
            refine ⟨5845150965976083565466035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7793534621301444753954713 5845150965976083565466035)
            ·
              refine ⟨8767726448964125348199053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5845150965976083565466035 8767726448964125348199053)
              ·
                refine ⟨3287897418361547005574645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8767726448964125348199053 3287897418361547005574645)
                ·
                  refine ⟨308240382971395031772623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3287897418361547005574645 308240382971395031772623)
                  ·
                    rfl

theorem cell23_5402664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 5].length) (baseStart_5402664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402664 prefixEnd_5402664 := by exact prefixLift 5402664
  have htrace : WordTrace (prefixWord ++ tailWord_5402664) baseStart_5402664 baseEnd_5402664 := by
    simpa [prefixWord, tailWord_5402664, baseEnd_5402664] using wordTrace_append hprefix tailTrace_5402664
  have hstable : (prefixWord ++ tailWord_5402664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402664).length < 2 ^ (prefixWord ++ tailWord_5402664).sum := by decide
  have hdescent : baseEnd_5402664 < baseStart_5402664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402680 : List Nat := [2, 1, 2, 1, 6, 1, 1, 2, 2, 1, 4]
def baseStart_5402680 : Nat := 118140960795 + 5402680 * 2 ^ 59
def prefixEnd_5402680 : Nat := 4983230072969 + 3 ^ 40 * 5402680 * 2
def baseEnd_5402680 : Nat := 2774171662433027223353533

theorem tailTrace_5402680 : CollatzResearch.WordTrace tailWord_5402680 prefixEnd_5402680 2774171662433027223353533 := by
  unfold tailWord_5402680
  simp only [CollatzResearch.WordTrace]
  refine ⟨98525964033510269564434747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131367952044680359419246329 98525964033510269564434747)
  ·
    refine ⟨147788946050265404346652121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98525964033510269564434747 147788946050265404346652121)
    ·
      refine ⟨110841709537699053259989091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147788946050265404346652121 110841709537699053259989091)
      ·
        refine ⟨166262564306548579889983637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110841709537699053259989091 166262564306548579889983637)
        ·
          refine ⟨7793557701869464682342983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 166262564306548579889983637 7793557701869464682342983)
          ·
            refine ⟨11690336552804197023514475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7793557701869464682342983 11690336552804197023514475)
            ·
              refine ⟨17535504829206295535271713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11690336552804197023514475 17535504829206295535271713)
              ·
                refine ⟨13151628621904721651453785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17535504829206295535271713 13151628621904721651453785)
                ·
                  refine ⟨9863721466428541238590339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13151628621904721651453785 9863721466428541238590339)
                  ·
                    refine ⟨14795582199642811857885509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9863721466428541238590339 14795582199642811857885509)
                    ·
                      refine ⟨2774171662433027223353533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14795582199642811857885509 2774171662433027223353533)
                      ·
                        rfl

theorem cell23_5402680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_5402680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402680 prefixEnd_5402680 := by exact prefixLift 5402680
  have htrace : WordTrace (prefixWord ++ tailWord_5402680) baseStart_5402680 baseEnd_5402680 := by
    simpa [prefixWord, tailWord_5402680, baseEnd_5402680] using wordTrace_append hprefix tailTrace_5402680
  have hstable : (prefixWord ++ tailWord_5402680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402680).length < 2 ^ (prefixWord ++ tailWord_5402680).sum := by decide
  have hdescent : baseEnd_5402680 < baseStart_5402680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402683 : List Nat := [1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 3]
def baseStart_5402683 : Nat := 118140960795 + 5402683 * 2 ^ 59
def prefixEnd_5402683 : Nat := 4983230072969 + 3 ^ 40 * 5402683 * 2
def baseEnd_5402683 : Nat := 2774173202874990711616019

theorem tailTrace_5402683 : CollatzResearch.WordTrace tailWord_5402683 prefixEnd_5402683 2774173202874990711616019 := by
  unfold tailWord_5402683
  simp only [CollatzResearch.WordTrace]
  refine ⟨197052037486009670641228703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131368024990673113760819135 197052037486009670641228703)
  ·
    refine ⟨295578056229014505961843055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197052037486009670641228703 295578056229014505961843055)
    ·
      refine ⟨443367084343521758942764583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295578056229014505961843055 443367084343521758942764583)
      ·
        refine ⟨665050626515282638414146875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443367084343521758942764583 665050626515282638414146875)
        ·
          refine ⟨997575939772923957621220313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 665050626515282638414146875 997575939772923957621220313)
          ·
            refine ⟨748181954829692968215915235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 997575939772923957621220313 748181954829692968215915235)
            ·
              refine ⟨1122272932244539452323872853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748181954829692968215915235 1122272932244539452323872853)
              ·
                refine ⟨13151635924740696706920385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1122272932244539452323872853 13151635924740696706920385)
                ·
                  refine ⟨9863726943555522530190289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13151635924740696706920385 9863726943555522530190289)
                  ·
                    refine ⟨7397795207666641897642717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9863726943555522530190289 7397795207666641897642717)
                    ·
                      refine ⟨2774173202874990711616019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7397795207666641897642717 2774173202874990711616019)
                      ·
                        rfl

theorem cell23_5402683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 3].length) (baseStart_5402683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402683 prefixEnd_5402683 := by exact prefixLift 5402683
  have htrace : WordTrace (prefixWord ++ tailWord_5402683) baseStart_5402683 baseEnd_5402683 := by
    simpa [prefixWord, tailWord_5402683, baseEnd_5402683] using wordTrace_append hprefix tailTrace_5402683
  have hstable : (prefixWord ++ tailWord_5402683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402683).length < 2 ^ (prefixWord ++ tailWord_5402683).sum := by decide
  have hdescent : baseEnd_5402683 < baseStart_5402683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402717 : List Nat := [1, 4, 4, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_5402717 : Nat := 118140960795 + 5402717 * 2 ^ 59
def prefixEnd_5402717 : Nat := 4983230072969 + 3 ^ 40 * 5402717 * 2
def baseEnd_5402717 : Nat := 2774190661217243578590863

theorem tailTrace_5402717 : CollatzResearch.WordTrace tailWord_5402717 prefixEnd_5402717 2774190661217243578590863 := by
  unfold tailWord_5402717
  simp only [CollatzResearch.WordTrace]
  refine ⟨197053277567886494447966405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131368851711924329631977603 197053277567886494447966405)
  ·
    refine ⟨36947489543978717708993701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197053277567886494447966405 36947489543978717708993701)
    ·
      refine ⟨6927654289496009570436319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36947489543978717708993701 6927654289496009570436319)
      ·
        refine ⟨10391481434244014355654479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6927654289496009570436319 10391481434244014355654479)
        ·
          refine ⟨15587222151366021533481719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10391481434244014355654479 15587222151366021533481719)
          ·
            refine ⟨23380833227049032300222579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15587222151366021533481719 23380833227049032300222579)
            ·
              refine ⟨35071249840573548450333869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23380833227049032300222579 35071249840573548450333869)
              ·
                refine ⟨13151718690215080668875201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35071249840573548450333869 13151718690215080668875201)
                ·
                  refine ⟨9863789017661310501656401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13151718690215080668875201 9863789017661310501656401)
                  ·
                    refine ⟨7397841763245982876242301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9863789017661310501656401 7397841763245982876242301)
                    ·
                      refine ⟨2774190661217243578590863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7397841763245982876242301 2774190661217243578590863)
                      ·
                        rfl

theorem cell23_5402717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_5402717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402717 prefixEnd_5402717 := by exact prefixLift 5402717
  have htrace : WordTrace (prefixWord ++ tailWord_5402717) baseStart_5402717 baseEnd_5402717 := by
    simpa [prefixWord, tailWord_5402717, baseEnd_5402717] using wordTrace_append hprefix tailTrace_5402717
  have hstable : (prefixWord ++ tailWord_5402717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402717).length < 2 ^ (prefixWord ++ tailWord_5402717).sum := by decide
  have hdescent : baseEnd_5402717 < baseStart_5402717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402763 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 8, 4]
def baseStart_5402763 : Nat := 118140960795 + 5402763 * 2 ^ 59
def prefixEnd_5402763 : Nat := 4983230072969 + 3 ^ 40 * 5402763 * 2
def baseEnd_5402763 : Nat := 924738093775783466205217

theorem tailTrace_5402763 : CollatzResearch.WordTrace tailWord_5402763 prefixEnd_5402763 924738093775783466205217 := by
  unfold tailWord_5402763
  simp only [CollatzResearch.WordTrace]
  refine ⟨197054955325719844304140943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131369970217146562869427295 197054955325719844304140943)
  ·
    refine ⟨295582432988579766456211415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197054955325719844304140943 295582432988579766456211415)
    ·
      refine ⟨443373649482869649684317123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295582432988579766456211415 443373649482869649684317123)
      ·
        refine ⟨665060474224304474526475685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443373649482869649684317123 665060474224304474526475685)
        ·
          refine ⟨124698838917057088973714191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 665060474224304474526475685 124698838917057088973714191)
          ·
            refine ⟨187048258375585633460571287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124698838917057088973714191 187048258375585633460571287)
            ·
              refine ⟨280572387563378450190856931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187048258375585633460571287 280572387563378450190856931)
              ·
                refine ⟨420858581345067675286285397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280572387563378450190856931 420858581345067675286285397)
                ·
                  refine ⟨4931936500137511819761157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 420858581345067675286285397 4931936500137511819761157)
                  ·
                    refine ⟨924738093775783466205217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4931936500137511819761157 924738093775783466205217)
                    ·
                      rfl

theorem cell23_5402763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 4].length) (baseStart_5402763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402763 prefixEnd_5402763 := by exact prefixLift 5402763
  have htrace : WordTrace (prefixWord ++ tailWord_5402763) baseStart_5402763 baseEnd_5402763 := by
    simpa [prefixWord, tailWord_5402763, baseEnd_5402763] using wordTrace_append hprefix tailTrace_5402763
  have hstable : (prefixWord ++ tailWord_5402763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402763).length < 2 ^ (prefixWord ++ tailWord_5402763).sum := by decide
  have hdescent : baseEnd_5402763 < baseStart_5402763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402770 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_5402770 : Nat := 118140960795 + 5402770 * 2 ^ 59
def prefixEnd_5402770 : Nat := 4983230072969 + 3 ^ 40 * 5402770 * 2
def baseEnd_5402770 : Nat := 2774217875691931871228119

theorem tailTrace_5402770 : CollatzResearch.WordTrace tailWord_5402770 prefixEnd_5402770 2774217875691931871228119 := by
  unfold tailWord_5402770
  simp only [CollatzResearch.WordTrace]
  refine ⟨49263802659173621124911441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131370140424462989666430509 49263802659173621124911441)
  ·
    refine ⟨36947851994380215843683581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49263802659173621124911441 36947851994380215843683581)
    ·
      refine ⟨13855444497892580941381343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36947851994380215843683581 13855444497892580941381343)
      ·
        refine ⟨20783166746838871412072015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13855444497892580941381343 20783166746838871412072015)
        ·
          refine ⟨31174750120258307118108023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20783166746838871412072015 31174750120258307118108023)
          ·
            refine ⟨46762125180387460677162035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31174750120258307118108023 46762125180387460677162035)
            ·
              refine ⟨70143187770581191015743053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46762125180387460677162035 70143187770581191015743053)
              ·
                refine ⟨26303695413967946630903645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70143187770581191015743053 26303695413967946630903645)
                ·
                  refine ⟨9863885780237979986588867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26303695413967946630903645 9863885780237979986588867)
                  ·
                    refine ⟨14795828670356969979883301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9863885780237979986588867 14795828670356969979883301)
                    ·
                      refine ⟨2774217875691931871228119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14795828670356969979883301 2774217875691931871228119)
                      ·
                        rfl

theorem cell23_5402770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_5402770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402770 prefixEnd_5402770 := by exact prefixLift 5402770
  have htrace : WordTrace (prefixWord ++ tailWord_5402770) baseStart_5402770 baseEnd_5402770 := by
    simpa [prefixWord, tailWord_5402770, baseEnd_5402770] using wordTrace_append hprefix tailTrace_5402770
  have hstable : (prefixWord ++ tailWord_5402770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402770).length < 2 ^ (prefixWord ++ tailWord_5402770).sum := by decide
  have hdescent : baseEnd_5402770 < baseStart_5402770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402780 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 4, 4]
def baseStart_5402780 : Nat := 118140960795 + 5402780 * 2 ^ 59
def prefixEnd_5402780 : Nat := 4983230072969 + 3 ^ 40 * 5402780 * 2
def baseEnd_5402780 : Nat := 924741003499492277367691

theorem tailTrace_5402780 : CollatzResearch.WordTrace tailWord_5402780 prefixEnd_5402780 924741003499492277367691 := by
  unfold tailWord_5402780
  simp only [CollatzResearch.WordTrace]
  refine ⟨98527787683329128103754897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131370383577772170805006529 98527787683329128103754897)
  ·
    refine ⟨73895840762496846077816173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98527787683329128103754897 73895840762496846077816173)
    ·
      refine ⟨27710940285936317279181065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73895840762496846077816173 27710940285936317279181065)
      ·
        refine ⟨20783205214452237959385799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27710940285936317279181065 20783205214452237959385799)
        ·
          refine ⟨31174807821678356939078699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20783205214452237959385799 31174807821678356939078699)
          ·
            refine ⟨46762211732517535408618049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31174807821678356939078699 46762211732517535408618049)
            ·
              refine ⟨35071658799388151556463537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46762211732517535408618049 35071658799388151556463537)
              ·
                refine ⟨26303744099541113667347653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35071658799388151556463537 26303744099541113667347653)
                ·
                  refine ⟨4931952018663958812627685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26303744099541113667347653 4931952018663958812627685)
                  ·
                    refine ⟨924741003499492277367691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4931952018663958812627685 924741003499492277367691)
                    ·
                      rfl

theorem cell23_5402780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_5402780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402780 prefixEnd_5402780 := by exact prefixLift 5402780
  have htrace : WordTrace (prefixWord ++ tailWord_5402780) baseStart_5402780 baseEnd_5402780 := by
    simpa [prefixWord, tailWord_5402780, baseEnd_5402780] using wordTrace_append hprefix tailTrace_5402780
  have hstable : (prefixWord ++ tailWord_5402780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402780).length < 2 ^ (prefixWord ++ tailWord_5402780).sum := by decide
  have hdescent : baseEnd_5402780 < baseStart_5402780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402797 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_5402797 : Nat := 118140960795 + 5402797 * 2 ^ 59
def prefixEnd_5402797 : Nat := 4983230072969 + 3 ^ 40 * 5402797 * 2
def baseEnd_5402797 : Nat := 924743913223201088530165

theorem tailTrace_5402797 : CollatzResearch.WordTrace tailWord_5402797 prefixEnd_5402797 924743913223201088530165 := by
  unfold tailWord_5402797
  simp only [CollatzResearch.WordTrace]
  refine ⟨197056195407596668110878645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131370796938397778740585763 197056195407596668110878645)
  ·
    refine ⟨18474018319462187635394873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197056195407596668110878645 18474018319462187635394873)
    ·
      refine ⟨13855513739596640726546155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18474018319462187635394873 13855513739596640726546155)
      ·
        refine ⟨20783270609394961089819233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13855513739596640726546155 20783270609394961089819233)
        ·
          refine ⟨15587452957046220817364425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20783270609394961089819233 15587452957046220817364425)
          ·
            refine ⟨11690589717784665613023319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15587452957046220817364425 11690589717784665613023319)
            ·
              refine ⟨17535884576676998419534979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11690589717784665613023319 17535884576676998419534979)
              ·
                refine ⟨26303826865015497629302469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17535884576676998419534979 26303826865015497629302469)
                ·
                  refine ⟨4931967537190405805494213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26303826865015497629302469 4931967537190405805494213)
                  ·
                    refine ⟨924743913223201088530165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4931967537190405805494213 924743913223201088530165)
                    ·
                      rfl

theorem cell23_5402797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_5402797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402797 prefixEnd_5402797 := by exact prefixLift 5402797
  have htrace : WordTrace (prefixWord ++ tailWord_5402797) baseStart_5402797 baseEnd_5402797 := by
    simpa [prefixWord, tailWord_5402797, baseEnd_5402797] using wordTrace_append hprefix tailTrace_5402797
  have hstable : (prefixWord ++ tailWord_5402797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402797).length < 2 ^ (prefixWord ++ tailWord_5402797).sum := by decide
  have hdescent : baseEnd_5402797 < baseStart_5402797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402814 : List Nat := [4, 2, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_5402814 : Nat := 118140960795 + 5402814 * 2 ^ 59
def prefixEnd_5402814 : Nat := 4983230072969 + 3 ^ 40 * 5402814 * 2
def baseEnd_5402814 : Nat := 924746822946909899692639

theorem tailTrace_5402814 : CollatzResearch.WordTrace tailWord_5402814 prefixEnd_5402814 924746822946909899692639 := by
  unfold tailWord_5402814
  simp only [CollatzResearch.WordTrace]
  refine ⟨24632101931066885001780937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131371210299023386676164997 24632101931066885001780937)
  ·
    refine ⟨18474076448300163751335703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24632101931066885001780937 18474076448300163751335703)
    ·
      refine ⟨27711114672450245627003555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18474076448300163751335703 27711114672450245627003555)
      ·
        refine ⟨41566672008675368440505333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27711114672450245627003555 41566672008675368440505333)
        ·
          refine ⟨3896875500813315791297375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41566672008675368440505333 3896875500813315791297375)
          ·
            refine ⟨5845313251219973686946063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3896875500813315791297375 5845313251219973686946063)
            ·
              refine ⟨8767969876829960530419095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5845313251219973686946063 8767969876829960530419095)
              ·
                refine ⟨13151954815244940795628643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8767969876829960530419095 13151954815244940795628643)
                ·
                  refine ⟨19727932222867411193442965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13151954815244940795628643 19727932222867411193442965)
                  ·
                    refine ⟨924746822946909899692639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19727932222867411193442965 924746822946909899692639)
                    ·
                      rfl

theorem cell23_5402814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_5402814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402814 prefixEnd_5402814 := by exact prefixLift 5402814
  have htrace : WordTrace (prefixWord ++ tailWord_5402814) baseStart_5402814 baseEnd_5402814 := by
    simpa [prefixWord, tailWord_5402814, baseEnd_5402814] using wordTrace_append hprefix tailTrace_5402814
  have hstable : (prefixWord ++ tailWord_5402814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402814).length < 2 ^ (prefixWord ++ tailWord_5402814).sum := by decide
  have hdescent : baseEnd_5402814 < baseStart_5402814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402817 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_5402817 : Nat := 118140960795 + 5402817 * 2 ^ 59
def prefixEnd_5402817 : Nat := 4983230072969 + 3 ^ 40 * 5402817 * 2
def baseEnd_5402817 : Nat := 2774242009282693187340403

theorem tailTrace_5402817 : CollatzResearch.WordTrace tailWord_5402817 prefixEnd_5402817 2774242009282693187340403 := by
  unfold tailWord_5402817
  simp only [CollatzResearch.WordTrace]
  refine ⟨197056924867524211526606705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131371283245016141017737803 197056924867524211526606705)
  ·
    refine ⟨147792693650643158644955029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197056924867524211526606705 147792693650643158644955029)
    ·
      refine ⟨6927782514873898061482267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 147792693650643158644955029 6927782514873898061482267)
      ·
        refine ⟨10391673772310847092223401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6927782514873898061482267 10391673772310847092223401)
        ·
          refine ⟨7793755329233135319167551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10391673772310847092223401 7793755329233135319167551)
          ·
            refine ⟨11690632993849702978751327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7793755329233135319167551 11690632993849702978751327)
            ·
              refine ⟨17535949490774554468126991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11690632993849702978751327 17535949490774554468126991)
              ·
                refine ⟨26303924236161831702190487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17535949490774554468126991 26303924236161831702190487)
                ·
                  refine ⟨39455886354242747553285731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26303924236161831702190487 39455886354242747553285731)
                  ·
                    refine ⟨59183829531364121329928597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39455886354242747553285731 59183829531364121329928597)
                    ·
                      refine ⟨2774242009282693187340403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59183829531364121329928597 2774242009282693187340403)
                      ·
                        rfl

theorem cell23_5402817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_5402817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402817 prefixEnd_5402817 := by exact prefixLift 5402817
  have htrace : WordTrace (prefixWord ++ tailWord_5402817) baseStart_5402817 baseEnd_5402817 := by
    simpa [prefixWord, tailWord_5402817, baseEnd_5402817] using wordTrace_append hprefix tailTrace_5402817
  have hstable : (prefixWord ++ tailWord_5402817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402817).length < 2 ^ (prefixWord ++ tailWord_5402817).sum := by decide
  have hdescent : baseEnd_5402817 < baseStart_5402817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402833 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 2, 2, 5]
def baseStart_5402833 : Nat := 118140960795 + 5402833 * 2 ^ 59
def prefixEnd_5402833 : Nat := 4983230072969 + 3 ^ 40 * 5402833 * 2
def baseEnd_5402833 : Nat := 2774250224973165124740329

theorem tailTrace_5402833 : CollatzResearch.WordTrace tailWord_5402833 prefixEnd_5402833 2774250224973165124740329 := by
  unfold tailWord_5402833
  simp only [CollatzResearch.WordTrace]
  refine ⟨197057508435466246259189153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131371672290310830839459435 197057508435466246259189153)
  ·
    refine ⟨147793131326599684694391865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197057508435466246259189153 147793131326599684694391865)
    ·
      refine ⟨110844848494949763520793899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147793131326599684694391865 110844848494949763520793899)
      ·
        refine ⟨166267272742424645281190849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110844848494949763520793899 166267272742424645281190849)
        ·
          refine ⟨124700454556818483960893137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166267272742424645281190849 124700454556818483960893137)
          ·
            refine ⟨93525340917613862970669853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124700454556818483960893137 93525340917613862970669853)
            ·
              refine ⟨35072002844105198614001195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93525340917613862970669853 35072002844105198614001195)
              ·
                refine ⟨52608004266157797921001793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35072002844105198614001195 52608004266157797921001793)
                ·
                  refine ⟨39456003199618348440751345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52608004266157797921001793 39456003199618348440751345)
                  ·
                    refine ⟨29592002399713761330563509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39456003199618348440751345 29592002399713761330563509)
                    ·
                      refine ⟨2774250224973165124740329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29592002399713761330563509 2774250224973165124740329)
                      ·
                        rfl

theorem cell23_5402833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_5402833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402833 prefixEnd_5402833 := by exact prefixLift 5402833
  have htrace : WordTrace (prefixWord ++ tailWord_5402833) baseStart_5402833 baseEnd_5402833 := by
    simpa [prefixWord, tailWord_5402833, baseEnd_5402833] using wordTrace_append hprefix tailTrace_5402833
  have hstable : (prefixWord ++ tailWord_5402833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402833).length < 2 ^ (prefixWord ++ tailWord_5402833).sum := by decide
  have hdescent : baseEnd_5402833 < baseStart_5402833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402844 : List Nat := [2, 2, 5, 2, 2, 1, 9]
def baseStart_5402844 : Nat := 118140960795 + 5402844 * 2 ^ 59
def prefixEnd_5402844 : Nat := 4983230072969 + 3 ^ 40 * 5402844 * 2
def baseEnd_5402844 : Nat := 34250072509387217058059

theorem tailTrace_5402844 : CollatzResearch.WordTrace tailWord_5402844 prefixEnd_5402844 34250072509387217058059 := by
  unfold tailWord_5402844
  simp only [CollatzResearch.WordTrace]
  refine ⟨98528954819213197568919793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131371939758950930091893057 98528954819213197568919793)
  ·
    refine ⟨73896716114409898176689845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98528954819213197568919793 73896716114409898176689845)
    ·
      refine ⟨6927817135725927954064673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73896716114409898176689845 6927817135725927954064673)
      ·
        refine ⟨5195862851794445965548505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6927817135725927954064673 5195862851794445965548505)
        ·
          refine ⟨3896897138845834474161379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5195862851794445965548505 3896897138845834474161379)
          ·
            refine ⟨5845345708268751711242069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3896897138845834474161379 5845345708268751711242069)
            ·
              refine ⟨34250072509387217058059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5845345708268751711242069 34250072509387217058059)
              ·
                rfl

theorem cell23_5402844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 9].length) (baseStart_5402844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402844 prefixEnd_5402844 := by exact prefixLift 5402844
  have htrace : WordTrace (prefixWord ++ tailWord_5402844) baseStart_5402844 baseEnd_5402844 := by
    simpa [prefixWord, tailWord_5402844, baseEnd_5402844] using wordTrace_append hprefix tailTrace_5402844
  have hstable : (prefixWord ++ tailWord_5402844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402844).length < 2 ^ (prefixWord ++ tailWord_5402844).sum := by decide
  have hdescent : baseEnd_5402844 < baseStart_5402844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402870 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_5402870 : Nat := 118140960795 + 5402870 * 2 ^ 59
def prefixEnd_5402870 : Nat := 4983230072969 + 3 ^ 40 * 5402870 * 2
def baseEnd_5402870 : Nat := 924756407919127159992553

theorem tailTrace_5402870 : CollatzResearch.WordTrace tailWord_5402870 prefixEnd_5402870 924756407919127159992553 := by
  unfold tailWord_5402870
  simp only [CollatzResearch.WordTrace]
  refine ⟨12316178621020762598642879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131372571957554801052190709 12316178621020762598642879)
  ·
    refine ⟨18474267931531143897964319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12316178621020762598642879 18474267931531143897964319)
    ·
      refine ⟨27711401897296715846946479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18474267931531143897964319 27711401897296715846946479)
      ·
        refine ⟨41567102845945073770419719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27711401897296715846946479 41567102845945073770419719)
        ·
          refine ⟨62350654268917610655629579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41567102845945073770419719 62350654268917610655629579)
          ·
            refine ⟨93525981403376415983444369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62350654268917610655629579 93525981403376415983444369)
            ·
              refine ⟨70144486052532311987583277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93525981403376415983444369 70144486052532311987583277)
              ·
                refine ⟨26304182269699616995343729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70144486052532311987583277 26304182269699616995343729)
                ·
                  refine ⟨19728136702274712746507797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26304182269699616995343729 19728136702274712746507797)
                  ·
                    refine ⟨924756407919127159992553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19728136702274712746507797 924756407919127159992553)
                    ·
                      rfl

theorem cell23_5402870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_5402870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402870 prefixEnd_5402870 := by exact prefixLift 5402870
  have htrace : WordTrace (prefixWord ++ tailWord_5402870) baseStart_5402870 baseEnd_5402870 := by
    simpa [prefixWord, tailWord_5402870, baseEnd_5402870] using wordTrace_append hprefix tailTrace_5402870
  have hstable : (prefixWord ++ tailWord_5402870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402870).length < 2 ^ (prefixWord ++ tailWord_5402870).sum := by decide
  have hdescent : baseEnd_5402870 < baseStart_5402870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402883 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 9]
def baseStart_5402883 : Nat := 118140960795 + 5402883 * 2 ^ 59
def prefixEnd_5402883 : Nat := 4983230072969 + 3 ^ 40 * 5402883 * 2
def baseEnd_5402883 : Nat := 308252877667321103235011

theorem tailTrace_5402883 : CollatzResearch.WordTrace tailWord_5402883 prefixEnd_5402883 308252877667321103235011 := by
  unfold tailWord_5402883
  simp only [CollatzResearch.WordTrace]
  refine ⟨197059332085285104798509303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131372888056856736532339535 197059332085285104798509303)
  ·
    refine ⟨295588998127927657197763955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197059332085285104798509303 295588998127927657197763955)
    ·
      refine ⟨443383497191891485796645933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295588998127927657197763955 443383497191891485796645933)
      ·
        refine ⟨166268811446959307173742225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 443383497191891485796645933 166268811446959307173742225)
        ·
          refine ⟨124701608585219480380306669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166268811446959307173742225 124701608585219480380306669)
          ·
            refine ⟨46763103219457305142615001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124701608585219480380306669 46763103219457305142615001)
            ·
              refine ⟨35072327414592978856961251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46763103219457305142615001 35072327414592978856961251)
              ·
                refine ⟨52608491121889468285441877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35072327414592978856961251 52608491121889468285441877)
                ·
                  refine ⟨308252877667321103235011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52608491121889468285441877 308252877667321103235011)
                  ·
                    rfl

theorem cell23_5402883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 9].length) (baseStart_5402883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402883 prefixEnd_5402883 := by exact prefixLift 5402883
  have htrace : WordTrace (prefixWord ++ tailWord_5402883) baseStart_5402883 baseEnd_5402883 := by
    simpa [prefixWord, tailWord_5402883, baseEnd_5402883] using wordTrace_append hprefix tailTrace_5402883
  have hstable : (prefixWord ++ tailWord_5402883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402883).length < 2 ^ (prefixWord ++ tailWord_5402883).sum := by decide
  have hdescent : baseEnd_5402883 < baseStart_5402883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402911 : List Nat := [1, 1, 2, 4, 3, 2, 2, 2, 2, 2, 2]
def baseStart_5402911 : Nat := 118140960795 + 5402911 * 2 ^ 59
def prefixEnd_5402911 : Nat := 4983230072969 + 3 ^ 40 * 5402911 * 2
def baseEnd_5402911 : Nat := 2774290276464215819564971

theorem tailTrace_5402911 : CollatzResearch.WordTrace tailWord_5402911 prefixEnd_5402911 2774290276464215819564971 := by
  unfold tailWord_5402911
  simp only [CollatzResearch.WordTrace]
  refine ⟨197060353329183665580528587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131373568886122443720352391 197060353329183665580528587)
  ·
    refine ⟨295590529993775498370792881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197060353329183665580528587 295590529993775498370792881)
    ·
      refine ⟨221692897495331623778094661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295590529993775498370792881 221692897495331623778094661)
      ·
        refine ⟨41567418280374679458392749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221692897495331623778094661 41567418280374679458392749)
        ·
          refine ⟨15587781855140504796897281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41567418280374679458392749 15587781855140504796897281)
          ·
            refine ⟨11690836391355378597672961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15587781855140504796897281 11690836391355378597672961)
            ·
              refine ⟨8768127293516533948254721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11690836391355378597672961 8768127293516533948254721)
              ·
                refine ⟨6576095470137400461191041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8768127293516533948254721 6576095470137400461191041)
                ·
                  refine ⟨4932071602603050345893281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6576095470137400461191041 4932071602603050345893281)
                  ·
                    refine ⟨3699053701952287759419961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4932071602603050345893281 3699053701952287759419961)
                    ·
                      refine ⟨2774290276464215819564971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3699053701952287759419961 2774290276464215819564971)
                      ·
                        rfl

theorem cell23_5402911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_5402911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402911 prefixEnd_5402911 := by exact prefixLift 5402911
  have htrace : WordTrace (prefixWord ++ tailWord_5402911) baseStart_5402911 baseEnd_5402911 := by
    simpa [prefixWord, tailWord_5402911, baseEnd_5402911] using wordTrace_append hprefix tailTrace_5402911
  have hstable : (prefixWord ++ tailWord_5402911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402911).length < 2 ^ (prefixWord ++ tailWord_5402911).sum := by decide
  have hdescent : baseEnd_5402911 < baseStart_5402911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402967 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 4, 4, 2]
def baseStart_5402967 : Nat := 118140960795 + 5402967 * 2 ^ 59
def prefixEnd_5402967 : Nat := 4983230072969 + 3 ^ 40 * 5402967 * 2
def baseEnd_5402967 : Nat := 2774319031380867600464713

theorem tailTrace_5402967 : CollatzResearch.WordTrace tailWord_5402967 prefixEnd_5402967 2774319031380867600464713 := by
  unfold tailWord_5402967
  simp only [CollatzResearch.WordTrace]
  refine ⟨197062395816980787144567155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131374930544653858096378103 197062395816980787144567155)
  ·
    refine ⟨295593593725471180716850733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197062395816980787144567155 295593593725471180716850733)
    ·
      refine ⟨110847597647051692768819025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295593593725471180716850733 110847597647051692768819025)
      ·
        refine ⟨83135698235288769576614269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110847597647051692768819025 83135698235288769576614269)
        ·
          refine ⟨31175886838233288591230351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83135698235288769576614269 31175886838233288591230351)
          ·
            refine ⟨46763830257349932886845527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31175886838233288591230351 46763830257349932886845527)
            ·
              refine ⟨70145745386024899330268291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46763830257349932886845527 70145745386024899330268291)
              ·
                refine ⟨105218618079037348995402437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70145745386024899330268291 105218618079037348995402437)
                ·
                  refine ⟨19728490889819502936637957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105218618079037348995402437 19728490889819502936637957)
                  ·
                    refine ⟨3699092041841156800619617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19728490889819502936637957 3699092041841156800619617)
                    ·
                      refine ⟨2774319031380867600464713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3699092041841156800619617 2774319031380867600464713)
                      ·
                        rfl

theorem cell23_5402967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_5402967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402967 prefixEnd_5402967 := by exact prefixLift 5402967
  have htrace : WordTrace (prefixWord ++ tailWord_5402967) baseStart_5402967 baseEnd_5402967 := by
    simpa [prefixWord, tailWord_5402967, baseEnd_5402967] using wordTrace_append hprefix tailTrace_5402967
  have hstable : (prefixWord ++ tailWord_5402967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402967).length < 2 ^ (prefixWord ++ tailWord_5402967).sum := by decide
  have hdescent : baseEnd_5402967 < baseStart_5402967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402980 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_5402980 : Nat := 118140960795 + 5402980 * 2 ^ 59
def prefixEnd_5402980 : Nat := 4983230072969 + 3 ^ 40 * 5402980 * 2
def baseEnd_5402980 : Nat := 2774325706629376049602153

theorem tailTrace_5402980 : CollatzResearch.WordTrace tailWord_5402980 prefixEnd_5402980 2774325706629376049602153 := by
  unfold tailWord_5402980
  simp only [CollatzResearch.WordTrace]
  refine ⟨98531434982966845182395197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131375246643955793576526929 98531434982966845182395197)
  ·
    refine ⟨36949288118612566943398199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98531434982966845182395197 36949288118612566943398199)
    ·
      refine ⟨55423932177918850415097299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36949288118612566943398199 55423932177918850415097299)
      ·
        refine ⟨83135898266878275622645949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55423932177918850415097299 83135898266878275622645949)
        ·
          refine ⟨31175961850079353358492231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83135898266878275622645949 31175961850079353358492231)
          ·
            refine ⟨46763942775119030037738347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31175961850079353358492231 46763942775119030037738347)
            ·
              refine ⟨70145914162678545056607521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46763942775119030037738347 70145914162678545056607521)
              ·
                refine ⟨52609435622008908792455641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70145914162678545056607521 52609435622008908792455641)
                ·
                  refine ⟨39457076716506681594341731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52609435622008908792455641 39457076716506681594341731)
                  ·
                    refine ⟨59185615074760022391512597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39457076716506681594341731 59185615074760022391512597)
                    ·
                      refine ⟨2774325706629376049602153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59185615074760022391512597 2774325706629376049602153)
                      ·
                        rfl

theorem cell23_5402980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_5402980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402980 prefixEnd_5402980 := by exact prefixLift 5402980
  have htrace : WordTrace (prefixWord ++ tailWord_5402980) baseStart_5402980 baseEnd_5402980 := by
    simpa [prefixWord, tailWord_5402980, baseEnd_5402980] using wordTrace_append hprefix tailTrace_5402980
  have hstable : (prefixWord ++ tailWord_5402980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402980).length < 2 ^ (prefixWord ++ tailWord_5402980).sum := by decide
  have hdescent : baseEnd_5402980 < baseStart_5402980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5402984 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 2, 4, 2]
def baseStart_5402984 : Nat := 118140960795 + 5402984 * 2 ^ 59
def prefixEnd_5402984 : Nat := 4983230072969 + 3 ^ 40 * 5402984 * 2
def baseEnd_5402984 : Nat := 2774327760551994033952135

theorem tailTrace_5402984 : CollatzResearch.WordTrace tailWord_5402984 prefixEnd_5402984 2774327760551994033952135 := by
  unfold tailWord_5402984
  simp only [CollatzResearch.WordTrace]
  refine ⟨98531507928959599523968003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131375343905279466031957337 98531507928959599523968003)
  ·
    refine ⟨147797261893439399285952005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98531507928959599523968003 147797261893439399285952005)
    ·
      refine ⟨27711986605019887366116001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147797261893439399285952005 27711986605019887366116001)
      ·
        refine ⟨20783989953764915524587001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27711986605019887366116001 20783989953764915524587001)
        ·
          refine ⟨15587992465323686643440251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20783989953764915524587001 15587992465323686643440251)
          ·
            refine ⟨23381988697985529965160377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15587992465323686643440251 23381988697985529965160377)
            ·
              refine ⟨17536491523489147473870283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23381988697985529965160377 17536491523489147473870283)
              ·
                refine ⟨26304737285233721210805425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17536491523489147473870283 26304737285233721210805425)
                ·
                  refine ⟨19728552963925290908104069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26304737285233721210805425 19728552963925290908104069)
                  ·
                    refine ⟨3699103680735992045269513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19728552963925290908104069 3699103680735992045269513)
                    ·
                      refine ⟨2774327760551994033952135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3699103680735992045269513 2774327760551994033952135)
                      ·
                        rfl

theorem cell23_5402984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_5402984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5402984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5402984 prefixEnd_5402984 := by exact prefixLift 5402984
  have htrace : WordTrace (prefixWord ++ tailWord_5402984) baseStart_5402984 baseEnd_5402984 := by
    simpa [prefixWord, tailWord_5402984, baseEnd_5402984] using wordTrace_append hprefix tailTrace_5402984
  have hstable : (prefixWord ++ tailWord_5402984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5402984).length < 2 ^ (prefixWord ++ tailWord_5402984).sum := by decide
  have hdescent : baseEnd_5402984 < baseStart_5402984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5402984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403028 : List Nat := [2, 4, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_5403028 : Nat := 118140960795 + 5403028 * 2 ^ 59
def prefixEnd_5403028 : Nat := 4983230072969 + 3 ^ 40 * 5403028 * 2
def baseEnd_5403028 : Nat := 924783451233597287267311

theorem tailTrace_5403028 : CollatzResearch.WordTrace tailWord_5403028 prefixEnd_5403028 924783451233597287267311 := by
  unfold tailWord_5403028
  simp only [CollatzResearch.WordTrace]
  refine ⟨98532310334879897281268869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131376413779839863041691825 98532310334879897281268869)
  ·
    refine ⟨18474808187789980740237913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98532310334879897281268869 18474808187789980740237913)
    ·
      refine ⟨13856106140842485555178435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18474808187789980740237913 13856106140842485555178435)
      ·
        refine ⟨20784159211263728332767653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13856106140842485555178435 20784159211263728332767653)
        ·
          refine ⟨3897029852111949062393935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20784159211263728332767653 3897029852111949062393935)
          ·
            refine ⟨5845544778167923593590903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3897029852111949062393935 5845544778167923593590903)
            ·
              refine ⟨8768317167251885390386355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5845544778167923593590903 8768317167251885390386355)
              ·
                refine ⟨13152475750877828085579533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8768317167251885390386355 13152475750877828085579533)
                ·
                  refine ⟨4932178406579185532092325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13152475750877828085579533 4932178406579185532092325)
                  ·
                    refine ⟨924783451233597287267311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4932178406579185532092325 924783451233597287267311)
                    ·
                      rfl

theorem cell23_5403028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_5403028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403028 prefixEnd_5403028 := by exact prefixLift 5403028
  have htrace : WordTrace (prefixWord ++ tailWord_5403028) baseStart_5403028 baseEnd_5403028 := by
    simpa [prefixWord, tailWord_5403028, baseEnd_5403028] using wordTrace_append hprefix tailTrace_5403028
  have hstable : (prefixWord ++ tailWord_5403028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403028).length < 2 ^ (prefixWord ++ tailWord_5403028).sum := by decide
  have hdescent : baseEnd_5403028 < baseStart_5403028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403080 : List Nat := [2, 1, 3, 1, 3, 13]
def baseStart_5403080 : Nat := 118140960795 + 5403080 * 2 ^ 59
def prefixEnd_5403080 : Nat := 4983230072969 + 3 ^ 40 * 5403080 * 2
def baseEnd_5403080 : Nat := 11417189525493109705151

theorem tailTrace_5403080 : CollatzResearch.WordTrace tailWord_5403080 prefixEnd_5403080 11417189525493109705151 := by
  unfold tailWord_5403080
  simp only [CollatzResearch.WordTrace]
  refine ⟨98533258632785703721715347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131377678177047604962287129 98533258632785703721715347)
  ·
    refine ⟨147799887949178555582573021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98533258632785703721715347 147799887949178555582573021)
    ·
      refine ⟨55424957980941958343464883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147799887949178555582573021 55424957980941958343464883)
      ·
        refine ⟨83137436971412937515197325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55424957980941958343464883 83137436971412937515197325)
        ·
          refine ⟨31176538864279851568198997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83137436971412937515197325 31176538864279851568198997)
          ·
            refine ⟨11417189525493109705151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 31176538864279851568198997 11417189525493109705151)
            ·
              rfl

theorem cell23_5403080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 13].length) (baseStart_5403080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403080 prefixEnd_5403080 := by exact prefixLift 5403080
  have htrace : WordTrace (prefixWord ++ tailWord_5403080) baseStart_5403080 baseEnd_5403080 := by
    simpa [prefixWord, tailWord_5403080, baseEnd_5403080] using wordTrace_append hprefix tailTrace_5403080
  have hstable : (prefixWord ++ tailWord_5403080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403080).length < 2 ^ (prefixWord ++ tailWord_5403080).sum := by decide
  have hdescent : baseEnd_5403080 < baseStart_5403080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403094 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_5403094 : Nat := 118140960795 + 5403094 * 2 ^ 59
def prefixEnd_5403094 : Nat := 4983230072969 + 3 ^ 40 * 5403094 * 2
def baseEnd_5403094 : Nat := 2774384243423988603576629

theorem tailTrace_5403094 : CollatzResearch.WordTrace tailWord_5403094 prefixEnd_5403094 2774384243423988603576629 := by
  unfold tailWord_5403094
  simp only [CollatzResearch.WordTrace]
  refine ⟨12316689242970042989652521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131378018591680458556293557 12316689242970042989652521)
  ·
    refine ⟨9237516932227532242239391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12316689242970042989652521 9237516932227532242239391)
    ·
      refine ⟨13856275398341298363359087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9237516932227532242239391 13856275398341298363359087)
      ·
        refine ⟨20784413097511947545038631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13856275398341298363359087 20784413097511947545038631)
        ·
          refine ⟨31176619646267921317557947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20784413097511947545038631 31176619646267921317557947)
          ·
            refine ⟨46764929469401881976336921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31176619646267921317557947 46764929469401881976336921)
            ·
              refine ⟨35073697102051411482252691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46764929469401881976336921 35073697102051411482252691)
              ·
                refine ⟨52610545653077117223379037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35073697102051411482252691 52610545653077117223379037)
                ·
                  refine ⟨19728954619903918958767139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52610545653077117223379037 19728954619903918958767139)
                  ·
                    refine ⟨29593431929855878438150709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19728954619903918958767139 29593431929855878438150709)
                    ·
                      refine ⟨2774384243423988603576629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29593431929855878438150709 2774384243423988603576629)
                      ·
                        rfl

theorem cell23_5403094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_5403094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403094 prefixEnd_5403094 := by exact prefixLift 5403094
  have htrace : WordTrace (prefixWord ++ tailWord_5403094) baseStart_5403094 baseEnd_5403094 := by
    simpa [prefixWord, tailWord_5403094, baseEnd_5403094] using wordTrace_append hprefix tailTrace_5403094
  have hstable : (prefixWord ++ tailWord_5403094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403094).length < 2 ^ (prefixWord ++ tailWord_5403094).sum := by decide
  have hdescent : baseEnd_5403094 < baseStart_5403094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403114 : List Nat := [3, 1, 3, 1, 3, 2, 3, 7]
def baseStart_5403114 : Nat := 118140960795 + 5403114 * 2 ^ 59
def prefixEnd_5403114 : Nat := 4983230072969 + 3 ^ 40 * 5403114 * 2
def baseEnd_5403114 : Nat := 102755352334706612049131

theorem tailTrace_5403114 : CollatzResearch.WordTrace tailWord_5403114 prefixEnd_5403114 102755352334706612049131 := by
  unfold tailWord_5403114
  simp only [CollatzResearch.WordTrace]
  refine ⟨49266939336862057812542099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131378504898298820833445597 49266939336862057812542099)
  ·
    refine ⟨73900409005293086718813149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49266939336862057812542099 73900409005293086718813149)
    ·
      refine ⟨27712653376984907519554931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73900409005293086718813149 27712653376984907519554931)
      ·
        refine ⟨41568980065477361279332397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27712653376984907519554931 41568980065477361279332397)
        ·
          refine ⟨15588367524554010479749649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41568980065477361279332397 15588367524554010479749649)
          ·
            refine ⟨11691275643415507859812237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15588367524554010479749649 11691275643415507859812237)
            ·
              refine ⟨4384228366280815447429589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11691275643415507859812237 4384228366280815447429589)
              ·
                refine ⟨102755352334706612049131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4384228366280815447429589 102755352334706612049131)
                ·
                  rfl

theorem cell23_5403114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 7].length) (baseStart_5403114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403114 prefixEnd_5403114 := by exact prefixLift 5403114
  have htrace : WordTrace (prefixWord ++ tailWord_5403114) baseStart_5403114 baseEnd_5403114 := by
    simpa [prefixWord, tailWord_5403114, baseEnd_5403114] using wordTrace_append hprefix tailTrace_5403114
  have hstable : (prefixWord ++ tailWord_5403114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403114).length < 2 ^ (prefixWord ++ tailWord_5403114).sum := by decide
  have hdescent : baseEnd_5403114 < baseStart_5403114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403125 : List Nat := [1, 3, 5, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_5403125 : Nat := 118140960795 + 5403125 * 2 ^ 59
def prefixEnd_5403125 : Nat := 4983230072969 + 3 ^ 40 * 5403125 * 2
def baseEnd_5403125 : Nat := 2774400161324277982288987

theorem tailTrace_5403125 : CollatzResearch.WordTrace tailWord_5403125 prefixEnd_5403125 2774400161324277982288987 := by
  unfold tailWord_5403125
  simp only [CollatzResearch.WordTrace]
  refine ⟨197068158550408380128818829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131378772366938920085879219 197068158550408380128818829)
  ·
    refine ⟨73900559456403142548307061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197068158550408380128818829 73900559456403142548307061)
    ·
      refine ⟨6928177449037794613903787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73900559456403142548307061 6928177449037794613903787)
      ·
        refine ⟨10392266173556691920855681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6928177449037794613903787 10392266173556691920855681)
        ·
          refine ⟨7794199630167518940641761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10392266173556691920855681 7794199630167518940641761)
          ·
            refine ⟨5845649722625639205481321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7794199630167518940641761 5845649722625639205481321)
            ·
              refine ⟨4384237291969229404110991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5845649722625639205481321 4384237291969229404110991)
              ·
                refine ⟨6576355937953844106166487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4384237291969229404110991 6576355937953844106166487)
                ·
                  refine ⟨9864533906930766159249731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6576355937953844106166487 9864533906930766159249731)
                  ·
                    refine ⟨14796800860396149238874597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9864533906930766159249731 14796800860396149238874597)
                    ·
                      refine ⟨2774400161324277982288987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14796800860396149238874597 2774400161324277982288987)
                      ·
                        rfl

theorem cell23_5403125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_5403125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403125 prefixEnd_5403125 := by exact prefixLift 5403125
  have htrace : WordTrace (prefixWord ++ tailWord_5403125) baseStart_5403125 baseEnd_5403125 := by
    simpa [prefixWord, tailWord_5403125, baseEnd_5403125] using wordTrace_append hprefix tailTrace_5403125
  have hstable : (prefixWord ++ tailWord_5403125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403125).length < 2 ^ (prefixWord ++ tailWord_5403125).sum := by decide
  have hdescent : baseEnd_5403125 < baseStart_5403125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403141 : List Nat := [1, 3, 1, 1, 2, 2, 5, 2, 2, 1, 3]
def baseStart_5403141 : Nat := 118140960795 + 5403141 * 2 ^ 59
def prefixEnd_5403141 : Nat := 4983230072969 + 3 ^ 40 * 5403141 * 2
def baseEnd_5403141 : Nat := 2774408377014749919688913

theorem tailTrace_5403141 : CollatzResearch.WordTrace tailWord_5403141 prefixEnd_5403141 2774408377014749919688913 := by
  unfold tailWord_5403141
  simp only [CollatzResearch.WordTrace]
  refine ⟨197068742118350414861401277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131379161412233609907600851 197068742118350414861401277)
  ·
    refine ⟨73900778294381405573025479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197068742118350414861401277 73900778294381405573025479)
    ·
      refine ⟨110851167441572108359538219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73900778294381405573025479 110851167441572108359538219)
      ·
        refine ⟨166276751162358162539307329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110851167441572108359538219 166276751162358162539307329)
        ·
          refine ⟨124707563371768621904480497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166276751162358162539307329 124707563371768621904480497)
          ·
            refine ⟨93530672528826466428360373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124707563371768621904480497 93530672528826466428360373)
            ·
              refine ⟨8768500549577481227658785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93530672528826466428360373 8768500549577481227658785)
              ·
                refine ⟨6576375412183110920744089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8768500549577481227658785 6576375412183110920744089)
                ·
                  refine ⟨4932281559137333190558067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6576375412183110920744089 4932281559137333190558067)
                  ·
                    refine ⟨7398422338705999785837101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4932281559137333190558067 7398422338705999785837101)
                    ·
                      refine ⟨2774408377014749919688913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7398422338705999785837101 2774408377014749919688913)
                      ·
                        rfl

theorem cell23_5403141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 1, 3].length) (baseStart_5403141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403141 prefixEnd_5403141 := by exact prefixLift 5403141
  have htrace : WordTrace (prefixWord ++ tailWord_5403141) baseStart_5403141 baseEnd_5403141 := by
    simpa [prefixWord, tailWord_5403141, baseEnd_5403141] using wordTrace_append hprefix tailTrace_5403141
  have hstable : (prefixWord ++ tailWord_5403141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403141).length < 2 ^ (prefixWord ++ tailWord_5403141).sum := by decide
  have hdescent : baseEnd_5403141 < baseStart_5403141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403142 : List Nat := [6, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_5403142 : Nat := 118140960795 + 5403142 * 2 ^ 59
def prefixEnd_5403142 : Nat := 4983230072969 + 3 ^ 40 * 5403142 * 2
def baseEnd_5403142 : Nat := 2774408890495404415776409

theorem tailTrace_5403142 : CollatzResearch.WordTrace tailWord_5403142 prefixEnd_5403142 2774408890495404415776409 := by
  unfold tailWord_5403142
  simp only [CollatzResearch.WordTrace]
  refine ⟨6158399330979587251005865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 131379185727564528021458453 6158399330979587251005865)
  ·
    refine ⟨4618799498234690438254399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6158399330979587251005865 4618799498234690438254399)
    ·
      refine ⟨6928199247352035657381599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4618799498234690438254399 6928199247352035657381599)
      ·
        refine ⟨10392298871028053486072399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6928199247352035657381599 10392298871028053486072399)
        ·
          refine ⟨15588448306542080229108599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10392298871028053486072399 15588448306542080229108599)
          ·
            refine ⟨23382672459813120343662899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15588448306542080229108599 23382672459813120343662899)
            ·
              refine ⟨35074008689719680515494349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23382672459813120343662899 35074008689719680515494349)
              ·
                refine ⟨13152753258644880193310381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35074008689719680515494349 13152753258644880193310381)
                ·
                  refine ⟨4932282471991830072491393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13152753258644880193310381 4932282471991830072491393)
                  ·
                    refine ⟨3699211853993872554368545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4932282471991830072491393 3699211853993872554368545)
                    ·
                      refine ⟨2774408890495404415776409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3699211853993872554368545 2774408890495404415776409)
                      ·
                        rfl

theorem cell23_5403142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_5403142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403142 prefixEnd_5403142 := by exact prefixLift 5403142
  have htrace : WordTrace (prefixWord ++ tailWord_5403142) baseStart_5403142 baseEnd_5403142 := by
    simpa [prefixWord, tailWord_5403142, baseEnd_5403142] using wordTrace_append hprefix tailTrace_5403142
  have hstable : (prefixWord ++ tailWord_5403142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403142).length < 2 ^ (prefixWord ++ tailWord_5403142).sum := by decide
  have hdescent : baseEnd_5403142 < baseStart_5403142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403157 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 2, 6]
def baseStart_5403157 : Nat := 118140960795 + 5403157 * 2 ^ 59
def prefixEnd_5403157 : Nat := 4983230072969 + 3 ^ 40 * 5403157 * 2
def baseEnd_5403157 : Nat := 924805530901740619029613

theorem tailTrace_5403157 : CollatzResearch.WordTrace tailWord_5403157 prefixEnd_5403157 924805530901740619029613 := by
  unfold tailWord_5403157
  simp only [CollatzResearch.WordTrace]
  refine ⟨197069325686292449593983725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131379550457528299729322483 197069325686292449593983725)
  ·
    refine ⟨73900997132359668597743897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197069325686292449593983725 73900997132359668597743897)
    ·
      refine ⟨55425747849269751448307923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73900997132359668597743897 55425747849269751448307923)
      ·
        refine ⟨83138621773904627172461885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55425747849269751448307923 83138621773904627172461885)
        ·
          refine ⟨31176983165214235189673207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83138621773904627172461885 31176983165214235189673207)
          ·
            refine ⟨46765474747821352784509811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31176983165214235189673207 46765474747821352784509811)
            ·
              refine ⟨70148212121732029176764717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46765474747821352784509811 70148212121732029176764717)
              ·
                refine ⟨26305579545649510941286769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70148212121732029176764717 26305579545649510941286769)
                ·
                  refine ⟨19729184659237133205965077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26305579545649510941286769 19729184659237133205965077)
                  ·
                    refine ⟨924805530901740619029613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19729184659237133205965077 924805530901740619029613)
                    ·
                      rfl

theorem cell23_5403157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_5403157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403157 prefixEnd_5403157 := by exact prefixLift 5403157
  have htrace : WordTrace (prefixWord ++ tailWord_5403157) baseStart_5403157 baseEnd_5403157 := by
    simpa [prefixWord, tailWord_5403157, baseEnd_5403157] using wordTrace_append hprefix tailTrace_5403157
  have hstable : (prefixWord ++ tailWord_5403157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403157).length < 2 ^ (prefixWord ++ tailWord_5403157).sum := by decide
  have hdescent : baseEnd_5403157 < baseStart_5403157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403167 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 5]
def baseStart_5403167 : Nat := 118140960795 + 5403167 * 2 ^ 59
def prefixEnd_5403167 : Nat := 4983230072969 + 3 ^ 40 * 5403167 * 2
def baseEnd_5403167 : Nat := 2774421727511766817963793

theorem tailTrace_5403167 : CollatzResearch.WordTrace tailWord_5403167 prefixEnd_5403167 2774421727511766817963793 := by
  unfold tailWord_5403167
  simp only [CollatzResearch.WordTrace]
  refine ⟨197069690416256221301847755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131379793610837480867898503 197069690416256221301847755)
  ·
    refine ⟨295604535624384331952771633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197069690416256221301847755 295604535624384331952771633)
    ·
      refine ⟨221703401718288248964578725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295604535624384331952771633 221703401718288248964578725)
      ·
        refine ⟨41569387822179046680858511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221703401718288248964578725 41569387822179046680858511)
        ·
          refine ⟨62354081733268570021287767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41569387822179046680858511 62354081733268570021287767)
          ·
            refine ⟨93531122599902855031931651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62354081733268570021287767 93531122599902855031931651)
            ·
              refine ⟨140296683899854282547897477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93531122599902855031931651 140296683899854282547897477)
              ·
                refine ⟨26305628231222677977730777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140296683899854282547897477 26305628231222677977730777)
                ·
                  refine ⟨19729221173417008483298083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26305628231222677977730777 19729221173417008483298083)
                  ·
                    refine ⟨29593831760125512724947125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19729221173417008483298083 29593831760125512724947125)
                    ·
                      refine ⟨2774421727511766817963793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29593831760125512724947125 2774421727511766817963793)
                      ·
                        rfl

theorem cell23_5403167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_5403167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403167 prefixEnd_5403167 := by exact prefixLift 5403167
  have htrace : WordTrace (prefixWord ++ tailWord_5403167) baseStart_5403167 baseEnd_5403167 := by
    simpa [prefixWord, tailWord_5403167, baseEnd_5403167] using wordTrace_append hprefix tailTrace_5403167
  have hstable : (prefixWord ++ tailWord_5403167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403167).length < 2 ^ (prefixWord ++ tailWord_5403167).sum := by decide
  have hdescent : baseEnd_5403167 < baseStart_5403167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403214 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3]
def baseStart_5403214 : Nat := 118140960795 + 5403214 * 2 ^ 59
def prefixEnd_5403214 : Nat := 4983230072969 + 3 ^ 40 * 5403214 * 2
def baseEnd_5403214 : Nat := 2774445861102528134076077

theorem tailTrace_5403214 : CollatzResearch.WordTrace tailWord_5403214 prefixEnd_5403214 2774445861102528134076077 := by
  unfold tailWord_5403214
  simp only [CollatzResearch.WordTrace]
  refine ⟨24633925580885743541101087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131380936431390632219205797 24633925580885743541101087)
  ·
    refine ⟨36950888371328615311651631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24633925580885743541101087 36950888371328615311651631)
    ·
      refine ⟨55426332556992922967477447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36950888371328615311651631 55426332556992922967477447)
      ·
        refine ⟨83139498835489384451216171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55426332556992922967477447 83139498835489384451216171)
        ·
          refine ⟨124709248253234076676824257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83139498835489384451216171 124709248253234076676824257)
          ·
            refine ⟨93531936189925557507618193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124709248253234076676824257 93531936189925557507618193)
            ·
              refine ⟨70148952142444168130713645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93531936189925557507618193 70148952142444168130713645)
              ·
                refine ⟨26305857053416563049017617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70148952142444168130713645 26305857053416563049017617)
                ·
                  refine ⟨19729392790062422286763213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26305857053416563049017617 19729392790062422286763213)
                  ·
                    refine ⟨7398522296273408357536205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19729392790062422286763213 7398522296273408357536205)
                    ·
                      refine ⟨2774445861102528134076077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7398522296273408357536205 2774445861102528134076077)
                      ·
                        rfl

theorem cell23_5403214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_5403214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403214 prefixEnd_5403214 := by exact prefixLift 5403214
  have htrace : WordTrace (prefixWord ++ tailWord_5403214) baseStart_5403214 baseEnd_5403214 := by
    simpa [prefixWord, tailWord_5403214, baseEnd_5403214] using wordTrace_append hprefix tailTrace_5403214
  have hstable : (prefixWord ++ tailWord_5403214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403214).length < 2 ^ (prefixWord ++ tailWord_5403214).sum := by decide
  have hdescent : baseEnd_5403214 < baseStart_5403214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403271 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 2, 4, 2]
def baseStart_5403271 : Nat := 118140960795 + 5403271 * 2 ^ 59
def prefixEnd_5403271 : Nat := 4983230072969 + 3 ^ 40 * 5403271 * 2
def baseEnd_5403271 : Nat := 2774475129499834411063315

theorem tailTrace_5403271 : CollatzResearch.WordTrace tailWord_5403271 prefixEnd_5403271 2774475129499834411063315 := by
  unfold tailWord_5403271
  simp only [CollatzResearch.WordTrace]
  refine ⟨197073483607879447063633667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131382322405252964709089111 197073483607879447063633667)
  ·
    refine ⟨295610225411819170595450501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197073483607879447063633667 295610225411819170595450501)
    ·
      refine ⟨55426917264716094486646969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 295610225411819170595450501 55426917264716094486646969)
      ·
        refine ⟨41570187948537070864985227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55426917264716094486646969 41570187948537070864985227)
        ·
          refine ⟨62355281922805606297477841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41570187948537070864985227 62355281922805606297477841)
          ·
            refine ⟨46766461442104204723108381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62355281922805606297477841 46766461442104204723108381)
            ·
              refine ⟨17537423040789076771165643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46766461442104204723108381 17537423040789076771165643)
              ·
                refine ⟨26306134561183615156748465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17537423040789076771165643 26306134561183615156748465)
                ·
                  refine ⟨19729600920887711367561349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26306134561183615156748465 19729600920887711367561349)
                  ·
                    refine ⟨3699300172666445881417753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19729600920887711367561349 3699300172666445881417753)
                    ·
                      refine ⟨2774475129499834411063315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3699300172666445881417753 2774475129499834411063315)
                      ·
                        rfl

theorem cell23_5403271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_5403271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403271 prefixEnd_5403271 := by exact prefixLift 5403271
  have htrace : WordTrace (prefixWord ++ tailWord_5403271) baseStart_5403271 baseEnd_5403271 := by
    simpa [prefixWord, tailWord_5403271, baseEnd_5403271] using wordTrace_append hprefix tailTrace_5403271
  have hstable : (prefixWord ++ tailWord_5403271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403271).length < 2 ^ (prefixWord ++ tailWord_5403271).sum := by decide
  have hdescent : baseEnd_5403271 < baseStart_5403271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403311 : List Nat := [1, 1, 2, 1, 2, 7, 1, 2, 6]
def baseStart_5403311 : Nat := 118140960795 + 5403311 * 2 ^ 59
def prefixEnd_5403311 : Nat := 4983230072969 + 3 ^ 40 * 5403311 * 2
def baseEnd_5403311 : Nat := 308277296525112694951459

theorem tailTrace_5403311 : CollatzResearch.WordTrace tailWord_5403311 prefixEnd_5403311 308277296525112694951459 := by
  unfold tailWord_5403311
  simp only [CollatzResearch.WordTrace]
  refine ⟨197074942527734533895089787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131383295018489689263393191 197074942527734533895089787)
  ·
    refine ⟨295612413791601800842634681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197074942527734533895089787 295612413791601800842634681)
    ·
      refine ⟨221709310343701350631976011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295612413791601800842634681 221709310343701350631976011)
      ·
        refine ⟨332563965515552025947964017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221709310343701350631976011 332563965515552025947964017)
        ·
          refine ⟨249422974136664019460973013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332563965515552025947964017 249422974136664019460973013)
          ·
            refine ⟨5845850956328062956116555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 249422974136664019460973013 5845850956328062956116555)
            ·
              refine ⟨8768776434492094434174833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5845850956328062956116555 8768776434492094434174833)
              ·
                refine ⟨6576582325869070825631125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8768776434492094434174833 6576582325869070825631125)
                ·
                  refine ⟨308277296525112694951459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6576582325869070825631125 308277296525112694951459)
                  ·
                    rfl

theorem cell23_5403311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 6].length) (baseStart_5403311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403311 prefixEnd_5403311 := by exact prefixLift 5403311
  have htrace : WordTrace (prefixWord ++ tailWord_5403311) baseStart_5403311 baseEnd_5403311 := by
    simpa [prefixWord, tailWord_5403311, baseEnd_5403311] using wordTrace_append hprefix tailTrace_5403311
  have hstable : (prefixWord ++ tailWord_5403311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403311).length < 2 ^ (prefixWord ++ tailWord_5403311).sum := by decide
  have hdescent : baseEnd_5403311 < baseStart_5403311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403338 : List Nat := [3, 1, 2, 1, 4, 1, 2, 2, 3, 1, 3]
def baseStart_5403338 : Nat := 118140960795 + 5403338 * 2 ^ 59
def prefixEnd_5403338 : Nat := 4983230072969 + 3 ^ 40 * 5403338 * 2
def baseEnd_5403338 : Nat := 2774509532703685648925507

theorem tailTrace_5403338 : CollatzResearch.WordTrace tailWord_5403338 prefixEnd_5403338 2774509532703685648925507 := by
  unfold tailWord_5403338
  simp only [CollatzResearch.WordTrace]
  refine ⟨49268981824659179376580667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131383951532424478337548445 49268981824659179376580667)
  ·
    refine ⟨73903472736988769064871001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49268981824659179376580667 73903472736988769064871001)
    ·
      refine ⟨55427604552741576798653251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73903472736988769064871001 55427604552741576798653251)
      ·
        refine ⟨83141406829112365197979877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55427604552741576798653251 83141406829112365197979877)
        ·
          refine ⟨15589013780458568474621227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83141406829112365197979877 15589013780458568474621227)
          ·
            refine ⟨23383520670687852711931841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15589013780458568474621227 23383520670687852711931841)
            ·
              refine ⟨17537640503015889533948881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23383520670687852711931841 17537640503015889533948881)
              ·
                refine ⟨13153230377261917150461661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17537640503015889533948881 13153230377261917150461661)
                ·
                  refine ⟨4932461391473218931423123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13153230377261917150461661 4932461391473218931423123)
                  ·
                    refine ⟨7398692087209828397134685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4932461391473218931423123 7398692087209828397134685)
                    ·
                      refine ⟨2774509532703685648925507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7398692087209828397134685 2774509532703685648925507)
                      ·
                        rfl

theorem cell23_5403338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_5403338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403338 prefixEnd_5403338 := by exact prefixLift 5403338
  have htrace : WordTrace (prefixWord ++ tailWord_5403338) baseStart_5403338 baseEnd_5403338 := by
    simpa [prefixWord, tailWord_5403338, baseEnd_5403338] using wordTrace_append hprefix tailTrace_5403338
  have hstable : (prefixWord ++ tailWord_5403338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403338).length < 2 ^ (prefixWord ++ tailWord_5403338).sum := by decide
  have hdescent : baseEnd_5403338 < baseStart_5403338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403344 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 4]
def baseStart_5403344 : Nat := 118140960795 + 5403344 * 2 ^ 59
def prefixEnd_5403344 : Nat := 4983230072969 + 3 ^ 40 * 5403344 * 2
def baseEnd_5403344 : Nat := 2774512613587612625450479

theorem tailTrace_5403344 : CollatzResearch.WordTrace tailWord_5403344 prefixEnd_5403344 2774512613587612625450479 := by
  unfold tailWord_5403344
  simp only [CollatzResearch.WordTrace]
  refine ⟨98538073068307490265520543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131384097424409987020694057 98538073068307490265520543)
  ·
    refine ⟨147807109602461235398280815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98538073068307490265520543 147807109602461235398280815)
    ·
      refine ⟨221710664403691853097421223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147807109602461235398280815 221710664403691853097421223)
      ·
        refine ⟨332565996605537779646131835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221710664403691853097421223 332565996605537779646131835)
        ·
          refine ⟨498848994908306669469197753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332565996605537779646131835 498848994908306669469197753)
          ·
            refine ⟨374136746181230002101898315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 498848994908306669469197753 374136746181230002101898315)
            ·
              refine ⟨561205119271845003152847473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374136746181230002101898315 561205119271845003152847473)
              ·
                refine ⟨420903839453883752364635605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 561205119271845003152847473 420903839453883752364635605)
                ·
                  refine ⟨9864933737200400446046147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 420903839453883752364635605 9864933737200400446046147)
                  ·
                    refine ⟨14797400605800600669069221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9864933737200400446046147 14797400605800600669069221)
                    ·
                      refine ⟨2774512613587612625450479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14797400605800600669069221 2774512613587612625450479)
                      ·
                        rfl

theorem cell23_5403344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 4].length) (baseStart_5403344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403344 prefixEnd_5403344 := by exact prefixLift 5403344
  have htrace : WordTrace (prefixWord ++ tailWord_5403344) baseStart_5403344 baseEnd_5403344 := by
    simpa [prefixWord, tailWord_5403344, baseEnd_5403344] using wordTrace_append hprefix tailTrace_5403344
  have hstable : (prefixWord ++ tailWord_5403344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403344).length < 2 ^ (prefixWord ++ tailWord_5403344).sum := by decide
  have hdescent : baseEnd_5403344 < baseStart_5403344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403349 : List Nat := [1, 3, 2, 5, 2, 1, 1, 3, 1, 4]
def baseStart_5403349 : Nat := 118140960795 + 5403349 * 2 ^ 59
def prefixEnd_5403349 : Nat := 4983230072969 + 3 ^ 40 * 5403349 * 2
def baseEnd_5403349 : Nat := 924838393663628368629319

theorem tailTrace_5403349 : CollatzResearch.WordTrace tailWord_5403349 prefixEnd_5403349 924838393663628368629319 := by
  unfold tailWord_5403349
  simp only [CollatzResearch.WordTrace]
  refine ⟨197076328501596866384973101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131384219001064577589982067 197076328501596866384973101)
  ·
    refine ⟨73903623188098824894364913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197076328501596866384973101 73903623188098824894364913)
    ·
      refine ⟨55427717391074118670773685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73903623188098824894364913 55427717391074118670773685)
      ·
        refine ⟨5196348505413198625385033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55427717391074118670773685 5196348505413198625385033)
        ·
          refine ⟨3897261379059898969038775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5196348505413198625385033 3897261379059898969038775)
          ·
            refine ⟨5845892068589848453558163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3897261379059898969038775 5845892068589848453558163)
            ·
              refine ⟨8768838102884772680337245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5845892068589848453558163 8768838102884772680337245)
              ·
                refine ⟨3288314288581789755126467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8768838102884772680337245 3288314288581789755126467)
                ·
                  refine ⟨4932471432872684632689701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3288314288581789755126467 4932471432872684632689701)
                  ·
                    refine ⟨924838393663628368629319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4932471432872684632689701 924838393663628368629319)
                    ·
                      rfl

theorem cell23_5403349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_5403349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403349 prefixEnd_5403349 := by exact prefixLift 5403349
  have htrace : WordTrace (prefixWord ++ tailWord_5403349) baseStart_5403349 baseEnd_5403349 := by
    simpa [prefixWord, tailWord_5403349, baseEnd_5403349] using wordTrace_append hprefix tailTrace_5403349
  have hstable : (prefixWord ++ tailWord_5403349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403349).length < 2 ^ (prefixWord ++ tailWord_5403349).sum := by decide
  have hdescent : baseEnd_5403349 < baseStart_5403349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403354 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 3, 6]
def baseStart_5403354 : Nat := 118140960795 + 5403354 * 2 ^ 59
def prefixEnd_5403354 : Nat := 4983230072969 + 3 ^ 40 * 5403354 * 2
def baseEnd_5403354 : Nat := 924839249464719195441811

theorem tailTrace_5403354 : CollatzResearch.WordTrace tailWord_5403354 prefixEnd_5403354 924839249464719195441811 := by
  unfold tailWord_5403354
  simp only [CollatzResearch.WordTrace]
  refine ⟨49269127716644688059726279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131384340577719168159270077 49269127716644688059726279)
  ·
    refine ⟨73903691574967032089589419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49269127716644688059726279 73903691574967032089589419)
    ·
      refine ⟨110855537362450548134384129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73903691574967032089589419 110855537362450548134384129)
      ·
        refine ⟨83141653021837911100788097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110855537362450548134384129 83141653021837911100788097)
        ·
          refine ⟨62356239766378433325591073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83141653021837911100788097 62356239766378433325591073)
          ·
            refine ⟨46767179824783824994193305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62356239766378433325591073 46767179824783824994193305)
            ·
              refine ⟨35075384868587868745644979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46767179824783824994193305 35075384868587868745644979)
              ·
                refine ⟨52613077302881803118467469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35075384868587868745644979 52613077302881803118467469)
                ·
                  refine ⟨19729903988580676169425301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52613077302881803118467469 19729903988580676169425301)
                  ·
                    refine ⟨924839249464719195441811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19729903988580676169425301 924839249464719195441811)
                    ·
                      rfl

theorem cell23_5403354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_5403354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403354 prefixEnd_5403354 := by exact prefixLift 5403354
  have htrace : WordTrace (prefixWord ++ tailWord_5403354) baseStart_5403354 baseEnd_5403354 := by
    simpa [prefixWord, tailWord_5403354, baseEnd_5403354] using wordTrace_append hprefix tailTrace_5403354
  have hstable : (prefixWord ++ tailWord_5403354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403354).length < 2 ^ (prefixWord ++ tailWord_5403354).sum := by decide
  have hdescent : baseEnd_5403354 < baseStart_5403354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403371 : List Nat := [1, 1, 1, 1, 2, 4, 1, 6, 2, 4]
def baseStart_5403371 : Nat := 118140960795 + 5403371 * 2 ^ 59
def prefixEnd_5403371 : Nat := 4983230072969 + 3 ^ 40 * 5403371 * 2
def baseEnd_5403371 : Nat := 924842159188428006604285

theorem tailTrace_5403371 : CollatzResearch.WordTrace tailWord_5403371 prefixEnd_5403371 924842159188428006604285 := by
  unfold tailWord_5403371
  simp only [CollatzResearch.WordTrace]
  refine ⟨197077130907517164142273967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131384753938344776094849311 197077130907517164142273967)
  ·
    refine ⟨295615696361275746213410951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197077130907517164142273967 295615696361275746213410951)
    ·
      refine ⟨443423544541913619320116427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295615696361275746213410951 443423544541913619320116427)
      ·
        refine ⟨665135316812870428980174641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443423544541913619320116427 665135316812870428980174641)
        ·
          refine ⟨498851487609652821735130981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 665135316812870428980174641 498851487609652821735130981)
          ·
            refine ⟨93534653926809904075337059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 498851487609652821735130981 93534653926809904075337059)
            ·
              refine ⟨140301980890214856113005589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93534653926809904075337059 140301980890214856113005589)
              ·
                refine ⟨6576655354228821380297137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 140301980890214856113005589 6576655354228821380297137)
                ·
                  refine ⟨4932491515671616035222853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6576655354228821380297137 4932491515671616035222853)
                  ·
                    refine ⟨924842159188428006604285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4932491515671616035222853 924842159188428006604285)
                    ·
                      rfl

theorem cell23_5403371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 4].length) (baseStart_5403371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403371 prefixEnd_5403371 := by exact prefixLift 5403371
  have htrace : WordTrace (prefixWord ++ tailWord_5403371) baseStart_5403371 baseEnd_5403371 := by
    simpa [prefixWord, tailWord_5403371, baseEnd_5403371] using wordTrace_append hprefix tailTrace_5403371
  have hstable : (prefixWord ++ tailWord_5403371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403371).length < 2 ^ (prefixWord ++ tailWord_5403371).sum := by decide
  have hdescent : baseEnd_5403371 < baseStart_5403371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403384 : List Nat := [2, 1, 2, 1, 1, 2, 6, 8]
def baseStart_5403384 : Nat := 118140960795 + 5403384 * 2 ^ 59
def prefixEnd_5403384 : Nat := 4983230072969 + 3 ^ 40 * 5403384 * 2
def baseEnd_5403384 : Nat := 102760487141251572924085

theorem tailTrace_5403384 : CollatzResearch.WordTrace tailWord_5403384 prefixEnd_5403384 102760487141251572924085 := by
  unfold tailWord_5403384
  simp only [CollatzResearch.WordTrace]
  refine ⟨98538802528235033681248603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131385070037646711574998137 98538802528235033681248603)
  ·
    refine ⟨147808203792352550521872905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98538802528235033681248603 147808203792352550521872905)
    ·
      refine ⟨110856152844264412891404679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147808203792352550521872905 110856152844264412891404679)
      ·
        refine ⟨166284229266396619337107019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110856152844264412891404679 166284229266396619337107019)
        ·
          refine ⟨249426343899594929005660529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166284229266396619337107019 249426343899594929005660529)
          ·
            refine ⟨187069757924696196754245397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249426343899594929005660529 187069757924696196754245397)
            ·
              refine ⟨8768894902720134222855253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 187069757924696196754245397 8768894902720134222855253)
              ·
                refine ⟨102760487141251572924085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8768894902720134222855253 102760487141251572924085)
                ·
                  rfl

theorem cell23_5403384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 8].length) (baseStart_5403384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403384 prefixEnd_5403384 := by exact prefixLift 5403384
  have htrace : WordTrace (prefixWord ++ tailWord_5403384) baseStart_5403384 baseEnd_5403384 := by
    simpa [prefixWord, tailWord_5403384, baseEnd_5403384] using wordTrace_append hprefix tailTrace_5403384
  have hstable : (prefixWord ++ tailWord_5403384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403384).length < 2 ^ (prefixWord ++ tailWord_5403384).sum := by decide
  have hdescent : baseEnd_5403384 < baseStart_5403384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403388 : List Nat := [2, 2, 2, 1, 3, 3, 1, 3, 2, 4]
def baseStart_5403388 : Nat := 118140960795 + 5403388 * 2 ^ 59
def prefixEnd_5403388 : Nat := 4983230072969 + 3 ^ 40 * 5403388 * 2
def baseEnd_5403388 : Nat := 924845068912136817766759

theorem tailTrace_5403388 : CollatzResearch.WordTrace tailWord_5403388 prefixEnd_5403388 924845068912136817766759 := by
  unfold tailWord_5403388
  simp only [CollatzResearch.WordTrace]
  refine ⟨98538875474227788022821409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131385167298970384030428545 98538875474227788022821409)
  ·
    refine ⟨73904156605670841017116057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98538875474227788022821409 73904156605670841017116057)
    ·
      refine ⟨55428117454253130762837043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73904156605670841017116057 55428117454253130762837043)
      ·
        refine ⟨83142176181379696144255565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55428117454253130762837043 83142176181379696144255565)
        ·
          refine ⟨31178316068017386054095837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83142176181379696144255565 31178316068017386054095837)
          ·
            refine ⟨11691868525506519770285939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31178316068017386054095837 11691868525506519770285939)
            ·
              refine ⟨17537802788259779655428909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11691868525506519770285939 17537802788259779655428909)
              ·
                refine ⟨6576676045597417370785841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17537802788259779655428909 6576676045597417370785841)
                ·
                  refine ⟨4932507034198063028089381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6576676045597417370785841 4932507034198063028089381)
                  ·
                    refine ⟨924845068912136817766759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4932507034198063028089381 924845068912136817766759)
                    ·
                      rfl

theorem cell23_5403388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_5403388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403388 prefixEnd_5403388 := by exact prefixLift 5403388
  have htrace : WordTrace (prefixWord ++ tailWord_5403388) baseStart_5403388 baseEnd_5403388 := by
    simpa [prefixWord, tailWord_5403388, baseEnd_5403388] using wordTrace_append hprefix tailTrace_5403388
  have hstable : (prefixWord ++ tailWord_5403388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403388).length < 2 ^ (prefixWord ++ tailWord_5403388).sum := by decide
  have hdescent : baseEnd_5403388 < baseStart_5403388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403411 : List Nat := [1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 3]
def baseStart_5403411 : Nat := 118140960795 + 5403411 * 2 ^ 59
def prefixEnd_5403411 : Nat := 4983230072969 + 3 ^ 40 * 5403411 * 2
def baseEnd_5403411 : Nat := 2774547016791463863312671

theorem tailTrace_5403411 : CollatzResearch.WordTrace tailWord_5403411 prefixEnd_5403411 2774547016791463863312671 := by
  unfold tailWord_5403411
  simp only [CollatzResearch.WordTrace]
  refine ⟨197078589827372250973730087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131385726551581500649153391 197078589827372250973730087)
  ·
    refine ⟨295617884741058376460595131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197078589827372250973730087 295617884741058376460595131)
    ·
      refine ⟨443426827111587564690892697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295617884741058376460595131 443426827111587564690892697)
      ·
        refine ⟨332570120333690673518169523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 443426827111587564690892697 332570120333690673518169523)
        ·
          refine ⟨498855180500536010277254285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332570120333690673518169523 498855180500536010277254285)
          ·
            refine ⟨187070692687701003853970357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 498855180500536010277254285 187070692687701003853970357)
            ·
              refine ⟨17537877439471969111309721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 187070692687701003853970357 17537877439471969111309721)
              ·
                refine ⟨13153408079603976833482291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17537877439471969111309721 13153408079603976833482291)
                ·
                  refine ⟨19730112119405965250223437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13153408079603976833482291 19730112119405965250223437)
                  ·
                    refine ⟨7398792044777236968833789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19730112119405965250223437 7398792044777236968833789)
                    ·
                      refine ⟨2774547016791463863312671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7398792044777236968833789 2774547016791463863312671)
                      ·
                        rfl

theorem cell23_5403411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 3].length) (baseStart_5403411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403411 prefixEnd_5403411 := by exact prefixLift 5403411
  have htrace : WordTrace (prefixWord ++ tailWord_5403411) baseStart_5403411 baseEnd_5403411 := by
    simpa [prefixWord, tailWord_5403411, baseEnd_5403411] using wordTrace_append hprefix tailTrace_5403411
  have hstable : (prefixWord ++ tailWord_5403411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403411).length < 2 ^ (prefixWord ++ tailWord_5403411).sum := by decide
  have hdescent : baseEnd_5403411 < baseStart_5403411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403415 : List Nat := [1, 1, 3, 4, 4, 1, 1, 1, 1, 1, 5]
def baseStart_5403415 : Nat := 118140960795 + 5403415 * 2 ^ 59
def prefixEnd_5403415 : Nat := 4983230072969 + 3 ^ 40 * 5403415 * 2
def baseEnd_5403415 : Nat := 2774549070714081847662653

theorem tailTrace_5403415 : CollatzResearch.WordTrace tailWord_5403415 prefixEnd_5403415 2774549070714081847662653 := by
  unfold tailWord_5403415
  simp only [CollatzResearch.WordTrace]
  refine ⟨197078735719357759656875699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131385823812905173104583799 197078735719357759656875699)
  ·
    refine ⟨295618103579036639485313549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197078735719357759656875699 295618103579036639485313549)
    ·
      refine ⟨110856788842138739806992581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295618103579036639485313549 110856788842138739806992581)
      ·
        refine ⟨20785647907901013713811109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110856788842138739806992581 20785647907901013713811109)
        ·
          refine ⟨3897308982731440071339583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20785647907901013713811109 3897308982731440071339583)
          ·
            refine ⟨5845963474097160107009375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3897308982731440071339583 5845963474097160107009375)
            ·
              refine ⟨8768945211145740160514063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5845963474097160107009375 8768945211145740160514063)
              ·
                refine ⟨13153417816718610240771095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8768945211145740160514063 13153417816718610240771095)
                ·
                  refine ⟨19730126725077915361156643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13153417816718610240771095 19730126725077915361156643)
                  ·
                    refine ⟨29595190087616873041734965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19730126725077915361156643 29595190087616873041734965)
                    ·
                      refine ⟨2774549070714081847662653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29595190087616873041734965 2774549070714081847662653)
                      ·
                        rfl

theorem cell23_5403415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_5403415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403415 prefixEnd_5403415 := by exact prefixLift 5403415
  have htrace : WordTrace (prefixWord ++ tailWord_5403415) baseStart_5403415 baseEnd_5403415 := by
    simpa [prefixWord, tailWord_5403415, baseEnd_5403415] using wordTrace_append hprefix tailTrace_5403415
  have hstable : (prefixWord ++ tailWord_5403415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403415).length < 2 ^ (prefixWord ++ tailWord_5403415).sum := by decide
  have hdescent : baseEnd_5403415 < baseStart_5403415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403445 : List Nat := [1, 3, 3, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_5403445 : Nat := 118140960795 + 5403445 * 2 ^ 59
def prefixEnd_5403445 : Nat := 4983230072969 + 3 ^ 40 * 5403445 * 2
def baseEnd_5403445 : Nat := 2774564475133716730287515

theorem tailTrace_5403445 : CollatzResearch.WordTrace tailWord_5403445 prefixEnd_5403445 2774564475133716730287515 := by
  unfold tailWord_5403445
  simp only [CollatzResearch.WordTrace]
  refine ⟨197079829909249074780467789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131386553272832716520311859 197079829909249074780467789)
  ·
    refine ⟨73904936215968403042675421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197079829909249074780467789 73904936215968403042675421)
    ·
      refine ⟨27714351080988151141003283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73904936215968403042675421 27714351080988151141003283)
      ·
        refine ⟨41571526621482226711504925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27714351080988151141003283 41571526621482226711504925)
        ·
          refine ⟨15589322483055835016814347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41571526621482226711504925 15589322483055835016814347)
          ·
            refine ⟨23383983724583752525221521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15589322483055835016814347 23383983724583752525221521)
            ·
              refine ⟨17537987793437814393916141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23383983724583752525221521 17537987793437814393916141)
              ·
                refine ⟨6576745422539180397718553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17537987793437814393916141 6576745422539180397718553)
                ·
                  refine ⟨4932559066904385298288915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6576745422539180397718553 4932559066904385298288915)
                  ·
                    refine ⟨7398838600356577947433373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4932559066904385298288915 7398838600356577947433373)
                    ·
                      refine ⟨2774564475133716730287515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7398838600356577947433373 2774564475133716730287515)
                      ·
                        rfl

theorem cell23_5403445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_5403445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403445 prefixEnd_5403445 := by exact prefixLift 5403445
  have htrace : WordTrace (prefixWord ++ tailWord_5403445) baseStart_5403445 baseEnd_5403445 := by
    simpa [prefixWord, tailWord_5403445, baseEnd_5403445] using wordTrace_append hprefix tailTrace_5403445
  have hstable : (prefixWord ++ tailWord_5403445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403445).length < 2 ^ (prefixWord ++ tailWord_5403445).sum := by decide
  have hdescent : baseEnd_5403445 < baseStart_5403445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403481 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 2, 2, 4]
def baseStart_5403481 : Nat := 118140960795 + 5403481 * 2 ^ 59
def prefixEnd_5403481 : Nat := 4983230072969 + 3 ^ 40 * 5403481 * 2
def baseEnd_5403481 : Nat := 2774582960437278589437349

theorem tailTrace_5403481 : CollatzResearch.WordTrace tailWord_5403481 prefixEnd_5403481 2774582960437278589437349 := by
  unfold tailWord_5403481
  simp only [CollatzResearch.WordTrace]
  refine ⟨197081142937118652928778297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131387428624745768619185531 197081142937118652928778297)
  ·
    refine ⟨147810857202838989696583723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197081142937118652928778297 147810857202838989696583723)
    ·
      refine ⟨221716285804258484544875585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147810857202838989696583723 221716285804258484544875585)
      ·
        refine ⟨166287214353193863408656689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221716285804258484544875585 166287214353193863408656689)
        ·
          refine ⟨124715410764895397556492517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166287214353193863408656689 124715410764895397556492517)
          ·
            refine ⟨23384139518417887041842347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124715410764895397556492517 23384139518417887041842347)
            ·
              refine ⟨35076209277626830562763521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23384139518417887041842347 35076209277626830562763521)
              ·
                refine ⟨26307156958220122922072641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35076209277626830562763521 26307156958220122922072641)
                ·
                  refine ⟨19730367718665092191554481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26307156958220122922072641 19730367718665092191554481)
                  ·
                    refine ⟨14797775788998819143665861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19730367718665092191554481 14797775788998819143665861)
                    ·
                      refine ⟨2774582960437278589437349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14797775788998819143665861 2774582960437278589437349)
                      ·
                        rfl

theorem cell23_5403481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_5403481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403481 prefixEnd_5403481 := by exact prefixLift 5403481
  have htrace : WordTrace (prefixWord ++ tailWord_5403481) baseStart_5403481 baseEnd_5403481 := by
    simpa [prefixWord, tailWord_5403481, baseEnd_5403481] using wordTrace_append hprefix tailTrace_5403481
  have hstable : (prefixWord ++ tailWord_5403481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403481).length < 2 ^ (prefixWord ++ tailWord_5403481).sum := by decide
  have hdescent : baseEnd_5403481 < baseStart_5403481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403491 : List Nat := [1, 1, 1, 5, 3, 1, 1, 3, 7]
def baseStart_5403491 : Nat := 118140960795 + 5403491 * 2 ^ 59
def prefixEnd_5403491 : Nat := 4983230072969 + 3 ^ 40 * 5403491 * 2
def baseEnd_5403491 : Nat := 308287566138202616701367

theorem tailTrace_5403491 : CollatzResearch.WordTrace tailWord_5403491 prefixEnd_5403491 308287566138202616701367 := by
  unfold tailWord_5403491
  simp only [CollatzResearch.WordTrace]
  refine ⟨197081507667082424636642327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131387671778054949757761551 197081507667082424636642327)
  ·
    refine ⟨295622261500623636954963491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197081507667082424636642327 295622261500623636954963491)
    ·
      refine ⟨443433392250935455432445237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295622261500623636954963491 443433392250935455432445237)
      ·
        refine ⟨41571880523525198946791741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 443433392250935455432445237 41571880523525198946791741)
        ·
          refine ⟨15589455196321949605046903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41571880523525198946791741 15589455196321949605046903)
          ·
            refine ⟨23384182794482924407570355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15589455196321949605046903 23384182794482924407570355)
            ·
              refine ⟨35076274191724386611355533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23384182794482924407570355 35076274191724386611355533)
              ·
                refine ⟨13153602821896644979258325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35076274191724386611355533 13153602821896644979258325)
                ·
                  refine ⟨308287566138202616701367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13153602821896644979258325 308287566138202616701367)
                  ·
                    rfl

theorem cell23_5403491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 7].length) (baseStart_5403491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403491 prefixEnd_5403491 := by exact prefixLift 5403491
  have htrace : WordTrace (prefixWord ++ tailWord_5403491) baseStart_5403491 baseEnd_5403491 := by
    simpa [prefixWord, tailWord_5403491, baseEnd_5403491] using wordTrace_append hprefix tailTrace_5403491
  have hstable : (prefixWord ++ tailWord_5403491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403491).length < 2 ^ (prefixWord ++ tailWord_5403491).sum := by decide
  have hdescent : baseEnd_5403491 < baseStart_5403491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403522 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_5403522 : Nat := 118140960795 + 5403522 * 2 ^ 59
def prefixEnd_5403522 : Nat := 4983230072969 + 3 ^ 40 * 5403522 * 2
def baseEnd_5403522 : Nat := 2774604013144112929024661

theorem tailTrace_5403522 : CollatzResearch.WordTrace tailWord_5403522 prefixEnd_5403522 2774604013144112929024661 := by
  unfold tailWord_5403522
  simp only [CollatzResearch.WordTrace]
  refine ⟨49270659582492529232755205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131388425553313411287347213 49270659582492529232755205)
  ·
    refine ⟨9238248671717349231141601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49270659582492529232755205 9238248671717349231141601)
    ·
      refine ⟨6928686503788011923356201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9238248671717349231141601 6928686503788011923356201)
      ·
        refine ⟨5196514877841008942517151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6928686503788011923356201 5196514877841008942517151)
        ·
          refine ⟨7794772316761513413775727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5196514877841008942517151 7794772316761513413775727)
          ·
            refine ⟨11692158475142270120663591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7794772316761513413775727 11692158475142270120663591)
            ·
              refine ⟨17538237712713405180995387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11692158475142270120663591 17538237712713405180995387)
              ·
                refine ⟨26307356569070107771493081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17538237712713405180995387 26307356569070107771493081)
                ·
                  refine ⟨19730517426802580828619811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26307356569070107771493081 19730517426802580828619811)
                  ·
                    refine ⟨29595776140203871242929717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19730517426802580828619811 29595776140203871242929717)
                    ·
                      refine ⟨2774604013144112929024661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29595776140203871242929717 2774604013144112929024661)
                      ·
                        rfl

theorem cell23_5403522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_5403522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403522 prefixEnd_5403522 := by exact prefixLift 5403522
  have htrace : WordTrace (prefixWord ++ tailWord_5403522) baseStart_5403522 baseEnd_5403522 := by
    simpa [prefixWord, tailWord_5403522, baseEnd_5403522] using wordTrace_append hprefix tailTrace_5403522
  have hstable : (prefixWord ++ tailWord_5403522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403522).length < 2 ^ (prefixWord ++ tailWord_5403522).sum := by decide
  have hdescent : baseEnd_5403522 < baseStart_5403522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403525 : List Nat := [1, 3, 1, 1, 3, 5, 1, 3, 5]
def baseStart_5403525 : Nat := 118140960795 + 5403525 * 2 ^ 59
def prefixEnd_5403525 : Nat := 4983230072969 + 3 ^ 40 * 5403525 * 2
def baseEnd_5403525 : Nat := 308289505954008490809683

theorem tailTrace_5403525 : CollatzResearch.WordTrace tailWord_5403525 prefixEnd_5403525 308289505954008490809683 := by
  unfold tailWord_5403525
  simp only [CollatzResearch.WordTrace]
  refine ⟨197082747748959248443380029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131388498499306165628920019 197082747748959248443380029)
  ·
    refine ⟨73906030405859718166267511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197082747748959248443380029 73906030405859718166267511)
    ·
      refine ⟨110859045608789577249401267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73906030405859718166267511 110859045608789577249401267)
      ·
        refine ⟨166288568413184365874101901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110859045608789577249401267 166288568413184365874101901)
        ·
          refine ⟨62358213154944137202788213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166288568413184365874101901 62358213154944137202788213)
          ·
            refine ⟨5846082483276012862761395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62358213154944137202788213 5846082483276012862761395)
            ·
              refine ⟨8769123724914019294142093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5846082483276012862761395 8769123724914019294142093)
              ·
                refine ⟨3288421396842757235303285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8769123724914019294142093 3288421396842757235303285)
                ·
                  refine ⟨308289505954008490809683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3288421396842757235303285 308289505954008490809683)
                  ·
                    rfl

theorem cell23_5403525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 5].length) (baseStart_5403525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403525 prefixEnd_5403525 := by exact prefixLift 5403525
  have htrace : WordTrace (prefixWord ++ tailWord_5403525) baseStart_5403525 baseEnd_5403525 := by
    simpa [prefixWord, tailWord_5403525, baseEnd_5403525] using wordTrace_append hprefix tailTrace_5403525
  have hstable : (prefixWord ++ tailWord_5403525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403525).length < 2 ^ (prefixWord ++ tailWord_5403525).sum := by decide
  have hdescent : baseEnd_5403525 < baseStart_5403525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403542 : List Nat := [5, 3, 1, 1, 1, 1, 3, 1, 7]
def baseStart_5403542 : Nat := 118140960795 + 5403542 * 2 ^ 59
def prefixEnd_5403542 : Nat := 4983230072969 + 3 ^ 40 * 5403542 * 2
def baseEnd_5403542 : Nat := 308290475861911427863841

theorem tailTrace_5403542 : CollatzResearch.WordTrace tailWord_5403542 prefixEnd_5403542 308290475861911427863841 := by
  unfold tailWord_5403542
  simp only [CollatzResearch.WordTrace]
  refine ⟨12317710486868603771671805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131388911859931773564499253 12317710486868603771671805)
  ·
    refine ⟨4619141432575726414376927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12317710486868603771671805 4619141432575726414376927)
    ·
      refine ⟨6928712148863589621565391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4619141432575726414376927 6928712148863589621565391)
      ·
        refine ⟨10393068223295384432348087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6928712148863589621565391 10393068223295384432348087)
        ·
          refine ⟨15589602334943076648522131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10393068223295384432348087 15589602334943076648522131)
          ·
            refine ⟨23384403502414614972783197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15589602334943076648522131 23384403502414614972783197)
            ·
              refine ⟨8769151313405480614793699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23384403502414614972783197 8769151313405480614793699)
              ·
                refine ⟨13153726970108220922190549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8769151313405480614793699 13153726970108220922190549)
                ·
                  refine ⟨308290475861911427863841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13153726970108220922190549 308290475861911427863841)
                  ·
                    rfl

theorem cell23_5403542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_5403542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403542 prefixEnd_5403542 := by exact prefixLift 5403542
  have htrace : WordTrace (prefixWord ++ tailWord_5403542) baseStart_5403542 baseEnd_5403542 := by
    simpa [prefixWord, tailWord_5403542, baseEnd_5403542] using wordTrace_append hprefix tailTrace_5403542
  have hstable : (prefixWord ++ tailWord_5403542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403542).length < 2 ^ (prefixWord ++ tailWord_5403542).sum := by decide
  have hdescent : baseEnd_5403542 < baseStart_5403542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
