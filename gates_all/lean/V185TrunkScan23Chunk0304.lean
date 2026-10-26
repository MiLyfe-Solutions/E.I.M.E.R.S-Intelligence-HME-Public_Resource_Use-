import V185TrunkScan23Chunk0303

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1798079 : List Nat := [1, 1, 2, 2, 2, 1, 7, 7]
def baseStart_1798079 : Nat := 118140960795 + 1798079 * 2 ^ 59
def prefixEnd_1798079 : Nat := 4983230072969 + 3 ^ 40 * 1798079 * 2
def baseEnd_1798079 : Nat := 34195510435399101531233

theorem tailTrace_1798079 : CollatzResearch.WordTrace tailWord_1798079 prefixEnd_1798079 34195510435399101531233 := by
  unfold tailWord_1798079
  simp only [CollatzResearch.WordTrace]
  refine ⟨65581328852874345289829291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43720885901916230193219527 65581328852874345289829291)
  ·
    refine ⟨98371993279311517934743937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65581328852874345289829291 98371993279311517934743937)
    ·
      refine ⟨73778994959483638451057953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98371993279311517934743937 73778994959483638451057953)
      ·
        refine ⟨55334246219612728838293465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73778994959483638451057953 55334246219612728838293465)
        ·
          refine ⟨41500684664709546628720099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55334246219612728838293465 41500684664709546628720099)
          ·
            refine ⟨62251026997064319943080149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41500684664709546628720099 62251026997064319943080149)
            ·
              refine ⟨1459008445243694998665941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 62251026997064319943080149 1459008445243694998665941)
              ·
                refine ⟨34195510435399101531233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1459008445243694998665941 34195510435399101531233)
                ·
                  rfl

theorem cell23_1798079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 7].length) (baseStart_1798079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798079 prefixEnd_1798079 := by exact prefixLift 1798079
  have htrace : WordTrace (prefixWord ++ tailWord_1798079) baseStart_1798079 baseEnd_1798079 := by
    simpa [prefixWord, tailWord_1798079, baseEnd_1798079] using wordTrace_append hprefix tailTrace_1798079
  have hstable : (prefixWord ++ tailWord_1798079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798079).length < 2 ^ (prefixWord ++ tailWord_1798079).sum := by decide
  have hdescent : baseEnd_1798079 < baseStart_1798079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798090 : List Nat := [3, 1, 2, 1, 2, 1, 3, 5, 1, 2, 2]
def baseStart_1798090 : Nat := 118140960795 + 1798090 * 2 ^ 59
def prefixEnd_1798090 : Nat := 4983230072969 + 3 ^ 40 * 1798090 * 2
def baseEnd_1798090 : Nat := 923284430042975198305741

theorem tailTrace_1798090 : CollatzResearch.WordTrace tailWord_1798090 prefixEnd_1798090 923284430042975198305741 := by
  unfold tailWord_1798090
  simp only [CollatzResearch.WordTrace]
  refine ⟨16395432513958623542119931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43721153370556329445653149 16395432513958623542119931)
  ·
    refine ⟨24593148770937935313179897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16395432513958623542119931 24593148770937935313179897)
    ·
      refine ⟨18444861578203451484884923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24593148770937935313179897 18444861578203451484884923)
      ·
        refine ⟨27667292367305177227327385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18444861578203451484884923 27667292367305177227327385)
        ·
          refine ⟨20750469275478882920495539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27667292367305177227327385 20750469275478882920495539)
          ·
            refine ⟨31125703913218324380743309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20750469275478882920495539 31125703913218324380743309)
            ·
              refine ⟨11672138967456871642778741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31125703913218324380743309 11672138967456871642778741)
              ·
                refine ⟨1094263028199081716510507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11672138967456871642778741 1094263028199081716510507)
                ·
                  refine ⟨1641394542298622574765761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1094263028199081716510507 1641394542298622574765761)
                  ·
                    refine ⟨1231045906723966931074321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1641394542298622574765761 1231045906723966931074321)
                    ·
                      refine ⟨923284430042975198305741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231045906723966931074321 923284430042975198305741)
                      ·
                        rfl

theorem cell23_1798090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 1, 2, 2].length) (baseStart_1798090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798090 prefixEnd_1798090 := by exact prefixLift 1798090
  have htrace : WordTrace (prefixWord ++ tailWord_1798090) baseStart_1798090 baseEnd_1798090 := by
    simpa [prefixWord, tailWord_1798090, baseEnd_1798090] using wordTrace_append hprefix tailTrace_1798090
  have hstable : (prefixWord ++ tailWord_1798090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798090).length < 2 ^ (prefixWord ++ tailWord_1798090).sum := by decide
  have hdescent : baseEnd_1798090 < baseStart_1798090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798149 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 1, 3, 5]
def baseStart_1798149 : Nat := 118140960795 + 1798149 * 2 ^ 59
def prefixEnd_1798149 : Nat := 4983230072969 + 3 ^ 40 * 1798149 * 2
def baseEnd_1798149 : Nat := 923314725401590467467969

theorem tailTrace_1798149 : CollatzResearch.WordTrace tailWord_1798149 prefixEnd_1798149 923314725401590467467969 := by
  unfold tailWord_1798149
  simp only [CollatzResearch.WordTrace]
  refine ⟨65583881962620747244877501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43722587975080498163251667 65583881962620747244877501)
  ·
    refine ⟨24593955735982780216829063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65583881962620747244877501 24593955735982780216829063)
    ·
      refine ⟨36890933603974170325243595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24593955735982780216829063 36890933603974170325243595)
      ·
        refine ⟨55336400405961255487865393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36890933603974170325243595 55336400405961255487865393)
        ·
          refine ⟨41502300304470941615899045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55336400405961255487865393 41502300304470941615899045)
          ·
            refine ⟨7781681307088301552981071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41502300304470941615899045 7781681307088301552981071)
            ·
              refine ⟨11672521960632452329471607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7781681307088301552981071 11672521960632452329471607)
              ·
                refine ⟨17508782940948678494207411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11672521960632452329471607 17508782940948678494207411)
                ·
                  refine ⟨26263174411423017741311117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17508782940948678494207411 26263174411423017741311117)
                  ·
                    refine ⟨9848690404283631652991669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26263174411423017741311117 9848690404283631652991669)
                    ·
                      refine ⟨923314725401590467467969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9848690404283631652991669 923314725401590467467969)
                      ·
                        rfl

theorem cell23_1798149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_1798149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798149 prefixEnd_1798149 := by exact prefixLift 1798149
  have htrace : WordTrace (prefixWord ++ tailWord_1798149) baseStart_1798149 baseEnd_1798149 := by
    simpa [prefixWord, tailWord_1798149, baseEnd_1798149] using wordTrace_append hprefix tailTrace_1798149
  have hstable : (prefixWord ++ tailWord_1798149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798149).length < 2 ^ (prefixWord ++ tailWord_1798149).sum := by decide
  have hdescent : baseEnd_1798149 < baseStart_1798149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798163 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 4, 2, 2]
def baseStart_1798163 : Nat := 118140960795 + 1798163 * 2 ^ 59
def prefixEnd_1798163 : Nat := 4983230072969 + 3 ^ 40 * 1798163 * 2
def baseEnd_1798163 : Nat := 923321914130753412692905

theorem tailTrace_1798163 : CollatzResearch.WordTrace tailWord_1798163 prefixEnd_1798163 923321914130753412692905 := by
  unfold tailWord_1798163
  simp only [CollatzResearch.WordTrace]
  refine ⟨65584392584570027635887143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43722928389713351757258095 65584392584570027635887143)
  ·
    refine ⟨98376588876855041453830715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65584392584570027635887143 98376588876855041453830715)
    ·
      refine ⟨147564883315282562180746073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98376588876855041453830715 147564883315282562180746073)
      ·
        refine ⟨110673662486461921635559555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147564883315282562180746073 110673662486461921635559555)
        ·
          refine ⟨166010493729692882453339333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110673662486461921635559555 166010493729692882453339333)
          ·
            refine ⟨31126967574317415460001125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166010493729692882453339333 31126967574317415460001125)
            ·
              refine ⟨5836306420184515398750211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31126967574317415460001125 5836306420184515398750211)
              ·
                refine ⟨8754459630276773098125317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5836306420184515398750211 8754459630276773098125317)
                ·
                  refine ⟨1641461180676894955898497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8754459630276773098125317 1641461180676894955898497)
                  ·
                    refine ⟨1231095885507671216923873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1641461180676894955898497 1231095885507671216923873)
                    ·
                      refine ⟨923321914130753412692905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231095885507671216923873 923321914130753412692905)
                      ·
                        rfl

theorem cell23_1798163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 2, 2].length) (baseStart_1798163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798163 prefixEnd_1798163 := by exact prefixLift 1798163
  have htrace : WordTrace (prefixWord ++ tailWord_1798163) baseStart_1798163 baseEnd_1798163 := by
    simpa [prefixWord, tailWord_1798163, baseEnd_1798163] using wordTrace_append hprefix tailTrace_1798163
  have hstable : (prefixWord ++ tailWord_1798163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798163).length < 2 ^ (prefixWord ++ tailWord_1798163).sum := by decide
  have hdescent : baseEnd_1798163 < baseStart_1798163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798184 : List Nat := [2, 1, 5, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_1798184 : Nat := 118140960795 + 1798184 * 2 ^ 59
def prefixEnd_1798184 : Nat := 4983230072969 + 3 ^ 40 * 1798184 * 2
def baseEnd_1798184 : Nat := 923332697224497830530309

theorem tailTrace_1798184 : CollatzResearch.WordTrace tailWord_1798184 prefixEnd_1798184 923332697224497830530309 := by
  unfold tailWord_1798184
  simp only [CollatzResearch.WordTrace]
  refine ⟨32792579258746974111200803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43723439011662632148267737 32792579258746974111200803)
  ·
    refine ⟨49188868888120461166801205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32792579258746974111200803 49188868888120461166801205)
    ·
      refine ⟨4611456458261293234387613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49188868888120461166801205 4611456458261293234387613)
      ·
        refine ⟨1729296171847984962895355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4611456458261293234387613 1729296171847984962895355)
        ·
          refine ⟨2593944257771977444343033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1729296171847984962895355 2593944257771977444343033)
          ·
            refine ⟨1945458193328983083257275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2593944257771977444343033 1945458193328983083257275)
            ·
              refine ⟨2918187289993474624885913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1945458193328983083257275 2918187289993474624885913)
              ·
                refine ⟨2188640467495105968664435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2918187289993474624885913 2188640467495105968664435)
                ·
                  refine ⟨3282960701242658952996653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2188640467495105968664435 3282960701242658952996653)
                  ·
                    refine ⟨1231110262965997107373745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3282960701242658952996653 1231110262965997107373745)
                    ·
                      refine ⟨923332697224497830530309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231110262965997107373745 923332697224497830530309)
                      ·
                        rfl

theorem cell23_1798184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_1798184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798184 prefixEnd_1798184 := by exact prefixLift 1798184
  have htrace : WordTrace (prefixWord ++ tailWord_1798184) baseStart_1798184 baseEnd_1798184 := by
    simpa [prefixWord, tailWord_1798184, baseEnd_1798184] using wordTrace_append hprefix tailTrace_1798184
  have hstable : (prefixWord ++ tailWord_1798184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798184).length < 2 ^ (prefixWord ++ tailWord_1798184).sum := by decide
  have hdescent : baseEnd_1798184 < baseStart_1798184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798199 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 1, 7]
def baseStart_1798199 : Nat := 118140960795 + 1798199 * 2 ^ 59
def prefixEnd_1798199 : Nat := 4983230072969 + 3 ^ 40 * 1798199 * 2
def baseEnd_1798199 : Nat := 307780133144771757280913

theorem tailTrace_1798199 : CollatzResearch.WordTrace tailWord_1798199 prefixEnd_1798199 307780133144771757280913 := by
  unfold tailWord_1798199
  simp only [CollatzResearch.WordTrace]
  refine ⟨65585705612439605784197651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43723803741626403856131767 65585705612439605784197651)
  ·
    refine ⟨98378558418659408676296477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65585705612439605784197651 98378558418659408676296477)
    ·
      refine ⟨36891959406997278253611179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98378558418659408676296477 36891959406997278253611179)
      ·
        refine ⟨55337939110495917380416769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36891959406997278253611179 55337939110495917380416769)
        ·
          refine ⟨41503454332871938035312577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55337939110495917380416769 41503454332871938035312577)
          ·
            refine ⟨31127590749653953526484433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41503454332871938035312577 31127590749653953526484433)
            ·
              refine ⟨23345693062240465144863325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31127590749653953526484433 23345693062240465144863325)
              ·
                refine ⟨8754634898340174429323747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23345693062240465144863325 8754634898340174429323747)
                ·
                  refine ⟨13131952347510261643985621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8754634898340174429323747 13131952347510261643985621)
                  ·
                    refine ⟨307780133144771757280913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13131952347510261643985621 307780133144771757280913)
                    ·
                      rfl

theorem cell23_1798199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_1798199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798199 prefixEnd_1798199 := by exact prefixLift 1798199
  have htrace : WordTrace (prefixWord ++ tailWord_1798199) baseStart_1798199 baseEnd_1798199 := by
    simpa [prefixWord, tailWord_1798199, baseEnd_1798199] using wordTrace_append hprefix tailTrace_1798199
  have hstable : (prefixWord ++ tailWord_1798199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798199).length < 2 ^ (prefixWord ++ tailWord_1798199).sum := by decide
  have hdescent : baseEnd_1798199 < baseStart_1798199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798214 : List Nat := [6, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_1798214 : Nat := 118140960795 + 1798214 * 2 ^ 59
def prefixEnd_1798214 : Nat := 4983230072969 + 3 ^ 40 * 1798214 * 2
def baseEnd_1798214 : Nat := 923348101644132713155171

theorem tailTrace_1798214 : CollatzResearch.WordTrace tailWord_1798214 prefixEnd_1798214 923348101644132713155171 := by
  unfold tailWord_1798214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2049570397105789479562303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43724168471590175563995797 2049570397105789479562303)
  ·
    refine ⟨3074355595658684219343455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2049570397105789479562303 3074355595658684219343455)
    ·
      refine ⟨4611533393488026329015183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3074355595658684219343455 4611533393488026329015183)
      ·
        refine ⟨6917300090232039493522775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4611533393488026329015183 6917300090232039493522775)
        ·
          refine ⟨10375950135348059240284163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6917300090232039493522775 10375950135348059240284163)
          ·
            refine ⟨15563925203022088860426245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10375950135348059240284163 15563925203022088860426245)
            ·
              refine ⟨2918235975566641661329921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15563925203022088860426245 2918235975566641661329921)
              ·
                refine ⟨2188676981674981245997441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2918235975566641661329921 2188676981674981245997441)
                ·
                  refine ⟨1641507736256235934498081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2188676981674981245997441 1641507736256235934498081)
                  ·
                    refine ⟨1231130802192176950873561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1641507736256235934498081 1231130802192176950873561)
                    ·
                      refine ⟨923348101644132713155171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231130802192176950873561 923348101644132713155171)
                      ·
                        rfl

theorem cell23_1798214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_1798214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798214 prefixEnd_1798214 := by exact prefixLift 1798214
  have htrace : WordTrace (prefixWord ++ tailWord_1798214) baseStart_1798214 baseEnd_1798214 := by
    simpa [prefixWord, tailWord_1798214, baseEnd_1798214] using wordTrace_append hprefix tailTrace_1798214
  have hstable : (prefixWord ++ tailWord_1798214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798214).length < 2 ^ (prefixWord ++ tailWord_1798214).sum := by decide
  have hdescent : baseEnd_1798214 < baseStart_1798214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798230 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_1798230 : Nat := 118140960795 + 1798230 * 2 ^ 59
def prefixEnd_1798230 : Nat := 4983230072969 + 3 ^ 40 * 1798230 * 2
def baseEnd_1798230 : Nat := 923356317334604650555097

theorem tailTrace_1798230 : CollatzResearch.WordTrace tailWord_1798230 prefixEnd_1798230 923356317334604650555097 := by
  unfold tailWord_1798230
  simp only [CollatzResearch.WordTrace]
  refine ⟨4099177267207956129911009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43724557516884865385717429 4099177267207956129911009)
  ·
    refine ⟨3074382950405967097433257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4099177267207956129911009 3074382950405967097433257)
    ·
      refine ⟨2305787212804475323074943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3074382950405967097433257 2305787212804475323074943)
      ·
        refine ⟨3458680819206712984612415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2305787212804475323074943 3458680819206712984612415)
        ·
          refine ⟨5188021228810069476918623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3458680819206712984612415 5188021228810069476918623)
          ·
            refine ⟨7782031843215104215377935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5188021228810069476918623 7782031843215104215377935)
            ·
              refine ⟨11673047764822656323066903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7782031843215104215377935 11673047764822656323066903)
              ·
                refine ⟨17509571647233984484600355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11673047764822656323066903 17509571647233984484600355)
                ·
                  refine ⟨26264357470850976726900533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17509571647233984484600355 26264357470850976726900533)
                  ·
                    refine ⟨2462283512892279068146925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26264357470850976726900533 2462283512892279068146925)
                    ·
                      refine ⟨923356317334604650555097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2462283512892279068146925 923356317334604650555097)
                      ·
                        rfl

theorem cell23_1798230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_1798230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798230 prefixEnd_1798230 := by exact prefixLift 1798230
  have htrace : WordTrace (prefixWord ++ tailWord_1798230) baseStart_1798230 baseEnd_1798230 := by
    simpa [prefixWord, tailWord_1798230, baseEnd_1798230] using wordTrace_append hprefix tailTrace_1798230
  have hstable : (prefixWord ++ tailWord_1798230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798230).length < 2 ^ (prefixWord ++ tailWord_1798230).sum := by decide
  have hdescent : baseEnd_1798230 < baseStart_1798230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798250 : List Nat := [3, 1, 3, 2, 3, 2, 1, 1, 2, 5]
def baseStart_1798250 : Nat := 118140960795 + 1798250 * 2 ^ 59
def prefixEnd_1798250 : Nat := 4983230072969 + 3 ^ 40 * 1798250 * 2
def baseEnd_1798250 : Nat := 307788862315898190768335

theorem tailTrace_1798250 : CollatzResearch.WordTrace tailWord_1798250 prefixEnd_1798250 307788862315898190768335 := by
  unfold tailWord_1798250
  simp only [CollatzResearch.WordTrace]
  refine ⟨16396891433813710373576051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43725043823503227662869469 16396891433813710373576051)
  ·
    refine ⟨24595337150720565560364077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16396891433813710373576051 24595337150720565560364077)
    ·
      refine ⟨9223251431520212085136529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24595337150720565560364077 9223251431520212085136529)
      ·
        refine ⟨6917438573640159063852397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9223251431520212085136529 6917438573640159063852397)
        ·
          refine ⟨2594039465115059648944649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6917438573640159063852397 2594039465115059648944649)
          ·
            refine ⟨1945529598836294736708487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2594039465115059648944649 1945529598836294736708487)
            ·
              refine ⟨2918294398254442105062731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1945529598836294736708487 2918294398254442105062731)
              ·
                refine ⟨4377441597381663157594097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2918294398254442105062731 4377441597381663157594097)
                ·
                  refine ⟨3283081198036247368195573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4377441597381663157594097 3283081198036247368195573)
                  ·
                    refine ⟨307788862315898190768335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3283081198036247368195573 307788862315898190768335)
                    ·
                      rfl

theorem cell23_1798250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_1798250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798250 prefixEnd_1798250 := by exact prefixLift 1798250
  have htrace : WordTrace (prefixWord ++ tailWord_1798250) baseStart_1798250 baseEnd_1798250 := by
    simpa [prefixWord, tailWord_1798250, baseEnd_1798250] using wordTrace_append hprefix tailTrace_1798250
  have hstable : (prefixWord ++ tailWord_1798250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798250).length < 2 ^ (prefixWord ++ tailWord_1798250).sum := by decide
  have hdescent : baseEnd_1798250 < baseStart_1798250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798253 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 1, 6, 2]
def baseStart_1798253 : Nat := 118140960795 + 1798253 * 2 ^ 59
def prefixEnd_1798253 : Nat := 4983230072969 + 3 ^ 40 * 1798253 * 2
def baseEnd_1798253 : Nat := 923368127389658060567491

theorem tailTrace_1798253 : CollatzResearch.WordTrace tailWord_1798253 prefixEnd_1798253 923368127389658060567491 := by
  unfold tailWord_1798253
  simp only [CollatzResearch.WordTrace]
  refine ⟨65587675154243973006663413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43725116769495982004442275 65587675154243973006663413)
  ·
    refine ⟨6148844545710372469374695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65587675154243973006663413 6148844545710372469374695)
    ·
      refine ⟨9223266818565558704062043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6148844545710372469374695 9223266818565558704062043)
      ·
        refine ⟨13834900227848338056093065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9223266818565558704062043 13834900227848338056093065)
        ·
          refine ⟨10376175170886253542069799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13834900227848338056093065 10376175170886253542069799)
          ·
            refine ⟨15564262756329380313104699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10376175170886253542069799 15564262756329380313104699)
            ·
              refine ⟨23346394134494070469657049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15564262756329380313104699 23346394134494070469657049)
              ·
                refine ⟨17509795600870552852242787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23346394134494070469657049 17509795600870552852242787)
                ·
                  refine ⟨26264693401305829278364181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17509795600870552852242787 26264693401305829278364181)
                  ·
                    refine ⟨1231157503186210747423321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26264693401305829278364181 1231157503186210747423321)
                    ·
                      refine ⟨923368127389658060567491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231157503186210747423321 923368127389658060567491)
                      ·
                        rfl

theorem cell23_1798253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_1798253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798253 prefixEnd_1798253 := by exact prefixLift 1798253
  have htrace : WordTrace (prefixWord ++ tailWord_1798253) baseStart_1798253 baseEnd_1798253 := by
    simpa [prefixWord, tailWord_1798253, baseEnd_1798253] using wordTrace_append hprefix tailTrace_1798253
  have hstable : (prefixWord ++ tailWord_1798253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798253).length < 2 ^ (prefixWord ++ tailWord_1798253).sum := by decide
  have hdescent : baseEnd_1798253 < baseStart_1798253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798276 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 8]
def baseStart_1798276 : Nat := 118140960795 + 1798276 * 2 ^ 59
def prefixEnd_1798276 : Nat := 4983230072969 + 3 ^ 40 * 1798276 * 2
def baseEnd_1798276 : Nat := 102597770827190163397765

theorem tailTrace_1798276 : CollatzResearch.WordTrace tailWord_1798276 prefixEnd_1798276 102597770827190163397765 := by
  unfold tailWord_1798276
  simp only [CollatzResearch.WordTrace]
  refine ⟨32794257016580323967375341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43725676022107098623167121 32794257016580323967375341)
  ·
    refine ⟨12297846381217621487765753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32794257016580323967375341 12297846381217621487765753)
    ·
      refine ⟨9223384785913216115824315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12297846381217621487765753 9223384785913216115824315)
      ·
        refine ⟨13835077178869824173736473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9223384785913216115824315 13835077178869824173736473)
        ·
          refine ⟨10376307884152368130302355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13835077178869824173736473 10376307884152368130302355)
          ·
            refine ⟨15564461826228552195453533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10376307884152368130302355 15564461826228552195453533)
            ·
              refine ⟨5836673184835707073295075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15564461826228552195453533 5836673184835707073295075)
              ·
                refine ⟨8755009777253560609942613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5836673184835707073295075 8755009777253560609942613)
                ·
                  refine ⟨102597770827190163397765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8755009777253560609942613 102597770827190163397765)
                  ·
                    rfl

theorem cell23_1798276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_1798276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798276 prefixEnd_1798276 := by exact prefixLift 1798276
  have htrace : WordTrace (prefixWord ++ tailWord_1798276) baseStart_1798276 baseEnd_1798276 := by
    simpa [prefixWord, tailWord_1798276, baseEnd_1798276] using wordTrace_append hprefix tailTrace_1798276
  have hstable : (prefixWord ++ tailWord_1798276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798276).length < 2 ^ (prefixWord ++ tailWord_1798276).sum := by decide
  have hdescent : baseEnd_1798276 < baseStart_1798276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798280 : List Nat := [2, 1, 3, 4, 1, 2, 2, 1, 3, 4]
def baseStart_1798280 : Nat := 118140960795 + 1798280 * 2 ^ 59
def prefixEnd_1798280 : Nat := 4983230072969 + 3 ^ 40 * 1798280 * 2
def baseEnd_1798280 : Nat := 307793997122443151643289

theorem tailTrace_1798280 : CollatzResearch.WordTrace tailWord_1798280 prefixEnd_1798280 307793997122443151643289 := by
  unfold tailWord_1798280
  simp only [CollatzResearch.WordTrace]
  refine ⟨32794329962573078308948147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43725773283430771078597529 32794329962573078308948147)
  ·
    refine ⟨49191494943859617463422221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32794329962573078308948147 49191494943859617463422221)
    ·
      refine ⟨18446810603947356548783333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49191494943859617463422221 18446810603947356548783333)
      ·
        refine ⟨3458776988240129352896875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18446810603947356548783333 3458776988240129352896875)
        ·
          refine ⟨5188165482360194029345313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3458776988240129352896875 5188165482360194029345313)
          ·
            refine ⟨3891124111770145522008985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5188165482360194029345313 3891124111770145522008985)
            ·
              refine ⟨2918343083827609141506739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3891124111770145522008985 2918343083827609141506739)
              ·
                refine ⟨4377514625741413712260109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2918343083827609141506739 4377514625741413712260109)
                ·
                  refine ⟨1641567984653030142097541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4377514625741413712260109 1641567984653030142097541)
                  ·
                    refine ⟨307793997122443151643289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1641567984653030142097541 307793997122443151643289)
                    ·
                      rfl

theorem cell23_1798280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_1798280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798280 prefixEnd_1798280 := by exact prefixLift 1798280
  have htrace : WordTrace (prefixWord ++ tailWord_1798280) baseStart_1798280 baseEnd_1798280 := by
    simpa [prefixWord, tailWord_1798280, baseEnd_1798280] using wordTrace_append hprefix tailTrace_1798280
  have hstable : (prefixWord ++ tailWord_1798280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798280).length < 2 ^ (prefixWord ++ tailWord_1798280).sum := by decide
  have hdescent : baseEnd_1798280 < baseStart_1798280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798293 : List Nat := [1, 3, 2, 1, 1, 1, 7, 1, 6]
def baseStart_1798293 : Nat := 118140960795 + 1798293 * 2 ^ 59
def prefixEnd_1798293 : Nat := 4983230072969 + 3 ^ 40 * 1798293 * 2
def baseEnd_1798293 : Nat := 102598740735093100451923

theorem tailTrace_1798293 : CollatzResearch.WordTrace tailWord_1798293 prefixEnd_1798293 102598740735093100451923 := by
  unfold tailWord_1798293
  simp only [CollatzResearch.WordTrace]
  refine ⟨65589134074099059838119533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43726089382732706558746355 65589134074099059838119533)
  ·
    refine ⟨24595925277787147439294825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65589134074099059838119533 24595925277787147439294825)
    ·
      refine ⟨18446943958340360579471119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24595925277787147439294825 18446943958340360579471119)
      ·
        refine ⟨27670415937510540869206679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18446943958340360579471119 27670415937510540869206679)
        ·
          refine ⟨41505623906265811303810019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27670415937510540869206679 41505623906265811303810019)
          ·
            refine ⟨62258435859398716955715029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41505623906265811303810019 62258435859398716955715029)
            ·
              refine ⟨1459182090454657428649571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 62258435859398716955715029 1459182090454657428649571)
              ·
                refine ⟨2188773135681986142974357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1459182090454657428649571 2188773135681986142974357)
                ·
                  refine ⟨102598740735093100451923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2188773135681986142974357 102598740735093100451923)
                  ·
                    rfl

theorem cell23_1798293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 6].length) (baseStart_1798293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798293 prefixEnd_1798293 := by exact prefixLift 1798293
  have htrace : WordTrace (prefixWord ++ tailWord_1798293) baseStart_1798293 baseEnd_1798293 := by
    simpa [prefixWord, tailWord_1798293, baseEnd_1798293] using wordTrace_append hprefix tailTrace_1798293
  have hstable : (prefixWord ++ tailWord_1798293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798293).length < 2 ^ (prefixWord ++ tailWord_1798293).sum := by decide
  have hdescent : baseEnd_1798293 < baseStart_1798293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798357 : List Nat := [1, 3, 2, 4, 2, 2, 1, 2, 1, 5]
def baseStart_1798357 : Nat := 118140960795 + 1798357 * 2 ^ 59
def prefixEnd_1798357 : Nat := 4983230072969 + 3 ^ 40 * 1798357 * 2
def baseEnd_1798357 : Nat := 307807176459241884555671

theorem tailTrace_1798357 : CollatzResearch.WordTrace tailWord_1798357 prefixEnd_1798357 307807176459241884555671 := by
  unfold tailWord_1798357
  simp only [CollatzResearch.WordTrace]
  refine ⟨65591468345867198768449325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43727645563911465845632883 65591468345867198768449325)
  ·
    refine ⟨24596800629700199538168497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65591468345867198768449325 24596800629700199538168497)
    ·
      refine ⟨18447600472275149653626373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24596800629700199538168497 18447600472275149653626373)
      ·
        refine ⟨3458925088551590560054945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18447600472275149653626373 3458925088551590560054945)
        ·
          refine ⟨2594193816413692920041209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3458925088551590560054945 2594193816413692920041209)
          ·
            refine ⟨1945645362310269690030907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2594193816413692920041209 1945645362310269690030907)
            ·
              refine ⟨2918468043465404535046361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1945645362310269690030907 2918468043465404535046361)
              ·
                refine ⟨2188851032599053401284771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2918468043465404535046361 2188851032599053401284771)
                ·
                  refine ⟨3283276548898580101927157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2188851032599053401284771 3283276548898580101927157)
                  ·
                    refine ⟨307807176459241884555671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3283276548898580101927157 307807176459241884555671)
                    ·
                      rfl

theorem cell23_1798357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_1798357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798357 prefixEnd_1798357 := by exact prefixLift 1798357
  have htrace : WordTrace (prefixWord ++ tailWord_1798357) baseStart_1798357 baseEnd_1798357 := by
    simpa [prefixWord, tailWord_1798357, baseEnd_1798357] using wordTrace_append hprefix tailTrace_1798357
  have hstable : (prefixWord ++ tailWord_1798357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798357).length < 2 ^ (prefixWord ++ tailWord_1798357).sum := by decide
  have hdescent : baseEnd_1798357 < baseStart_1798357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798360 : List Nat := [2, 1, 2, 2, 4, 1, 3, 2, 1, 1, 4]
def baseStart_1798360 : Nat := 118140960795 + 1798360 * 2 ^ 59
def prefixEnd_1798360 : Nat := 4983230072969 + 3 ^ 40 * 1798360 * 2
def baseEnd_1798360 : Nat := 923423069819689141929499

theorem tailTrace_1798360 : CollatzResearch.WordTrace tailWord_1798360 prefixEnd_1798360 923423069819689141929499 := by
  unfold tailWord_1798360
  simp only [CollatzResearch.WordTrace]
  refine ⟨32795788882428165140404267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43727718509904220187205689 32795788882428165140404267)
  ·
    refine ⟨49193683323642247710606401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32795788882428165140404267 49193683323642247710606401)
    ·
      refine ⟨36895262492731685782954801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49193683323642247710606401 36895262492731685782954801)
      ·
        refine ⟨27671446869548764337216101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36895262492731685782954801 27671446869548764337216101)
        ·
          refine ⟨5188396288040393313228019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27671446869548764337216101 5188396288040393313228019)
          ·
            refine ⟨7782594432060589969842029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5188396288040393313228019 7782594432060589969842029)
            ·
              refine ⟨2918472912022721238690761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7782594432060589969842029 2918472912022721238690761)
              ·
                refine ⟨2188854684017040929018071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2918472912022721238690761 2188854684017040929018071)
                ·
                  refine ⟨3283282026025561393527107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2188854684017040929018071 3283282026025561393527107)
                  ·
                    refine ⟨4924923039038342090290661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3283282026025561393527107 4924923039038342090290661)
                    ·
                      refine ⟨923423069819689141929499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4924923039038342090290661 923423069819689141929499)
                      ·
                        rfl

theorem cell23_1798360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_1798360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798360 prefixEnd_1798360 := by exact prefixLift 1798360
  have htrace : WordTrace (prefixWord ++ tailWord_1798360) baseStart_1798360 baseEnd_1798360 := by
    simpa [prefixWord, tailWord_1798360, baseEnd_1798360] using wordTrace_append hprefix tailTrace_1798360
  have hstable : (prefixWord ++ tailWord_1798360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798360).length < 2 ^ (prefixWord ++ tailWord_1798360).sum := by decide
  have hdescent : baseEnd_1798360 < baseStart_1798360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798373 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 3, 2, 4]
def baseStart_1798373 : Nat := 118140960795 + 1798373 * 2 ^ 59
def prefixEnd_1798373 : Nat := 4983230072969 + 3 ^ 40 * 1798373 * 2
def baseEnd_1798373 : Nat := 923429745068197591066939

theorem tailTrace_1798373 : CollatzResearch.WordTrace tailWord_1798373 prefixEnd_1798373 923429745068197591066939 := by
  unfold tailWord_1798373
  simp only [CollatzResearch.WordTrace]
  refine ⟨65592051913809233501031773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43728034609206155667354515 65592051913809233501031773)
  ·
    refine ⟨24597019467678462562886915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65592051913809233501031773 24597019467678462562886915)
    ·
      refine ⟨36895529201517693844330373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24597019467678462562886915 36895529201517693844330373)
      ·
        refine ⟨6917911725284567595811945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36895529201517693844330373 6917911725284567595811945)
        ·
          refine ⟨5188433793963425696858959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6917911725284567595811945 5188433793963425696858959)
          ·
            refine ⟨7782650690945138545288439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5188433793963425696858959 7782650690945138545288439)
            ·
              refine ⟨11673976036417707817932659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7782650690945138545288439 11673976036417707817932659)
              ·
                refine ⟨17510964054626561726898989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11673976036417707817932659 17510964054626561726898989)
                ·
                  refine ⟨6566611520484960647587121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17510964054626561726898989 6566611520484960647587121)
                  ·
                    refine ⟨4924958640363720485690341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6566611520484960647587121 4924958640363720485690341)
                    ·
                      refine ⟨923429745068197591066939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4924958640363720485690341 923429745068197591066939)
                      ·
                        rfl

theorem cell23_1798373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_1798373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798373 prefixEnd_1798373 := by exact prefixLift 1798373
  have htrace : WordTrace (prefixWord ++ tailWord_1798373) baseStart_1798373 baseEnd_1798373 := by
    simpa [prefixWord, tailWord_1798373, baseEnd_1798373] using wordTrace_append hprefix tailTrace_1798373
  have hstable : (prefixWord ++ tailWord_1798373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798373).length < 2 ^ (prefixWord ++ tailWord_1798373).sum := by decide
  have hdescent : baseEnd_1798373 < baseStart_1798373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798394 : List Nat := [3, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2]
def baseStart_1798394 : Nat := 118140960795 + 1798394 * 2 ^ 59
def prefixEnd_1798394 : Nat := 4983230072969 + 3 ^ 40 * 1798394 * 2
def baseEnd_1798394 : Nat := 923440528161942008904343

theorem tailTrace_1798394 : CollatzResearch.WordTrace tailWord_1798394 prefixEnd_1798394 923440528161942008904343 := by
  unfold tailWord_1798394
  simp only [CollatzResearch.WordTrace]
  refine ⟨16398204461683288521886559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43728545231155436058364157 16398204461683288521886559)
  ·
    refine ⟨24597306692524932782829839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16398204461683288521886559 24597306692524932782829839)
    ·
      refine ⟨36895960038787399174244759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24597306692524932782829839 36895960038787399174244759)
      ·
        refine ⟨55343940058181098761367139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36895960038787399174244759 55343940058181098761367139)
        ·
          refine ⟨83015910087271648142050709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55343940058181098761367139 83015910087271648142050709)
          ·
            refine ⟨3891370785340858506658627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83015910087271648142050709 3891370785340858506658627)
            ·
              refine ⟨5837056178011287759987941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3891370785340858506658627 5837056178011287759987941)
              ·
                refine ⟨1094448033377116454997739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5837056178011287759987941 1094448033377116454997739)
                ·
                  refine ⟨1641672050065674682496609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1094448033377116454997739 1641672050065674682496609)
                  ·
                    refine ⟨1231254037549256011872457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1641672050065674682496609 1231254037549256011872457)
                    ·
                      refine ⟨923440528161942008904343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231254037549256011872457 923440528161942008904343)
                      ·
                        rfl

theorem cell23_1798394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2].length) (baseStart_1798394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798394 prefixEnd_1798394 := by exact prefixLift 1798394
  have htrace : WordTrace (prefixWord ++ tailWord_1798394) baseStart_1798394 baseEnd_1798394 := by
    simpa [prefixWord, tailWord_1798394, baseEnd_1798394] using wordTrace_append hprefix tailTrace_1798394
  have hstable : (prefixWord ++ tailWord_1798394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798394).length < 2 ^ (prefixWord ++ tailWord_1798394).sum := by decide
  have hdescent : baseEnd_1798394 < baseStart_1798394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798407 : List Nat := [1, 1, 4, 5, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1798407 : Nat := 118140960795 + 1798407 * 2 ^ 59
def prefixEnd_1798407 : Nat := 4983230072969 + 3 ^ 40 * 1798407 * 2
def baseEnd_1798407 : Nat := 923447203410450458041783

theorem tailTrace_1798407 : CollatzResearch.WordTrace tailWord_1798407 prefixEnd_1798407 923447203410450458041783 := by
  unfold tailWord_1798407
  simp only [CollatzResearch.WordTrace]
  refine ⟨65593291995686057307769475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43728861330457371538512983 65593291995686057307769475)
  ·
    refine ⟨98389937993529085961654213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65593291995686057307769475 98389937993529085961654213)
    ·
      refine ⟨18448113373786703617810165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98389937993529085961654213 18448113373786703617810165)
      ·
        refine ⟨1729510628792503464169703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18448113373786703617810165 1729510628792503464169703)
        ·
          refine ⟨2594265943188755196254555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1729510628792503464169703 2594265943188755196254555)
          ·
            refine ⟨3891398914783132794381833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2594265943188755196254555 3891398914783132794381833)
            ·
              refine ⟨2918549186087349595786375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3891398914783132794381833 2918549186087349595786375)
              ·
                refine ⟨4377823779131024393679563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2918549186087349595786375 4377823779131024393679563)
                ·
                  refine ⟨6566735668696536590519345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4377823779131024393679563 6566735668696536590519345)
                  ·
                    refine ⟨4925051751522402442889509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6566735668696536590519345 4925051751522402442889509)
                    ·
                      refine ⟨923447203410450458041783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4925051751522402442889509 923447203410450458041783)
                      ·
                        rfl

theorem cell23_1798407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1798407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798407 prefixEnd_1798407 := by exact prefixLift 1798407
  have htrace : WordTrace (prefixWord ++ tailWord_1798407) baseStart_1798407 baseEnd_1798407 := by
    simpa [prefixWord, tailWord_1798407, baseEnd_1798407] using wordTrace_append hprefix tailTrace_1798407
  have hstable : (prefixWord ++ tailWord_1798407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798407).length < 2 ^ (prefixWord ++ tailWord_1798407).sum := by decide
  have hdescent : baseEnd_1798407 < baseStart_1798407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798463 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 4]
def baseStart_1798463 : Nat := 118140960795 + 1798463 * 2 ^ 59
def prefixEnd_1798463 : Nat := 4983230072969 + 3 ^ 40 * 1798463 * 2
def baseEnd_1798463 : Nat := 923475958327102238941525

theorem tailTrace_1798463 : CollatzResearch.WordTrace tailWord_1798463 prefixEnd_1798463 923475958327102238941525 := by
  unfold tailWord_1798463
  simp only [CollatzResearch.WordTrace]
  refine ⟨65595334483483178871808043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43730222988988785914538695 65595334483483178871808043)
  ·
    refine ⟨98393001725224768307712065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65595334483483178871808043 98393001725224768307712065)
    ·
      refine ⟨73794751293918576230784049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98393001725224768307712065 73794751293918576230784049)
      ·
        refine ⟨55346063470438932173088037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73794751293918576230784049 55346063470438932173088037)
        ·
          refine ⟨10377386900707299782454007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55346063470438932173088037 10377386900707299782454007)
          ·
            refine ⟨15566080351060949673681011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10377386900707299782454007 15566080351060949673681011)
            ·
              refine ⟨23349120526591424510521517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15566080351060949673681011 23349120526591424510521517)
              ·
                refine ⟨8755920197471784191445569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23349120526591424510521517 8755920197471784191445569)
                ·
                  refine ⟨6566940148103838143584177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8755920197471784191445569 6566940148103838143584177)
                  ·
                    refine ⟨4925205111077878607688133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6566940148103838143584177 4925205111077878607688133)
                    ·
                      refine ⟨923475958327102238941525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4925205111077878607688133 923475958327102238941525)
                      ·
                        rfl

theorem cell23_1798463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_1798463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798463 prefixEnd_1798463 := by exact prefixLift 1798463
  have htrace : WordTrace (prefixWord ++ tailWord_1798463) baseStart_1798463 baseEnd_1798463 := by
    simpa [prefixWord, tailWord_1798463, baseEnd_1798463] using wordTrace_append hprefix tailTrace_1798463
  have hstable : (prefixWord ++ tailWord_1798463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798463).length < 2 ^ (prefixWord ++ tailWord_1798463).sum := by decide
  have hdescent : baseEnd_1798463 < baseStart_1798463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798467 : List Nat := [1, 1, 1, 3, 1, 3, 2, 5, 2, 2, 2]
def baseStart_1798467 : Nat := 118140960795 + 1798467 * 2 ^ 59
def prefixEnd_1798467 : Nat := 4983230072969 + 3 ^ 40 * 1798467 * 2
def baseEnd_1798467 : Nat := 923478012249720223291507

theorem tailTrace_1798467 : CollatzResearch.WordTrace tailWord_1798467 prefixEnd_1798467 923478012249720223291507 := by
  unfold tailWord_1798467
  simp only [CollatzResearch.WordTrace]
  refine ⟨65595480375468687554953655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43730320250312458369969103 65595480375468687554953655)
  ·
    refine ⟨98393220563203031332430483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65595480375468687554953655 98393220563203031332430483)
    ·
      refine ⟨147589830844804546998645725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98393220563203031332430483 147589830844804546998645725)
      ·
        refine ⟨55346186566801705124492147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147589830844804546998645725 55346186566801705124492147)
        ·
          refine ⟨83019279850202557686738221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55346186566801705124492147 83019279850202557686738221)
          ·
            refine ⟨31132229943825959132526833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83019279850202557686738221 31132229943825959132526833)
            ·
              refine ⟨23349172457869469349395125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31132229943825959132526833 23349172457869469349395125)
              ·
                refine ⟨2188984917925262751505793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23349172457869469349395125 2188984917925262751505793)
                ·
                  refine ⟨1641738688443947063629345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2188984917925262751505793 1641738688443947063629345)
                  ·
                    refine ⟨1231304016332960297722009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1641738688443947063629345 1231304016332960297722009)
                    ·
                      refine ⟨923478012249720223291507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231304016332960297722009 923478012249720223291507)
                      ·
                        rfl

theorem cell23_1798467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 2, 2].length) (baseStart_1798467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798467 prefixEnd_1798467 := by exact prefixLift 1798467
  have htrace : WordTrace (prefixWord ++ tailWord_1798467) baseStart_1798467 baseEnd_1798467 := by
    simpa [prefixWord, tailWord_1798467, baseEnd_1798467] using wordTrace_append hprefix tailTrace_1798467
  have hstable : (prefixWord ++ tailWord_1798467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798467).length < 2 ^ (prefixWord ++ tailWord_1798467).sum := by decide
  have hdescent : baseEnd_1798467 < baseStart_1798467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798483 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 3]
def baseStart_1798483 : Nat := 118140960795 + 1798483 * 2 ^ 59
def prefixEnd_1798483 : Nat := 4983230072969 + 3 ^ 40 * 1798483 * 2
def baseEnd_1798483 : Nat := 923486227940192160691433

theorem tailTrace_1798483 : CollatzResearch.WordTrace tailWord_1798483 prefixEnd_1798483 923486227940192160691433 := by
  unfold tailWord_1798483
  simp only [CollatzResearch.WordTrace]
  refine ⟨65596063943410722287536103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43730709295607148191690735 65596063943410722287536103)
  ·
    refine ⟨98394095915116083431304155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65596063943410722287536103 98394095915116083431304155)
    ·
      refine ⟨147591143872674125146956233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98394095915116083431304155 147591143872674125146956233)
      ·
        refine ⟨110693357904505593860217175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147591143872674125146956233 110693357904505593860217175)
        ·
          refine ⟨166040036856758390790325763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110693357904505593860217175 166040036856758390790325763)
          ·
            refine ⟨249060055285137586185488645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166040036856758390790325763 249060055285137586185488645)
            ·
              refine ⟨46698760365963297409779121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249060055285137586185488645 46698760365963297409779121)
              ·
                refine ⟨35024070274472473057334341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46698760365963297409779121 35024070274472473057334341)
                ·
                  refine ⟨6567013176463588698250189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35024070274472473057334341 6567013176463588698250189)
                  ·
                    refine ⟨2462629941173845761843821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6567013176463588698250189 2462629941173845761843821)
                    ·
                      refine ⟨923486227940192160691433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2462629941173845761843821 923486227940192160691433)
                      ·
                        rfl

theorem cell23_1798483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 3].length) (baseStart_1798483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798483 prefixEnd_1798483 := by exact prefixLift 1798483
  have htrace : WordTrace (prefixWord ++ tailWord_1798483) baseStart_1798483 baseEnd_1798483 := by
    simpa [prefixWord, tailWord_1798483, baseEnd_1798483] using wordTrace_append hprefix tailTrace_1798483
  have hstable : (prefixWord ++ tailWord_1798483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798483).length < 2 ^ (prefixWord ++ tailWord_1798483).sum := by decide
  have hdescent : baseEnd_1798483 < baseStart_1798483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798518 : List Nat := [5, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2]
def baseStart_1798518 : Nat := 118140960795 + 1798518 * 2 ^ 59
def prefixEnd_1798518 : Nat := 4983230072969 + 3 ^ 40 * 1798518 * 2
def baseEnd_1798518 : Nat := 923504199763099523753773

theorem tailTrace_1798518 : CollatzResearch.WordTrace tailWord_1798518 prefixEnd_1798518 923504199763099523753773 := by
  unfold tailWord_1798518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4099833781142745204066263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43731560332189282176706805 4099833781142745204066263)
  ·
    refine ⟨6149750671714117806099395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4099833781142745204066263 6149750671714117806099395)
    ·
      refine ⟨9224626007571176709149093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6149750671714117806099395 9224626007571176709149093)
      ·
        refine ⟨1729617376419595632965455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9224626007571176709149093 1729617376419595632965455)
        ·
          refine ⟨2594426064629393449448183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1729617376419595632965455 2594426064629393449448183)
          ·
            refine ⟨3891639096944090174172275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2594426064629393449448183 3891639096944090174172275)
            ·
              refine ⟨5837458645416135261258413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3891639096944090174172275 5837458645416135261258413)
              ·
                refine ⟨2189046992031050722971905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5837458645416135261258413 2189046992031050722971905)
                ·
                  refine ⟨1641785244023288042228929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2189046992031050722971905 1641785244023288042228929)
                  ·
                    refine ⟨1231338933017466031671697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1641785244023288042228929 1231338933017466031671697)
                    ·
                      refine ⟨923504199763099523753773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231338933017466031671697 923504199763099523753773)
                      ·
                        rfl

theorem cell23_1798518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_1798518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798518 prefixEnd_1798518 := by exact prefixLift 1798518
  have htrace : WordTrace (prefixWord ++ tailWord_1798518) baseStart_1798518 baseEnd_1798518 := by
    simpa [prefixWord, tailWord_1798518, baseEnd_1798518] using wordTrace_append hprefix tailTrace_1798518
  have hstable : (prefixWord ++ tailWord_1798518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798518).length < 2 ^ (prefixWord ++ tailWord_1798518).sum := by decide
  have hdescent : baseEnd_1798518 < baseStart_1798518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798540 : List Nat := [2, 2, 1, 2, 1, 4, 1, 3, 2, 1, 4]
def baseStart_1798540 : Nat := 118140960795 + 1798540 * 2 ^ 59
def prefixEnd_1798540 : Nat := 4983230072969 + 3 ^ 40 * 1798540 * 2
def baseEnd_1798540 : Nat := 923515496337498437678671

theorem tailTrace_1798540 : CollatzResearch.WordTrace tailWord_1798540 prefixEnd_1798540 923515496337498437678671 := by
  unfold tailWord_1798540
  simp only [CollatzResearch.WordTrace]
  refine ⟨32799071452102110511180537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43732095269469480681574049 32799071452102110511180537)
  ·
    refine ⟨24599303589076582883385403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32799071452102110511180537 24599303589076582883385403)
    ·
      refine ⟨36898955383614874325078105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24599303589076582883385403 36898955383614874325078105)
      ·
        refine ⟨27674216537711155743808579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36898955383614874325078105 27674216537711155743808579)
        ·
          refine ⟨41511324806566733615712869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27674216537711155743808579 41511324806566733615712869)
          ·
            refine ⟨7783373401231262552946163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41511324806566733615712869 7783373401231262552946163)
            ·
              refine ⟨11675060101846893829419245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7783373401231262552946163 11675060101846893829419245)
              ·
                refine ⟨4378147538192585186032217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11675060101846893829419245 4378147538192585186032217)
                ·
                  refine ⟨3283610653644438889524163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4378147538192585186032217 3283610653644438889524163)
                  ·
                    refine ⟨4925415980466658334286245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3283610653644438889524163 4925415980466658334286245)
                    ·
                      refine ⟨923515496337498437678671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4925415980466658334286245 923515496337498437678671)
                      ·
                        rfl

theorem cell23_1798540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_1798540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798540 prefixEnd_1798540 := by exact prefixLift 1798540
  have htrace : WordTrace (prefixWord ++ tailWord_1798540) baseStart_1798540 baseEnd_1798540 := by
    simpa [prefixWord, tailWord_1798540, baseEnd_1798540] using wordTrace_append hprefix tailTrace_1798540
  have hstable : (prefixWord ++ tailWord_1798540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798540).length < 2 ^ (prefixWord ++ tailWord_1798540).sum := by decide
  have hdescent : baseEnd_1798540 < baseStart_1798540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798553 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 2, 1, 6]
def baseStart_1798553 : Nat := 118140960795 + 1798553 * 2 ^ 59
def prefixEnd_1798553 : Nat := 4983230072969 + 3 ^ 40 * 1798553 * 2
def baseEnd_1798553 : Nat := 923522171586006886816111

theorem tailTrace_1798553 : CollatzResearch.WordTrace tailWord_1798553 prefixEnd_1798553 923522171586006886816111 := by
  unfold tailWord_1798553
  simp only [CollatzResearch.WordTrace]
  refine ⟨65598617053157124242584313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43732411368771416161722875 65598617053157124242584313)
  ·
    refine ⟨49198962789867843181938235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65598617053157124242584313 49198962789867843181938235)
    ·
      refine ⟨73798444184801764772907353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49198962789867843181938235 73798444184801764772907353)
      ·
        refine ⟨55348833138601323579680515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73798444184801764772907353 55348833138601323579680515)
        ·
          refine ⟨83023249707901985369520773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55348833138601323579680515 83023249707901985369520773)
          ·
            refine ⟨15566859320231622256785145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83023249707901985369520773 15566859320231622256785145)
            ·
              refine ⟨11675144490173716692588859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15566859320231622256785145 11675144490173716692588859)
              ·
                refine ⟨17512716735260575038883289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11675144490173716692588859 17512716735260575038883289)
                ·
                  refine ⟨13134537551445431279162467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17512716735260575038883289 13134537551445431279162467)
                  ·
                    refine ⟨19701806327168146918743701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13134537551445431279162467 19701806327168146918743701)
                    ·
                      refine ⟨923522171586006886816111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19701806327168146918743701 923522171586006886816111)
                      ·
                        rfl

theorem cell23_1798553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_1798553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798553 prefixEnd_1798553 := by exact prefixLift 1798553
  have htrace : WordTrace (prefixWord ++ tailWord_1798553) baseStart_1798553 baseEnd_1798553 := by
    simpa [prefixWord, tailWord_1798553, baseEnd_1798553] using wordTrace_append hprefix tailTrace_1798553
  have hstable : (prefixWord ++ tailWord_1798553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798553).length < 2 ^ (prefixWord ++ tailWord_1798553).sum := by decide
  have hdescent : baseEnd_1798553 < baseStart_1798553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798603 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 5]
def baseStart_1798603 : Nat := 118140960795 + 1798603 * 2 ^ 59
def prefixEnd_1798603 : Nat := 4983230072969 + 3 ^ 40 * 1798603 * 2
def baseEnd_1798603 : Nat := 923547845618731691190881

theorem tailTrace_1798603 : CollatzResearch.WordTrace tailWord_1798603 prefixEnd_1798603 923547845618731691190881 := by
  unfold tailWord_1798603
  simp only [CollatzResearch.WordTrace]
  refine ⟨65600440702975982781904463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43733627135317321854602975 65600440702975982781904463)
  ·
    refine ⟨98400661054463974172856695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65600440702975982781904463 98400661054463974172856695)
    ·
      refine ⟨147600991581695961259285043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98400661054463974172856695 147600991581695961259285043)
      ·
        refine ⟨221401487372543941888927565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147600991581695961259285043 221401487372543941888927565)
        ·
          refine ⟨83025557764703978208347837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221401487372543941888927565 83025557764703978208347837)
          ·
            refine ⟨31134584161763991828130439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83025557764703978208347837 31134584161763991828130439)
            ·
              refine ⟨46701876242645987742195659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31134584161763991828130439 46701876242645987742195659)
              ·
                refine ⟨70052814363968981613293489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46701876242645987742195659 70052814363968981613293489)
                ·
                  refine ⟨52539610772976736209970117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70052814363968981613293489 52539610772976736209970117)
                  ·
                    refine ⟨9851177019933138039369397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52539610772976736209970117 9851177019933138039369397)
                    ·
                      refine ⟨923547845618731691190881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9851177019933138039369397 923547845618731691190881)
                      ·
                        rfl

theorem cell23_1798603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 5].length) (baseStart_1798603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798603 prefixEnd_1798603 := by exact prefixLift 1798603
  have htrace : WordTrace (prefixWord ++ tailWord_1798603) baseStart_1798603 baseEnd_1798603 := by
    simpa [prefixWord, tailWord_1798603, baseEnd_1798603] using wordTrace_append hprefix tailTrace_1798603
  have hstable : (prefixWord ++ tailWord_1798603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798603).length < 2 ^ (prefixWord ++ tailWord_1798603).sum := by decide
  have hdescent : baseEnd_1798603 < baseStart_1798603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798617 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 4, 3, 2]
def baseStart_1798617 : Nat := 118140960795 + 1798617 * 2 ^ 59
def prefixEnd_1798617 : Nat := 4983230072969 + 3 ^ 40 * 1798617 * 2
def baseEnd_1798617 : Nat := 923555034347894636415817

theorem tailTrace_1798617 : CollatzResearch.WordTrace tailWord_1798617 prefixEnd_1798617 923555034347894636415817 := by
  unfold tailWord_1798617
  simp only [CollatzResearch.WordTrace]
  refine ⟨65600951324925263172914105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43733967549950175448609403 65600951324925263172914105)
  ·
    refine ⟨49200713493693947379685579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65600951324925263172914105 49200713493693947379685579)
    ·
      refine ⟨73801070240540921069528369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49200713493693947379685579 73801070240540921069528369)
      ·
        refine ⟨55350802680405690802146277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73801070240540921069528369 55350802680405690802146277)
        ·
          refine ⟨10378275502576067025402427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55350802680405690802146277 10378275502576067025402427)
          ·
            refine ⟨15567413253864100538103641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10378275502576067025402427 15567413253864100538103641)
            ·
              refine ⟨11675559940398075403577731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15567413253864100538103641 11675559940398075403577731)
              ·
                refine ⟨17513339910597113105366597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11675559940398075403577731 17513339910597113105366597)
                ·
                  refine ⟨3283751233236958707256237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17513339910597113105366597 3283751233236958707256237)
                  ·
                    refine ⟨1231406712463859515221089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3283751233236958707256237 1231406712463859515221089)
                    ·
                      refine ⟨923555034347894636415817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231406712463859515221089 923555034347894636415817)
                      ·
                        rfl

theorem cell23_1798617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 3, 2].length) (baseStart_1798617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798617 prefixEnd_1798617 := by exact prefixLift 1798617
  have htrace : WordTrace (prefixWord ++ tailWord_1798617) baseStart_1798617 baseEnd_1798617 := by
    simpa [prefixWord, tailWord_1798617, baseEnd_1798617] using wordTrace_append hprefix tailTrace_1798617
  have hstable : (prefixWord ++ tailWord_1798617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798617).length < 2 ^ (prefixWord ++ tailWord_1798617).sum := by decide
  have hdescent : baseEnd_1798617 < baseStart_1798617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798624 : List Nat := [2, 1, 1, 3, 1, 1, 3, 6, 1, 1, 3]
def baseStart_1798624 : Nat := 118140960795 + 1798624 * 2 ^ 59
def prefixEnd_1798624 : Nat := 4983230072969 + 3 ^ 40 * 1798624 * 2
def baseEnd_1798624 : Nat := 923558628712476109028285

theorem tailTrace_1798624 : CollatzResearch.WordTrace tailWord_1798624 prefixEnd_1798624 923558628712476109028285 := by
  unfold tailWord_1798624
  simp only [CollatzResearch.WordTrace]
  refine ⟨32800603317949951684209463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43734137757266602245612617 32800603317949951684209463)
  ·
    refine ⟨49200904976924927526314195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32800603317949951684209463 49200904976924927526314195)
    ·
      refine ⟨73801357465387391289471293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49200904976924927526314195 73801357465387391289471293)
      ·
        refine ⟨27675509049520271733551735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73801357465387391289471293 27675509049520271733551735)
        ·
          refine ⟨41513263574280407600327603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27675509049520271733551735 41513263574280407600327603)
          ·
            refine ⟨62269895361420611400491405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41513263574280407600327603 62269895361420611400491405)
            ·
              refine ⟨23351210760532729275184277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62269895361420611400491405 23351210760532729275184277)
              ·
                refine ⟨1094588004399971684774263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23351210760532729275184277 1094588004399971684774263)
                ·
                  refine ⟨1641882006599957527161395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1094588004399971684774263 1641882006599957527161395)
                  ·
                    refine ⟨2462823009899936290742093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1641882006599957527161395 2462823009899936290742093)
                    ·
                      refine ⟨923558628712476109028285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2462823009899936290742093 923558628712476109028285)
                      ·
                        rfl

theorem cell23_1798624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 1, 1, 3].length) (baseStart_1798624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798624 prefixEnd_1798624 := by exact prefixLift 1798624
  have htrace : WordTrace (prefixWord ++ tailWord_1798624) baseStart_1798624 baseEnd_1798624 := by
    simpa [prefixWord, tailWord_1798624, baseEnd_1798624] using wordTrace_append hprefix tailTrace_1798624
  have hstable : (prefixWord ++ tailWord_1798624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798624).length < 2 ^ (prefixWord ++ tailWord_1798624).sum := by decide
  have hdescent : baseEnd_1798624 < baseStart_1798624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798657 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 4, 4]
def baseStart_1798657 : Nat := 118140960795 + 1798657 * 2 ^ 59
def prefixEnd_1798657 : Nat := 4983230072969 + 3 ^ 40 * 1798657 * 2
def baseEnd_1798657 : Nat := 307858524524691493305211

theorem tailTrace_1798657 : CollatzResearch.WordTrace tailWord_1798657 prefixEnd_1798657 307858524524691493305211 := by
  unfold tailWord_1798657
  simp only [CollatzResearch.WordTrace]
  refine ⟨65602410244780350004370225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43734940163186900002913483 65602410244780350004370225)
  ·
    refine ⟨49201807683585262503277669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65602410244780350004370225 49201807683585262503277669)
    ·
      refine ⟨9225338940672236719364563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49201807683585262503277669 9225338940672236719364563)
      ·
        refine ⟨13838008411008355079046845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9225338940672236719364563 13838008411008355079046845)
        ·
          refine ⟨5189253154128133154642567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13838008411008355079046845 5189253154128133154642567)
          ·
            refine ⟨7783879731192199731963851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5189253154128133154642567 7783879731192199731963851)
            ·
              refine ⟨11675819596788299597945777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7783879731192199731963851 11675819596788299597945777)
              ·
                refine ⟨8756864697591224698459333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11675819596788299597945777 8756864697591224698459333)
                ·
                  refine ⟨1641912130798354630961125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8756864697591224698459333 1641912130798354630961125)
                  ·
                    refine ⟨307858524524691493305211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1641912130798354630961125 307858524524691493305211)
                    ·
                      rfl

theorem cell23_1798657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_1798657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798657 prefixEnd_1798657 := by exact prefixLift 1798657
  have htrace : WordTrace (prefixWord ++ tailWord_1798657) baseStart_1798657 baseEnd_1798657 := by
    simpa [prefixWord, tailWord_1798657, baseEnd_1798657] using wordTrace_append hprefix tailTrace_1798657
  have hstable : (prefixWord ++ tailWord_1798657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798657).length < 2 ^ (prefixWord ++ tailWord_1798657).sum := by decide
  have hdescent : baseEnd_1798657 < baseStart_1798657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798667 : List Nat := [1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 5]
def baseStart_1798667 : Nat := 118140960795 + 1798667 * 2 ^ 59
def prefixEnd_1798667 : Nat := 4983230072969 + 3 ^ 40 * 1798667 * 2
def baseEnd_1798667 : Nat := 923580708380619440790587

theorem tailTrace_1798667 : CollatzResearch.WordTrace tailWord_1798667 prefixEnd_1798667 923580708380619440790587 := by
  unfold tailWord_1798667
  simp only [CollatzResearch.WordTrace]
  refine ⟨65602774974744121712234255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43735183316496081141489503 65602774974744121712234255)
  ·
    refine ⟨98404162462116182568351383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65602774974744121712234255 98404162462116182568351383)
    ·
      refine ⟨147606243693174273852527075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98404162462116182568351383 147606243693174273852527075)
      ·
        refine ⟨221409365539761410778790613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147606243693174273852527075 221409365539761410778790613)
        ·
          refine ⟨5189282004838158065127905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 221409365539761410778790613 5189282004838158065127905)
          ·
            refine ⟨3891961503628618548845929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5189282004838158065127905 3891961503628618548845929)
            ·
              refine ⟨2918971127721463911634447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3891961503628618548845929 2918971127721463911634447)
              ·
                refine ⟨4378456691582195867451671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2918971127721463911634447 4378456691582195867451671)
                ·
                  refine ⟨6567685037373293801177507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4378456691582195867451671 6567685037373293801177507)
                  ·
                    refine ⟨9851527556059940701766261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6567685037373293801177507 9851527556059940701766261)
                    ·
                      refine ⟨923580708380619440790587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9851527556059940701766261 923580708380619440790587)
                      ·
                        rfl

theorem cell23_1798667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 5].length) (baseStart_1798667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798667 prefixEnd_1798667 := by exact prefixLift 1798667
  have htrace : WordTrace (prefixWord ++ tailWord_1798667) baseStart_1798667 baseEnd_1798667 := by
    simpa [prefixWord, tailWord_1798667, baseEnd_1798667] using wordTrace_append hprefix tailTrace_1798667
  have hstable : (prefixWord ++ tailWord_1798667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798667).length < 2 ^ (prefixWord ++ tailWord_1798667).sum := by decide
  have hdescent : baseEnd_1798667 < baseStart_1798667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798670 : List Nat := [4, 1, 1, 2, 3, 1, 11]
def baseStart_1798670 : Nat := 118140960795 + 1798670 * 2 ^ 59
def prefixEnd_1798670 : Nat := 4983230072969 + 3 ^ 40 * 1798670 * 2
def baseEnd_1798670 : Nat := 11402249985463986778433

theorem tailTrace_1798670 : CollatzResearch.WordTrace tailWord_1798670 prefixEnd_1798670 11402249985463986778433 := by
  unfold tailWord_1798670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8200360549216656653074183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43735256262488835483062309 8200360549216656653074183)
  ·
    refine ⟨12300540823824984979611275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8200360549216656653074183 12300540823824984979611275)
    ·
      refine ⟨18450811235737477469416913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12300540823824984979611275 18450811235737477469416913)
      ·
        refine ⟨13838108426803108102062685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18450811235737477469416913 13838108426803108102062685)
        ·
          refine ⟨5189290660051165538273507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13838108426803108102062685 5189290660051165538273507)
          ·
            refine ⟨7783935990076748307410261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5189290660051165538273507 7783935990076748307410261)
            ·
              refine ⟨11402249985463986778433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7783935990076748307410261 11402249985463986778433)
              ·
                rfl

theorem cell23_1798670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 11].length) (baseStart_1798670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798670 prefixEnd_1798670 := by exact prefixLift 1798670
  have htrace : WordTrace (prefixWord ++ tailWord_1798670) baseStart_1798670 baseEnd_1798670 := by
    simpa [prefixWord, tailWord_1798670, baseEnd_1798670] using wordTrace_append hprefix tailTrace_1798670
  have hstable : (prefixWord ++ tailWord_1798670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798670).length < 2 ^ (prefixWord ++ tailWord_1798670).sum := by decide
  have hdescent : baseEnd_1798670 < baseStart_1798670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798690 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_1798690 : Nat := 118140960795 + 1798690 * 2 ^ 59
def prefixEnd_1798690 : Nat := 4983230072969 + 3 ^ 40 * 1798690 * 2
def baseEnd_1798690 : Nat := 923592518435672850802981

theorem tailTrace_1798690 : CollatzResearch.WordTrace tailWord_1798690 prefixEnd_1798690 923592518435672850802981 := by
  unfold tailWord_1798690
  simp only [CollatzResearch.WordTrace]
  refine ⟨16400903463415199160080381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43735742569107197760214349 16400903463415199160080381)
  ·
    refine ⟨6150338798780699685030143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16400903463415199160080381 6150338798780699685030143)
    ·
      refine ⟨9225508198171049527545215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6150338798780699685030143 9225508198171049527545215)
      ·
        refine ⟨13838262297256574291317823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9225508198171049527545215 13838262297256574291317823)
        ·
          refine ⟨20757393445884861436976735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13838262297256574291317823 20757393445884861436976735)
          ·
            refine ⟨31136090168827292155465103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20757393445884861436976735 31136090168827292155465103)
            ·
              refine ⟨46704135253240938233197655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31136090168827292155465103 46704135253240938233197655)
              ·
                refine ⟨70056202879861407349796483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46704135253240938233197655 70056202879861407349796483)
                ·
                  refine ⟨105084304319792111024694725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70056202879861407349796483 105084304319792111024694725)
                  ·
                    refine ⟨19703307059961020817130261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105084304319792111024694725 19703307059961020817130261)
                    ·
                      refine ⟨923592518435672850802981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19703307059961020817130261 923592518435672850802981)
                      ·
                        rfl

theorem cell23_1798690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_1798690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798690 prefixEnd_1798690 := by exact prefixLift 1798690
  have htrace : WordTrace (prefixWord ++ tailWord_1798690) baseStart_1798690 baseEnd_1798690 := by
    simpa [prefixWord, tailWord_1798690, baseEnd_1798690] using wordTrace_append hprefix tailTrace_1798690
  have hstable : (prefixWord ++ tailWord_1798690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798690).length < 2 ^ (prefixWord ++ tailWord_1798690).sum := by decide
  have hdescent : baseEnd_1798690 < baseStart_1798690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798691 : List Nat := [1, 1, 1, 4, 4, 3, 2, 1, 2, 4]
def baseStart_1798691 : Nat := 118140960795 + 1798691 * 2 ^ 59
def prefixEnd_1798691 : Nat := 4983230072969 + 3 ^ 40 * 1798691 * 2
def baseEnd_1798691 : Nat := 307864343972109115630159

theorem tailTrace_1798691 : CollatzResearch.WordTrace tailWord_1798691 prefixEnd_1798691 307864343972109115630159 := by
  unfold tailWord_1798691
  simp only [CollatzResearch.WordTrace]
  refine ⟨65603650326657173811107927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43735766884438115874071951 65603650326657173811107927)
  ·
    refine ⟨98405475489985760716661891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65603650326657173811107927 98405475489985760716661891)
    ·
      refine ⟨147608213234978641074992837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98405475489985760716661891 147608213234978641074992837)
      ·
        refine ⟨27676539981558495201561157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147608213234978641074992837 27676539981558495201561157)
        ·
          refine ⟨5189351246542217850292717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27676539981558495201561157 5189351246542217850292717)
          ·
            refine ⟨1946006717453331693859769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5189351246542217850292717 1946006717453331693859769)
            ·
              refine ⟨1459505038089998770394827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1946006717453331693859769 1459505038089998770394827)
              ·
                refine ⟨2189257557134998155592241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1459505038089998770394827 2189257557134998155592241)
                ·
                  refine ⟨1641943167851248616694181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2189257557134998155592241 1641943167851248616694181)
                  ·
                    refine ⟨307864343972109115630159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1641943167851248616694181 307864343972109115630159)
                    ·
                      rfl

theorem cell23_1798691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 2, 4].length) (baseStart_1798691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798691 prefixEnd_1798691 := by exact prefixLift 1798691
  have htrace : WordTrace (prefixWord ++ tailWord_1798691) baseStart_1798691 baseEnd_1798691 := by
    simpa [prefixWord, tailWord_1798691, baseEnd_1798691] using wordTrace_append hprefix tailTrace_1798691
  have hstable : (prefixWord ++ tailWord_1798691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798691).length < 2 ^ (prefixWord ++ tailWord_1798691).sum := by decide
  have hdescent : baseEnd_1798691 < baseStart_1798691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798718 : List Nat := [4, 2, 1, 4, 2, 1, 1, 1, 1, 1, 5]
def baseStart_1798718 : Nat := 118140960795 + 1798718 * 2 ^ 59
def prefixEnd_1798718 : Nat := 4983230072969 + 3 ^ 40 * 1798718 * 2
def baseEnd_1798718 : Nat := 923606895893998741252853

theorem tailTrace_1798718 : CollatzResearch.WordTrace tailWord_1798718 prefixEnd_1798718 923606895893998741252853 := by
  unfold tailWord_1798718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8200579387194919677792601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43736423398372904948227205 8200579387194919677792601)
  ·
    refine ⟨6150434540396189758344451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8200579387194919677792601 6150434540396189758344451)
    ·
      refine ⟨9225651810594284637516677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6150434540396189758344451 9225651810594284637516677)
      ·
        refine ⟨1729809714486428369534377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9225651810594284637516677 1729809714486428369534377)
        ·
          refine ⟨1297357285864821277150783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1729809714486428369534377 1297357285864821277150783)
          ·
            refine ⟨1946035928797231915726175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1297357285864821277150783 1946035928797231915726175)
            ·
              refine ⟨2919053893195847873589263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1946035928797231915726175 2919053893195847873589263)
              ·
                refine ⟨4378580839793771810383895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2919053893195847873589263 4378580839793771810383895)
                ·
                  refine ⟨6567871259690657715575843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4378580839793771810383895 6567871259690657715575843)
                  ·
                    refine ⟨9851806889535986573363765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6567871259690657715575843 9851806889535986573363765)
                    ·
                      refine ⟨923606895893998741252853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9851806889535986573363765 923606895893998741252853)
                      ·
                        rfl

theorem cell23_1798718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_1798718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798718 prefixEnd_1798718 := by exact prefixLift 1798718
  have htrace : WordTrace (prefixWord ++ tailWord_1798718) baseStart_1798718 baseEnd_1798718 := by
    simpa [prefixWord, tailWord_1798718, baseEnd_1798718] using wordTrace_append hprefix tailTrace_1798718
  have hstable : (prefixWord ++ tailWord_1798718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798718).length < 2 ^ (prefixWord ++ tailWord_1798718).sum := by decide
  have hdescent : baseEnd_1798718 < baseStart_1798718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798787 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 3]
def baseStart_1798787 : Nat := 118140960795 + 1798787 * 2 ^ 59
def prefixEnd_1798787 : Nat := 4983230072969 + 3 ^ 40 * 1798787 * 2
def baseEnd_1798787 : Nat := 923642326059158971290035

theorem tailTrace_1798787 : CollatzResearch.WordTrace tailWord_1798787 prefixEnd_1798787 923642326059158971290035 := by
  unfold tailWord_1798787
  simp only [CollatzResearch.WordTrace]
  refine ⟨65607151734309382206602615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43738101156206254804401743 65607151734309382206602615)
  ·
    refine ⟨98410727601464073309903923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65607151734309382206602615 98410727601464073309903923)
    ·
      refine ⟨147616091402196109964855885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98410727601464073309903923 147616091402196109964855885)
      ·
        refine ⟨55356034275823541236820957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147616091402196109964855885 55356034275823541236820957)
        ·
          refine ⟨20758512853433827963807859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55356034275823541236820957 20758512853433827963807859)
          ·
            refine ⟨31137769280150741945711789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20758512853433827963807859 31137769280150741945711789)
            ·
              refine ⟨11676663480056528229641921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31137769280150741945711789 11676663480056528229641921)
              ·
                refine ⟨8757497610042396172231441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11676663480056528229641921 8757497610042396172231441)
                ·
                  refine ⟨6568123207531797129173581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8757497610042396172231441 6568123207531797129173581)
                  ·
                    refine ⟨2463046202824423923440093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6568123207531797129173581 2463046202824423923440093)
                    ·
                      refine ⟨923642326059158971290035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2463046202824423923440093 923642326059158971290035)
                      ·
                        rfl

theorem cell23_1798787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_1798787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798787 prefixEnd_1798787 := by exact prefixLift 1798787
  have htrace : WordTrace (prefixWord ++ tailWord_1798787) baseStart_1798787 baseEnd_1798787 := by
    simpa [prefixWord, tailWord_1798787, baseEnd_1798787] using wordTrace_append hprefix tailTrace_1798787
  have hstable : (prefixWord ++ tailWord_1798787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798787).length < 2 ^ (prefixWord ++ tailWord_1798787).sum := by decide
  have hdescent : baseEnd_1798787 < baseStart_1798787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798788 : List Nat := [2, 3, 2, 1, 3, 1, 3, 2, 2, 2, 2]
def baseStart_1798788 : Nat := 118140960795 + 1798788 * 2 ^ 59
def prefixEnd_1798788 : Nat := 4983230072969 + 3 ^ 40 * 1798788 * 2
def baseEnd_1798788 : Nat := 923642839539813467377531

theorem tailTrace_1798788 : CollatzResearch.WordTrace tailWord_1798788 prefixEnd_1798788 923642839539813467377531 := by
  unfold tailWord_1798788
  simp only [CollatzResearch.WordTrace]
  refine ⟨32803594103652879688694509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43738125471537172918259345 32803594103652879688694509)
  ·
    refine ⟨12301347788869829883260441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32803594103652879688694509 12301347788869829883260441)
    ·
      refine ⟨9226010841652372412445331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12301347788869829883260441 9226010841652372412445331)
      ·
        refine ⟨13839016262478558618667997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9226010841652372412445331 13839016262478558618667997)
        ·
          refine ⟨5189631098429459482000499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13839016262478558618667997 5189631098429459482000499)
          ·
            refine ⟨7784446647644189223000749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5189631098429459482000499 7784446647644189223000749)
            ·
              refine ⟨2919167492866570958625281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7784446647644189223000749 2919167492866570958625281)
              ·
                refine ⟨2189375619649928218968961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2919167492866570958625281 2189375619649928218968961)
                ·
                  refine ⟨1642031714737446164226721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2189375619649928218968961 1642031714737446164226721)
                  ·
                    refine ⟨1231523786053084623170041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1642031714737446164226721 1231523786053084623170041)
                    ·
                      refine ⟨923642839539813467377531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231523786053084623170041 923642839539813467377531)
                      ·
                        rfl

theorem cell23_1798788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_1798788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798788 prefixEnd_1798788 := by exact prefixLift 1798788
  have htrace : WordTrace (prefixWord ++ tailWord_1798788) baseStart_1798788 baseEnd_1798788 := by
    simpa [prefixWord, tailWord_1798788, baseEnd_1798788] using wordTrace_append hprefix tailTrace_1798788
  have hstable : (prefixWord ++ tailWord_1798788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798788).length < 2 ^ (prefixWord ++ tailWord_1798788).sum := by decide
  have hdescent : baseEnd_1798788 < baseStart_1798788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798794 : List Nat := [3, 1, 2, 3, 3, 1, 2, 1, 7]
def baseStart_1798794 : Nat := 118140960795 + 1798794 * 2 ^ 59
def prefixEnd_1798794 : Nat := 4983230072969 + 3 ^ 40 * 1798794 * 2
def baseEnd_1798794 : Nat := 102627324491526715989167

theorem tailTrace_1798794 : CollatzResearch.WordTrace tailWord_1798794 prefixEnd_1798794 102627324491526715989167 := by
  unfold tailWord_1798794
  simp only [CollatzResearch.WordTrace]
  refine ⟨16401851761321005600526859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43738271363522681601404957 16401851761321005600526859)
  ·
    refine ⟨24602777641981508400790289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16401851761321005600526859 24602777641981508400790289)
    ·
      refine ⟨18452083231486131300592717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24602777641981508400790289 18452083231486131300592717)
      ·
        refine ⟨6919531211807299237722269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18452083231486131300592717 6919531211807299237722269)
        ·
          refine ⟨2594824204427737214145851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6919531211807299237722269 2594824204427737214145851)
          ·
            refine ⟨3892236306641605821218777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2594824204427737214145851 3892236306641605821218777)
            ·
              refine ⟨2919177229981204365914083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3892236306641605821218777 2919177229981204365914083)
              ·
                refine ⟨4378765844971806548871125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2919177229981204365914083 4378765844971806548871125)
                ·
                  refine ⟨102627324491526715989167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4378765844971806548871125 102627324491526715989167)
                  ·
                    rfl

theorem cell23_1798794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 7].length) (baseStart_1798794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798794 prefixEnd_1798794 := by exact prefixLift 1798794
  have htrace : WordTrace (prefixWord ++ tailWord_1798794) baseStart_1798794 baseEnd_1798794 := by
    simpa [prefixWord, tailWord_1798794, baseEnd_1798794] using wordTrace_append hprefix tailTrace_1798794
  have hstable : (prefixWord ++ tailWord_1798794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798794).length < 2 ^ (prefixWord ++ tailWord_1798794).sum := by decide
  have hdescent : baseEnd_1798794 < baseStart_1798794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798844 : List Nat := [2, 2, 2, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_1798844 : Nat := 118140960795 + 1798844 * 2 ^ 59
def prefixEnd_1798844 : Nat := 4983230072969 + 3 ^ 40 * 1798844 * 2
def baseEnd_1798844 : Nat := 923671594456465248277273

theorem tailTrace_1798844 : CollatzResearch.WordTrace tailWord_1798844 prefixEnd_1798844 923671594456465248277273 := by
  unfold tailWord_1798844
  simp only [CollatzResearch.WordTrace]
  refine ⟨32804615347551440470713793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43739487130068587294285057 32804615347551440470713793)
  ·
    refine ⟨24603461510663580353035345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32804615347551440470713793 24603461510663580353035345)
    ·
      refine ⟨18452596132997685264776509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24603461510663580353035345 18452596132997685264776509)
      ·
        refine ⟨6919723549874131974291191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18452596132997685264776509 6919723549874131974291191)
        ·
          refine ⟨10379585324811197961436787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6919723549874131974291191 10379585324811197961436787)
          ·
            refine ⟨15569377987216796942155181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10379585324811197961436787 15569377987216796942155181)
            ·
              refine ⟨5838516745206298853308193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15569377987216796942155181 5838516745206298853308193)
              ·
                refine ⟨4378887558904724139981145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5838516745206298853308193 4378887558904724139981145)
                ·
                  refine ⟨3284165669178543104985859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4378887558904724139981145 3284165669178543104985859)
                  ·
                    refine ⟨4926248503767814657478789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3284165669178543104985859 4926248503767814657478789)
                    ·
                      refine ⟨923671594456465248277273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4926248503767814657478789 923671594456465248277273)
                      ·
                        rfl

theorem cell23_1798844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_1798844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798844 prefixEnd_1798844 := by exact prefixLift 1798844
  have htrace : WordTrace (prefixWord ++ tailWord_1798844) baseStart_1798844 baseEnd_1798844 := by
    simpa [prefixWord, tailWord_1798844, baseEnd_1798844] using wordTrace_append hprefix tailTrace_1798844
  have hstable : (prefixWord ++ tailWord_1798844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798844).length < 2 ^ (prefixWord ++ tailWord_1798844).sum := by decide
  have hdescent : baseEnd_1798844 < baseStart_1798844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798881 : List Nat := [1, 2, 3, 1, 4, 2, 2, 1, 2, 2, 3]
def baseStart_1798881 : Nat := 118140960795 + 1798881 * 2 ^ 59
def prefixEnd_1798881 : Nat := 4983230072969 + 3 ^ 40 * 1798881 * 2
def baseEnd_1798881 : Nat := 923690593240681603514603

theorem tailTrace_1798881 : CollatzResearch.WordTrace tailWord_1798881 prefixEnd_1798881 923690593240681603514603 := by
  unfold tailWord_1798881
  simp only [CollatzResearch.WordTrace]
  refine ⟨65610580195968836260524497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43740386797312557507016331 65610580195968836260524497)
  ·
    refine ⟨49207935146976627195393373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65610580195968836260524497 49207935146976627195393373)
    ·
      refine ⟨18452975680116235198272515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49207935146976627195393373 18452975680116235198272515)
      ·
        refine ⟨27679463520174352797408773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18452975680116235198272515 27679463520174352797408773)
        ·
          refine ⟨5189899410032691149514145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27679463520174352797408773 5189899410032691149514145)
          ·
            refine ⟨3892424557524518362135609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5189899410032691149514145 3892424557524518362135609)
            ·
              refine ⟨2919318418143388771601707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3892424557524518362135609 2919318418143388771601707)
              ·
                refine ⟨4378977627215083157402561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2919318418143388771601707 4378977627215083157402561)
                ·
                  refine ⟨3284233220411312368051921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4378977627215083157402561 3284233220411312368051921)
                  ·
                    refine ⟨2463174915308484276038941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3284233220411312368051921 2463174915308484276038941)
                    ·
                      refine ⟨923690593240681603514603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2463174915308484276038941 923690593240681603514603)
                      ·
                        rfl

theorem cell23_1798881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_1798881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798881 prefixEnd_1798881 := by exact prefixLift 1798881
  have htrace : WordTrace (prefixWord ++ tailWord_1798881) baseStart_1798881 baseEnd_1798881 := by
    simpa [prefixWord, tailWord_1798881, baseEnd_1798881] using wordTrace_append hprefix tailTrace_1798881
  have hstable : (prefixWord ++ tailWord_1798881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798881).length < 2 ^ (prefixWord ++ tailWord_1798881).sum := by decide
  have hdescent : baseEnd_1798881 < baseStart_1798881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798937 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 5, 1, 5]
def baseStart_1798937 : Nat := 118140960795 + 1798937 * 2 ^ 59
def prefixEnd_1798937 : Nat := 4983230072969 + 3 ^ 40 * 1798937 * 2
def baseEnd_1798937 : Nat := 923719348157333384414345

theorem tailTrace_1798937 : CollatzResearch.WordTrace tailWord_1798937 prefixEnd_1798937 923719348157333384414345 := by
  unfold tailWord_1798937
  simp only [CollatzResearch.WordTrace]
  refine ⟨65612622683765957824563065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43741748455843971883042043 65612622683765957824563065)
  ·
    refine ⟨49209467012824468368422299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65612622683765957824563065 49209467012824468368422299)
    ·
      refine ⟨73814200519236702552633449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49209467012824468368422299 73814200519236702552633449)
      ·
        refine ⟨55360650389427526914475087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73814200519236702552633449 55360650389427526914475087)
        ·
          refine ⟨83040975584141290371712631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55360650389427526914475087 83040975584141290371712631)
          ·
            refine ⟨124561463376211935557568947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83040975584141290371712631 124561463376211935557568947)
            ·
              refine ⟨186842195064317903336353421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124561463376211935557568947 186842195064317903336353421)
              ·
                refine ⟨70065823149119213751132533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186842195064317903336353421 70065823149119213751132533)
                ·
                  refine ⟨6568670920229926289168675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70065823149119213751132533 6568670920229926289168675)
                  ·
                    refine ⟨9853006380344889433753013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6568670920229926289168675 9853006380344889433753013)
                    ·
                      refine ⟨923719348157333384414345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9853006380344889433753013 923719348157333384414345)
                      ·
                        rfl

theorem cell23_1798937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_1798937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798937 prefixEnd_1798937 := by exact prefixLift 1798937
  have htrace : WordTrace (prefixWord ++ tailWord_1798937) baseStart_1798937 baseEnd_1798937 := by
    simpa [prefixWord, tailWord_1798937, baseEnd_1798937] using wordTrace_append hprefix tailTrace_1798937
  have hstable : (prefixWord ++ tailWord_1798937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798937).length < 2 ^ (prefixWord ++ tailWord_1798937).sum := by decide
  have hdescent : baseEnd_1798937 < baseStart_1798937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798944 : List Nat := [2, 1, 1, 5, 1, 2, 2, 2, 1, 6]
def baseStart_1798944 : Nat := 118140960795 + 1798944 * 2 ^ 59
def prefixEnd_1798944 : Nat := 4983230072969 + 3 ^ 40 * 1798944 * 2
def baseEnd_1798944 : Nat := 307907647507304952342271

theorem tailTrace_1798944 : CollatzResearch.WordTrace tailWord_1798944 prefixEnd_1798944 307907647507304952342271 := by
  unfold tailWord_1798944
  simp only [CollatzResearch.WordTrace]
  refine ⟨32806438997370299010033943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43741918663160398680045257 32806438997370299010033943)
  ·
    refine ⟨49209658496055448515050915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32806438997370299010033943 49209658496055448515050915)
    ·
      refine ⟨73814487744083172772576373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49209658496055448515050915 73814487744083172772576373)
      ·
        refine ⟨6920108226007797447429035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73814487744083172772576373 6920108226007797447429035)
        ·
          refine ⟨10380162339011696171143553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6920108226007797447429035 10380162339011696171143553)
          ·
            refine ⟨7785121754258772128357665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10380162339011696171143553 7785121754258772128357665)
            ·
              refine ⟨5838841315694079096268249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7785121754258772128357665 5838841315694079096268249)
              ·
                refine ⟨4379130986770559322201187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5838841315694079096268249 4379130986770559322201187)
                ·
                  refine ⟨6568696480155838983301781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4379130986770559322201187 6568696480155838983301781)
                  ·
                    refine ⟨307907647507304952342271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6568696480155838983301781 307907647507304952342271)
                    ·
                      rfl

theorem cell23_1798944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 1, 6].length) (baseStart_1798944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798944 prefixEnd_1798944 := by exact prefixLift 1798944
  have htrace : WordTrace (prefixWord ++ tailWord_1798944) baseStart_1798944 baseEnd_1798944 := by
    simpa [prefixWord, tailWord_1798944, baseEnd_1798944] using wordTrace_append hprefix tailTrace_1798944
  have hstable : (prefixWord ++ tailWord_1798944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798944).length < 2 ^ (prefixWord ++ tailWord_1798944).sum := by decide
  have hdescent : baseEnd_1798944 < baseStart_1798944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798947 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 6]
def baseStart_1798947 : Nat := 118140960795 + 1798947 * 2 ^ 59
def prefixEnd_1798947 : Nat := 4983230072969 + 3 ^ 40 * 1798947 * 2
def baseEnd_1798947 : Nat := 923724482963878345289299

theorem tailTrace_1798947 : CollatzResearch.WordTrace tailWord_1798947 prefixEnd_1798947 923724482963878345289299 := by
  unfold tailWord_1798947
  simp only [CollatzResearch.WordTrace]
  refine ⟨65612987413729729532427095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43741991609153153021618063 65612987413729729532427095)
  ·
    refine ⟨98419481120594594298640643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65612987413729729532427095 98419481120594594298640643)
    ·
      refine ⟨147629221680891891447960965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98419481120594594298640643 147629221680891891447960965)
      ·
        refine ⟨27680479065167229646492681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147629221680891891447960965 27680479065167229646492681)
        ·
          refine ⟨20760359298875422234869511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27680479065167229646492681 20760359298875422234869511)
          ·
            refine ⟨31140538948313133352304267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20760359298875422234869511 31140538948313133352304267)
            ·
              refine ⟨46710808422469700028456401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31140538948313133352304267 46710808422469700028456401)
              ·
                refine ⟨35033106316852275021342301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46710808422469700028456401 35033106316852275021342301)
                ·
                  refine ⟨13137414868819603133003363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35033106316852275021342301 13137414868819603133003363)
                  ·
                    refine ⟨19706122303229404699505045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13137414868819603133003363 19706122303229404699505045)
                    ·
                      refine ⟨923724482963878345289299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19706122303229404699505045 923724482963878345289299)
                      ·
                        rfl

theorem cell23_1798947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_1798947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798947 prefixEnd_1798947 := by exact prefixLift 1798947
  have htrace : WordTrace (prefixWord ++ tailWord_1798947) baseStart_1798947 baseEnd_1798947 := by
    simpa [prefixWord, tailWord_1798947, baseEnd_1798947] using wordTrace_append hprefix tailTrace_1798947
  have hstable : (prefixWord ++ tailWord_1798947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798947).length < 2 ^ (prefixWord ++ tailWord_1798947).sum := by decide
  have hdescent : baseEnd_1798947 < baseStart_1798947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798968 : List Nat := [2, 1, 2, 1, 3, 2, 4, 1, 3, 2, 2]
def baseStart_1798968 : Nat := 118140960795 + 1798968 * 2 ^ 59
def prefixEnd_1798968 : Nat := 4983230072969 + 3 ^ 40 * 1798968 * 2
def baseEnd_1798968 : Nat := 923735266057622763126703

theorem tailTrace_1798968 : CollatzResearch.WordTrace tailWord_1798968 prefixEnd_1798968 923735266057622763126703 := by
  unfold tailWord_1798968
  simp only [CollatzResearch.WordTrace]
  refine ⟨32806876673326825059470779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43742502231102433412627705 32806876673326825059470779)
  ·
    refine ⟨49210315009990237589206169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32806876673326825059470779 49210315009990237589206169)
    ·
      refine ⟨36907736257492678191904627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49210315009990237589206169 36907736257492678191904627)
      ·
        refine ⟨55361604386239017287856941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36907736257492678191904627 55361604386239017287856941)
        ·
          refine ⟨20760601644839631482946353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55361604386239017287856941 20760601644839631482946353)
          ·
            refine ⟨15570451233629723612209765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20760601644839631482946353 15570451233629723612209765)
            ·
              refine ⟨2919459606305573177289331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15570451233629723612209765 2919459606305573177289331)
              ·
                refine ⟨4379189409458359765933997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2919459606305573177289331 4379189409458359765933997)
                ·
                  refine ⟨1642196028546884912225249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4379189409458359765933997 1642196028546884912225249)
                  ·
                    refine ⟨1231647021410163684168937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1642196028546884912225249 1231647021410163684168937)
                    ·
                      refine ⟨923735266057622763126703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231647021410163684168937 923735266057622763126703)
                      ·
                        rfl

theorem cell23_1798968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 3, 2, 2].length) (baseStart_1798968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798968 prefixEnd_1798968 := by exact prefixLift 1798968
  have htrace : WordTrace (prefixWord ++ tailWord_1798968) baseStart_1798968 baseEnd_1798968 := by
    simpa [prefixWord, tailWord_1798968, baseEnd_1798968] using wordTrace_append hprefix tailTrace_1798968
  have hstable : (prefixWord ++ tailWord_1798968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798968).length < 2 ^ (prefixWord ++ tailWord_1798968).sum := by decide
  have hdescent : baseEnd_1798968 < baseStart_1798968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798988 : List Nat := [2, 2, 1, 3, 3, 2, 2, 2, 1, 2, 3]
def baseStart_1798988 : Nat := 118140960795 + 1798988 * 2 ^ 59
def prefixEnd_1798988 : Nat := 4983230072969 + 3 ^ 40 * 1798988 * 2
def baseEnd_1798988 : Nat := 923745535670712684876611

theorem tailTrace_1798988 : CollatzResearch.WordTrace tailWord_1798988 prefixEnd_1798988 923745535670712684876611 := by
  unfold tailWord_1798988
  simp only [CollatzResearch.WordTrace]
  refine ⟨32807241403290596767334809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43742988537720795689779745 32807241403290596767334809)
  ·
    refine ⟨24605431052467947575501107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32807241403290596767334809 24605431052467947575501107)
    ·
      refine ⟨36908146578701921363251661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24605431052467947575501107 36908146578701921363251661)
      ·
        refine ⟨13840554967013220511219373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36908146578701921363251661 13840554967013220511219373)
        ·
          refine ⟨5190208112629957691707265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13840554967013220511219373 5190208112629957691707265)
          ·
            refine ⟨3892656084472468268780449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5190208112629957691707265 3892656084472468268780449)
            ·
              refine ⟨2919492063354351201585337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3892656084472468268780449 2919492063354351201585337)
              ·
                refine ⟨2189619047515763401189003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2919492063354351201585337 2189619047515763401189003)
                ·
                  refine ⟨3284428571273645101783505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2189619047515763401189003 3284428571273645101783505)
                  ·
                    refine ⟨2463321428455233826337629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3284428571273645101783505 2463321428455233826337629)
                    ·
                      refine ⟨923745535670712684876611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2463321428455233826337629 923745535670712684876611)
                      ·
                        rfl

theorem cell23_1798988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_1798988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798988 prefixEnd_1798988 := by exact prefixLift 1798988
  have htrace : WordTrace (prefixWord ++ tailWord_1798988) baseStart_1798988 baseEnd_1798988 := by
    simpa [prefixWord, tailWord_1798988, baseEnd_1798988] using wordTrace_append hprefix tailTrace_1798988
  have hstable : (prefixWord ++ tailWord_1798988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798988).length < 2 ^ (prefixWord ++ tailWord_1798988).sum := by decide
  have hdescent : baseEnd_1798988 < baseStart_1798988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799001 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 4, 1, 3]
def baseStart_1799001 : Nat := 118140960795 + 1799001 * 2 ^ 59
def prefixEnd_1799001 : Nat := 4983230072969 + 3 ^ 40 * 1799001 * 2
def baseEnd_1799001 : Nat := 923752210919221134014051

theorem tailTrace_1799001 : CollatzResearch.WordTrace tailWord_1799001 prefixEnd_1799001 923752210919221134014051 := by
  unfold tailWord_1799001
  simp only [CollatzResearch.WordTrace]
  refine ⟨65614956955534096754892857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43743304637022731169928571 65614956955534096754892857)
  ·
    refine ⟨49211217716650572566169643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65614956955534096754892857 49211217716650572566169643)
    ·
      refine ⟨73816826574975858849254465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49211217716650572566169643 73816826574975858849254465)
      ·
        refine ⟨55362619931231894136940849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73816826574975858849254465 55362619931231894136940849)
        ·
          refine ⟨41521964948423920602705637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55362619931231894136940849 41521964948423920602705637)
          ·
            refine ⟨7785368427829485113007307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41521964948423920602705637 7785368427829485113007307)
            ·
              refine ⟨11678052641744227669510961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7785368427829485113007307 11678052641744227669510961)
              ·
                refine ⟨8758539481308170752133221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11678052641744227669510961 8758539481308170752133221)
                ·
                  refine ⟨1642226152745282016024979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8758539481308170752133221 1642226152745282016024979)
                  ·
                    refine ⟨2463339229117923024037469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1642226152745282016024979 2463339229117923024037469)
                    ·
                      refine ⟨923752210919221134014051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2463339229117923024037469 923752210919221134014051)
                      ·
                        rfl

theorem cell23_1799001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 1, 3].length) (baseStart_1799001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799001 prefixEnd_1799001 := by exact prefixLift 1799001
  have htrace : WordTrace (prefixWord ++ tailWord_1799001) baseStart_1799001 baseEnd_1799001 := by
    simpa [prefixWord, tailWord_1799001, baseEnd_1799001] using wordTrace_append hprefix tailTrace_1799001
  have hstable : (prefixWord ++ tailWord_1799001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799001).length < 2 ^ (prefixWord ++ tailWord_1799001).sum := by decide
  have hdescent : baseEnd_1799001 < baseStart_1799001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799002 : List Nat := [3, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2]
def baseStart_1799002 : Nat := 118140960795 + 1799002 * 2 ^ 59
def prefixEnd_1799002 : Nat := 4983230072969 + 3 ^ 40 * 1799002 * 2
def baseEnd_1799002 : Nat := 923752724399875630101547

theorem tailTrace_1799002 : CollatzResearch.WordTrace tailWord_1799002 prefixEnd_1799002 923752724399875630101547 := by
  unfold tailWord_1799002
  simp only [CollatzResearch.WordTrace]
  refine ⟨16403748357132618481419815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43743328952353649283786173 16403748357132618481419815)
  ·
    refine ⟨24605622535698927722129723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16403748357132618481419815 24605622535698927722129723)
    ·
      refine ⟨36908433803548391583194585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24605622535698927722129723 36908433803548391583194585)
      ·
        refine ⟨27681325352661293687395939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36908433803548391583194585 27681325352661293687395939)
        ·
          refine ⟨41521988028991940531093909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27681325352661293687395939 41521988028991940531093909)
          ·
            refine ⟨1946343188858997212395027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41521988028991940531093909 1946343188858997212395027)
            ·
              refine ⟨2919514783288495818592541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1946343188858997212395027 2919514783288495818592541)
              ·
                refine ⟨1094818043733185931972203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2919514783288495818592541 1094818043733185931972203)
                ·
                  refine ⟨1642227065599778897958305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1094818043733185931972203 1642227065599778897958305)
                  ·
                    refine ⟨1231670299199834173468729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1642227065599778897958305 1231670299199834173468729)
                    ·
                      refine ⟨923752724399875630101547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231670299199834173468729 923752724399875630101547)
                      ·
                        rfl

theorem cell23_1799002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2].length) (baseStart_1799002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799002 prefixEnd_1799002 := by exact prefixLift 1799002
  have htrace : WordTrace (prefixWord ++ tailWord_1799002) baseStart_1799002 baseEnd_1799002 := by
    simpa [prefixWord, tailWord_1799002, baseEnd_1799002] using wordTrace_append hprefix tailTrace_1799002
  have hstable : (prefixWord ++ tailWord_1799002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799002).length < 2 ^ (prefixWord ++ tailWord_1799002).sum := by decide
  have hdescent : baseEnd_1799002 < baseStart_1799002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799045 : List Nat := [1, 3, 1, 1, 3, 5, 1, 2, 1, 3, 2]
def baseStart_1799045 : Nat := 118140960795 + 1799045 * 2 ^ 59
def prefixEnd_1799045 : Nat := 4983230072969 + 3 ^ 40 * 1799045 * 2
def baseEnd_1799045 : Nat := 923774804068018961863849

theorem tailTrace_1799045 : CollatzResearch.WordTrace tailWord_1799045 prefixEnd_1799045 923774804068018961863849 := by
  unfold tailWord_1799045
  simp only [CollatzResearch.WordTrace]
  refine ⟨65616561767374692269494589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43744374511583128179663059 65616561767374692269494589)
  ·
    refine ⟨24606210662765509601060471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65616561767374692269494589 24606210662765509601060471)
    ·
      refine ⟨36909315994148264401590707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24606210662765509601060471 36909315994148264401590707)
      ·
        refine ⟨55363973991222396602386061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36909315994148264401590707 55363973991222396602386061)
        ·
          refine ⟨20761490246708398725894773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55363973991222396602386061 20761490246708398725894773)
          ·
            refine ⟨1946389710628912380552635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20761490246708398725894773 1946389710628912380552635)
            ·
              refine ⟨2919584565943368570828953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1946389710628912380552635 2919584565943368570828953)
              ·
                refine ⟨2189688424457526428121715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2919584565943368570828953 2189688424457526428121715)
                ·
                  refine ⟨3284532636686289642182573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2189688424457526428121715 3284532636686289642182573)
                  ·
                    refine ⟨1231699738757358615818465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3284532636686289642182573 1231699738757358615818465)
                    ·
                      refine ⟨923774804068018961863849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231699738757358615818465 923774804068018961863849)
                      ·
                        rfl

theorem cell23_1799045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 3, 2].length) (baseStart_1799045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799045 prefixEnd_1799045 := by exact prefixLift 1799045
  have htrace : WordTrace (prefixWord ++ tailWord_1799045) baseStart_1799045 baseEnd_1799045 := by
    simpa [prefixWord, tailWord_1799045, baseEnd_1799045] using wordTrace_append hprefix tailTrace_1799045
  have hstable : (prefixWord ++ tailWord_1799045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799045).length < 2 ^ (prefixWord ++ tailWord_1799045).sum := by decide
  have hdescent : baseEnd_1799045 < baseStart_1799045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799081 : List Nat := [1, 2, 1, 1, 1, 1, 7, 4, 5]
def baseStart_1799081 : Nat := 118140960795 + 1799081 * 2 ^ 59
def prefixEnd_1799081 : Nat := 4983230072969 + 3 ^ 40 * 1799081 * 2
def baseEnd_1799081 : Nat := 102643698819064535668187

theorem tailTrace_1799081 : CollatzResearch.WordTrace tailWord_1799081 prefixEnd_1799081 102643698819064535668187 := by
  unfold tailWord_1799081
  simp only [CollatzResearch.WordTrace]
  refine ⟨65617874795244270417805097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43745249863496180278536731 65617874795244270417805097)
  ·
    refine ⟨49213406096433202813353823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65617874795244270417805097 49213406096433202813353823)
    ·
      refine ⟨73820109144649804220030735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49213406096433202813353823 73820109144649804220030735)
      ·
        refine ⟨110730163716974706330046103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73820109144649804220030735 110730163716974706330046103)
        ·
          refine ⟨166095245575462059495069155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110730163716974706330046103 166095245575462059495069155)
          ·
            refine ⟨249142868363193089242603733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166095245575462059495069155 249142868363193089242603733)
            ·
              refine ⟨5839285977262338029123525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 249142868363193089242603733 5839285977262338029123525)
              ·
                refine ⟨1094866120736688380460661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5839285977262338029123525 1094866120736688380460661)
                ·
                  refine ⟨102643698819064535668187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1094866120736688380460661 102643698819064535668187)
                  ·
                    rfl

theorem cell23_1799081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 5].length) (baseStart_1799081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799081 prefixEnd_1799081 := by exact prefixLift 1799081
  have htrace : WordTrace (prefixWord ++ tailWord_1799081) baseStart_1799081 baseEnd_1799081 := by
    simpa [prefixWord, tailWord_1799081, baseEnd_1799081] using wordTrace_append hprefix tailTrace_1799081
  have hstable : (prefixWord ++ tailWord_1799081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799081).length < 2 ^ (prefixWord ++ tailWord_1799081).sum := by decide
  have hdescent : baseEnd_1799081 < baseStart_1799081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799092 : List Nat := [2, 5, 2, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_1799092 : Nat := 118140960795 + 1799092 * 2 ^ 59
def prefixEnd_1799092 : Nat := 4983230072969 + 3 ^ 40 * 1799092 * 2
def baseEnd_1799092 : Nat := 923798937658780277976133

theorem tailTrace_1799092 : CollatzResearch.WordTrace tailWord_1799092 prefixEnd_1799092 923798937658780277976133 := by
  unfold tailWord_1799092
  simp only [CollatzResearch.WordTrace]
  refine ⟨32809137999102209648227765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43745517332136279530970353 32809137999102209648227765)
  ·
    refine ⟨3075856687415832154521353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32809137999102209648227765 3075856687415832154521353)
    ·
      refine ⟨2306892515561874115891015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3075856687415832154521353 2306892515561874115891015)
      ·
        refine ⟨3460338773342811173836523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2306892515561874115891015 3460338773342811173836523)
        ·
          refine ⟨5190508160014216760754785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3460338773342811173836523 5190508160014216760754785)
          ·
            refine ⟨3892881120010662570566089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5190508160014216760754785 3892881120010662570566089)
            ·
              refine ⟨2919660840007996927924567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3892881120010662570566089 2919660840007996927924567)
              ·
                refine ⟨4379491260011995391886851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2919660840007996927924567 4379491260011995391886851)
                ·
                  refine ⟨6569236890017993087830277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4379491260011995391886851 6569236890017993087830277)
                  ·
                    refine ⟨1231731916878373703968177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6569236890017993087830277 1231731916878373703968177)
                    ·
                      refine ⟨923798937658780277976133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231731916878373703968177 923798937658780277976133)
                      ·
                        rfl

theorem cell23_1799092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_1799092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799092 prefixEnd_1799092 := by exact prefixLift 1799092
  have htrace : WordTrace (prefixWord ++ tailWord_1799092) baseStart_1799092 baseEnd_1799092 := by
    simpa [prefixWord, tailWord_1799092, baseEnd_1799092] using wordTrace_append hprefix tailTrace_1799092
  have hstable : (prefixWord ++ tailWord_1799092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799092).length < 2 ^ (prefixWord ++ tailWord_1799092).sum := by decide
  have hdescent : baseEnd_1799092 < baseStart_1799092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799111 : List Nat := [1, 1, 4, 1, 1, 2, 5, 1, 2, 5]
def baseStart_1799111 : Nat := 118140960795 + 1799111 * 2 ^ 59
def prefixEnd_1799111 : Nat := 4983230072969 + 3 ^ 40 * 1799111 * 2
def baseEnd_1799111 : Nat := 307936231263738567879515

theorem tailTrace_1799111 : CollatzResearch.WordTrace tailWord_1799111 prefixEnd_1799111 307936231263738567879515 := by
  unfold tailWord_1799111
  simp only [CollatzResearch.WordTrace]
  refine ⟨65618968985135585541397187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43745979323423723694264791 65618968985135585541397187)
  ·
    refine ⟨98428453477703378312095781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65618968985135585541397187 98428453477703378312095781)
    ·
      refine ⟨18455335027069383433517959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98428453477703378312095781 18455335027069383433517959)
      ·
        refine ⟨27683002540604075150276939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18455335027069383433517959 27683002540604075150276939)
        ·
          refine ⟨41524503810906112725415409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27683002540604075150276939 41524503810906112725415409)
          ·
            refine ⟨31143377858179584544061557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41524503810906112725415409 31143377858179584544061557)
            ·
              refine ⟨2919691674204336051005771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31143377858179584544061557 2919691674204336051005771)
              ·
                refine ⟨4379537511306504076508657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2919691674204336051005771 4379537511306504076508657)
                ·
                  refine ⟨3284653133479878057381493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4379537511306504076508657 3284653133479878057381493)
                  ·
                    refine ⟨307936231263738567879515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3284653133479878057381493 307936231263738567879515)
                    ·
                      rfl

theorem cell23_1799111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_1799111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799111 prefixEnd_1799111 := by exact prefixLift 1799111
  have htrace : WordTrace (prefixWord ++ tailWord_1799111) baseStart_1799111 baseEnd_1799111 := by
    simpa [prefixWord, tailWord_1799111, baseEnd_1799111] using wordTrace_append hprefix tailTrace_1799111
  have hstable : (prefixWord ++ tailWord_1799111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799111).length < 2 ^ (prefixWord ++ tailWord_1799111).sum := by decide
  have hdescent : baseEnd_1799111 < baseStart_1799111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799151 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 3]
def baseStart_1799151 : Nat := 118140960795 + 1799151 * 2 ^ 59
def prefixEnd_1799151 : Nat := 4983230072969 + 3 ^ 40 * 1799151 * 2
def baseEnd_1799151 : Nat := 923829233017395547138361

theorem tailTrace_1799151 : CollatzResearch.WordTrace tailWord_1799151 prefixEnd_1799151 923829233017395547138361 := by
  unfold tailWord_1799151
  simp only [CollatzResearch.WordTrace]
  refine ⟨65620427904990672372853307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43746951936660448248568871 65620427904990672372853307)
  ·
    refine ⟨98430641857486008559279961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65620427904990672372853307 98430641857486008559279961)
    ·
      refine ⟨73822981393114506419459971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98430641857486008559279961 73822981393114506419459971)
      ·
        refine ⟨110734472089671759629189957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73822981393114506419459971 110734472089671759629189957)
        ·
          refine ⟨20762713516813454930473117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110734472089671759629189957 20762713516813454930473117)
          ·
            refine ⟨7786017568805045598927419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20762713516813454930473117 7786017568805045598927419)
            ·
              refine ⟨11679026353207568398391129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7786017568805045598927419 11679026353207568398391129)
              ·
                refine ⟨8759269764905676298793347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11679026353207568398391129 8759269764905676298793347)
                ·
                  refine ⟨13138904647358514448190021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8759269764905676298793347 13138904647358514448190021)
                  ·
                    refine ⟨2463544621379721459035629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13138904647358514448190021 2463544621379721459035629)
                    ·
                      refine ⟨923829233017395547138361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2463544621379721459035629 923829233017395547138361)
                      ·
                        rfl

theorem cell23_1799151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 3].length) (baseStart_1799151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799151 prefixEnd_1799151 := by exact prefixLift 1799151
  have htrace : WordTrace (prefixWord ++ tailWord_1799151) baseStart_1799151 baseEnd_1799151 := by
    simpa [prefixWord, tailWord_1799151, baseEnd_1799151] using wordTrace_append hprefix tailTrace_1799151
  have hstable : (prefixWord ++ tailWord_1799151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799151).length < 2 ^ (prefixWord ++ tailWord_1799151).sum := by decide
  have hdescent : baseEnd_1799151 < baseStart_1799151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799192 : List Nat := [2, 1, 2, 3, 2, 3, 3, 2, 1, 4]
def baseStart_1799192 : Nat := 118140960795 + 1799192 * 2 ^ 59
def prefixEnd_1799192 : Nat := 4983230072969 + 3 ^ 40 * 1799192 * 2
def baseEnd_1799192 : Nat := 307950095241409962241891

theorem tailTrace_1799192 : CollatzResearch.WordTrace tailWord_1799192 prefixEnd_1799192 307950095241409962241891 := by
  unfold tailWord_1799192
  simp only [CollatzResearch.WordTrace]
  refine ⟨32810961648921068187547915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43747948865228090916730553 32810961648921068187547915)
  ·
    refine ⟨49216442473381602281321873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32810961648921068187547915 49216442473381602281321873)
    ·
      refine ⟨36912331855036201710991405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49216442473381602281321873 36912331855036201710991405)
      ·
        refine ⟨13842124445638575641621777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36912331855036201710991405 13842124445638575641621777)
        ·
          refine ⟨10381593334228931731216333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13842124445638575641621777 10381593334228931731216333)
          ·
            refine ⟨3893097500335849399206125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10381593334228931731216333 3893097500335849399206125)
            ·
              refine ⟨1459911562625943524702297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3893097500335849399206125 1459911562625943524702297)
              ·
                refine ⟨1094933671969457643526723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1459911562625943524702297 1094933671969457643526723)
                ·
                  refine ⟨1642400507954186465290085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1094933671969457643526723 1642400507954186465290085)
                  ·
                    refine ⟨307950095241409962241891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1642400507954186465290085 307950095241409962241891)
                    ·
                      rfl

theorem cell23_1799192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 1, 4].length) (baseStart_1799192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799192 prefixEnd_1799192 := by exact prefixLift 1799192
  have htrace : WordTrace (prefixWord ++ tailWord_1799192) baseStart_1799192 baseEnd_1799192 := by
    simpa [prefixWord, tailWord_1799192, baseEnd_1799192] using wordTrace_append hprefix tailTrace_1799192
  have hstable : (prefixWord ++ tailWord_1799192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799192).length < 2 ^ (prefixWord ++ tailWord_1799192).sum := by decide
  have hdescent : baseEnd_1799192 < baseStart_1799192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799225 : List Nat := [1, 2, 1, 5, 2, 1, 1, 3, 2, 3, 2]
def baseStart_1799225 : Nat := 118140960795 + 1799225 * 2 ^ 59
def prefixEnd_1799225 : Nat := 4983230072969 + 3 ^ 40 * 1799225 * 2
def baseEnd_1799225 : Nat := 923867230585828257613021

theorem tailTrace_1799225 : CollatzResearch.WordTrace tailWord_1799225 prefixEnd_1799225 923867230585828257613021 := by
  unfold tailWord_1799225
  simp only [CollatzResearch.WordTrace]
  refine ⟨65623126906722583011047129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43748751271148388674031419 65623126906722583011047129)
  ·
    refine ⟨49217345180041937258285347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65623126906722583011047129 49217345180041937258285347)
    ·
      refine ⟨73826017770062905887428021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49217345180041937258285347 73826017770062905887428021)
      ·
        refine ⟨6921189165943397426946377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73826017770062905887428021 6921189165943397426946377)
        ·
          refine ⟨5190891874457548070209783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6921189165943397426946377 5190891874457548070209783)
          ·
            refine ⟨7786337811686322105314675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5190891874457548070209783 7786337811686322105314675)
            ·
              refine ⟨11679506717529483157972013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7786337811686322105314675 11679506717529483157972013)
              ·
                refine ⟨4379815019073556184239505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11679506717529483157972013 4379815019073556184239505)
                ·
                  refine ⟨3284861264305167138179629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4379815019073556184239505 3284861264305167138179629)
                  ·
                    refine ⟨1231822974114437676817361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3284861264305167138179629 1231822974114437676817361)
                    ·
                      refine ⟨923867230585828257613021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231822974114437676817361 923867230585828257613021)
                      ·
                        rfl

theorem cell23_1799225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_1799225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799225 prefixEnd_1799225 := by exact prefixLift 1799225
  have htrace : WordTrace (prefixWord ++ tailWord_1799225) baseStart_1799225 baseEnd_1799225 := by
    simpa [prefixWord, tailWord_1799225, baseEnd_1799225] using wordTrace_append hprefix tailTrace_1799225
  have hstable : (prefixWord ++ tailWord_1799225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799225).length < 2 ^ (prefixWord ++ tailWord_1799225).sum := by decide
  have hdescent : baseEnd_1799225 < baseStart_1799225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799241 : List Nat := [1, 2, 1, 1, 2, 2, 2, 5, 1, 1, 5]
def baseStart_1799241 : Nat := 118140960795 + 1799241 * 2 ^ 59
def prefixEnd_1799241 : Nat := 4983230072969 + 3 ^ 40 * 1799241 * 2
def baseEnd_1799241 : Nat := 923875446276300195012947

theorem tailTrace_1799241 : CollatzResearch.WordTrace tailWord_1799241 prefixEnd_1799241 923875446276300195012947 := by
  unfold tailWord_1799241
  simp only [CollatzResearch.WordTrace]
  refine ⟨65623710474664617743629577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43749140316443078495753051 65623710474664617743629577)
  ·
    refine ⟨49217782855998463307722183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65623710474664617743629577 49217782855998463307722183)
    ·
      refine ⟨73826674283997694961583275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49217782855998463307722183 73826674283997694961583275)
      ·
        refine ⟨110740011425996542442374913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73826674283997694961583275 110740011425996542442374913)
        ·
          refine ⟨83055008569497406831781185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110740011425996542442374913 83055008569497406831781185)
          ·
            refine ⟨62291256427123055123835889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83055008569497406831781185 62291256427123055123835889)
            ·
              refine ⟨46718442320342291342876917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62291256427123055123835889 46718442320342291342876917)
              ·
                refine ⟨4379853967532089813394711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46718442320342291342876917 4379853967532089813394711)
                ·
                  refine ⟨6569780951298134720092067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4379853967532089813394711 6569780951298134720092067)
                  ·
                    refine ⟨9854671426947202080138101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6569780951298134720092067 9854671426947202080138101)
                    ·
                      refine ⟨923875446276300195012947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9854671426947202080138101 923875446276300195012947)
                      ·
                        rfl

theorem cell23_1799241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 1, 5].length) (baseStart_1799241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799241 prefixEnd_1799241 := by exact prefixLift 1799241
  have htrace : WordTrace (prefixWord ++ tailWord_1799241) baseStart_1799241 baseEnd_1799241 := by
    simpa [prefixWord, tailWord_1799241, baseEnd_1799241] using wordTrace_append hprefix tailTrace_1799241
  have hstable : (prefixWord ++ tailWord_1799241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799241).length < 2 ^ (prefixWord ++ tailWord_1799241).sum := by decide
  have hdescent : baseEnd_1799241 < baseStart_1799241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799255 : List Nat := [1, 1, 3, 2, 2, 1, 1, 5, 3, 2, 2]
def baseStart_1799255 : Nat := 118140960795 + 1799255 * 2 ^ 59
def prefixEnd_1799255 : Nat := 4983230072969 + 3 ^ 40 * 1799255 * 2
def baseEnd_1799255 : Nat := 923882635005463140237883

theorem tailTrace_1799255 : CollatzResearch.WordTrace tailWord_1799255 prefixEnd_1799255 923882635005463140237883 := by
  unfold tailWord_1799255
  simp only [CollatzResearch.WordTrace]
  refine ⟨65624221096613898134639219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43749480731075932089759479 65624221096613898134639219)
  ·
    refine ⟨98436331644920847201958829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65624221096613898134639219 98436331644920847201958829)
    ·
      refine ⟨36913624366845317700734561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98436331644920847201958829 36913624366845317700734561)
      ·
        refine ⟨27685218275133988275550921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36913624366845317700734561 27685218275133988275550921)
        ·
          refine ⟨20763913706350491206663191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27685218275133988275550921 20763913706350491206663191)
          ·
            refine ⟨31145870559525736809994787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20763913706350491206663191 31145870559525736809994787)
            ·
              refine ⟨46718805839288605214992181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31145870559525736809994787 46718805839288605214992181)
              ·
                refine ⟨4379888047433306738905517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46718805839288605214992181 4379888047433306738905517)
                ·
                  refine ⟨1642458017787490027089569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4379888047433306738905517 1642458017787490027089569)
                  ·
                    refine ⟨1231843513340617520317177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1642458017787490027089569 1231843513340617520317177)
                    ·
                      refine ⟨923882635005463140237883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231843513340617520317177 923882635005463140237883)
                      ·
                        rfl

theorem cell23_1799255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_1799255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799255 prefixEnd_1799255 := by exact prefixLift 1799255
  have htrace : WordTrace (prefixWord ++ tailWord_1799255) baseStart_1799255 baseEnd_1799255 := by
    simpa [prefixWord, tailWord_1799255, baseEnd_1799255] using wordTrace_append hprefix tailTrace_1799255
  have hstable : (prefixWord ++ tailWord_1799255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799255).length < 2 ^ (prefixWord ++ tailWord_1799255).sum := by decide
  have hdescent : baseEnd_1799255 < baseStart_1799255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799288 : List Nat := [2, 1, 2, 1, 1, 1, 6, 2, 1, 3, 3]
def baseStart_1799288 : Nat := 118140960795 + 1799288 * 2 ^ 59
def prefixEnd_1799288 : Nat := 4983230072969 + 3 ^ 40 * 1799288 * 2
def baseEnd_1799288 : Nat := 923899579867061511125231

theorem tailTrace_1799288 : CollatzResearch.WordTrace tailWord_1799288 prefixEnd_1799288 923899579867061511125231 := by
  unfold tailWord_1799288
  simp only [CollatzResearch.WordTrace]
  refine ⟨32812712352747172385295259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43750283136996229847060345 32812712352747172385295259)
  ·
    refine ⟨49219068529120758577942889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32812712352747172385295259 49219068529120758577942889)
    ·
      refine ⟨36914301396840568933457167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49219068529120758577942889 36914301396840568933457167)
      ·
        refine ⟨55371452095260853400185751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36914301396840568933457167 55371452095260853400185751)
        ·
          refine ⟨83057178142891280100278627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55371452095260853400185751 83057178142891280100278627)
          ·
            refine ⟨124585767214336920150417941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83057178142891280100278627 124585767214336920150417941)
            ·
              refine ⟨5839957838172043132050841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124585767214336920150417941 5839957838172043132050841)
              ·
                refine ⟨4379968378629032349038131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5839957838172043132050841 4379968378629032349038131)
                ·
                  refine ⟨6569952567943548523557197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4379968378629032349038131 6569952567943548523557197)
                  ·
                    refine ⟨2463732212978830696333949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6569952567943548523557197 2463732212978830696333949)
                    ·
                      refine ⟨923899579867061511125231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2463732212978830696333949 923899579867061511125231)
                      ·
                        rfl

theorem cell23_1799288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_1799288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799288 prefixEnd_1799288 := by exact prefixLift 1799288
  have htrace : WordTrace (prefixWord ++ tailWord_1799288) baseStart_1799288 baseEnd_1799288 := by
    simpa [prefixWord, tailWord_1799288, baseEnd_1799288] using wordTrace_append hprefix tailTrace_1799288
  have hstable : (prefixWord ++ tailWord_1799288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799288).length < 2 ^ (prefixWord ++ tailWord_1799288).sum := by decide
  have hdescent : baseEnd_1799288 < baseStart_1799288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799289 : List Nat := [1, 2, 1, 3, 6, 1, 2, 1, 1, 1, 4]
def baseStart_1799289 : Nat := 118140960795 + 1799289 * 2 ^ 59
def prefixEnd_1799289 : Nat := 4983230072969 + 3 ^ 40 * 1799289 * 2
def baseEnd_1799289 : Nat := 923900093347716007212727

theorem tailTrace_1799289 : CollatzResearch.WordTrace tailWord_1799289 prefixEnd_1799289 923900093347716007212727 := by
  unfold tailWord_1799289
  simp only [CollatzResearch.WordTrace]
  refine ⟨65625461178490721941376921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43750307452327147960917947 65625461178490721941376921)
  ·
    refine ⟨49219095883868041456032691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65625461178490721941376921 49219095883868041456032691)
    ·
      refine ⟨73828643825802062184049037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49219095883868041456032691 73828643825802062184049037)
      ·
        refine ⟨27685741434675773319018389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73828643825802062184049037 27685741434675773319018389)
        ·
          refine ⟨1297769129750426874328987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27685741434675773319018389 1297769129750426874328987)
          ·
            refine ⟨1946653694625640311493481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1297769129750426874328987 1946653694625640311493481)
            ·
              refine ⟨1459990270969230233620111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1946653694625640311493481 1459990270969230233620111)
              ·
                refine ⟨2189985406453845350430167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1459990270969230233620111 2189985406453845350430167)
                ·
                  refine ⟨3284978109680768025645251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2189985406453845350430167 3284978109680768025645251)
                  ·
                    refine ⟨4927467164521152038467877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3284978109680768025645251 4927467164521152038467877)
                    ·
                      refine ⟨923900093347716007212727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4927467164521152038467877 923900093347716007212727)
                      ·
                        rfl

theorem cell23_1799289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_1799289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799289 prefixEnd_1799289 := by exact prefixLift 1799289
  have htrace : WordTrace (prefixWord ++ tailWord_1799289) baseStart_1799289 baseEnd_1799289 := by
    simpa [prefixWord, tailWord_1799289, baseEnd_1799289] using wordTrace_append hprefix tailTrace_1799289
  have hstable : (prefixWord ++ tailWord_1799289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799289).length < 2 ^ (prefixWord ++ tailWord_1799289).sum := by decide
  have hdescent : baseEnd_1799289 < baseStart_1799289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799305 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 4, 1, 3]
def baseStart_1799305 : Nat := 118140960795 + 1799305 * 2 ^ 59
def prefixEnd_1799305 : Nat := 4983230072969 + 3 ^ 40 * 1799305 * 2
def baseEnd_1799305 : Nat := 923908309038187944612653

theorem tailTrace_1799305 : CollatzResearch.WordTrace tailWord_1799305 prefixEnd_1799305 923908309038187944612653 := by
  unfold tailWord_1799305
  simp only [CollatzResearch.WordTrace]
  refine ⟨65626044746432756673959369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43750696497621837782639579 65626044746432756673959369)
  ·
    refine ⟨49219533559824567505469527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65626044746432756673959369 49219533559824567505469527)
    ·
      refine ⟨73829300339736851258204291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49219533559824567505469527 73829300339736851258204291)
      ·
        refine ⟨110743950509605276887306437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73829300339736851258204291 110743950509605276887306437)
        ·
          refine ⟨20764490720550989416369957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110743950509605276887306437 20764490720550989416369957)
          ·
            refine ⟨3893342010103310515569367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20764490720550989416369957 3893342010103310515569367)
            ·
              refine ⟨5840013015154965773354051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3893342010103310515569367 5840013015154965773354051)
              ·
                refine ⟨8760019522732448660031077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5840013015154965773354051 8760019522732448660031077)
                ·
                  refine ⟨1642503660512334123755827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8760019522732448660031077 1642503660512334123755827)
                  ·
                    refine ⟨2463755490768501185633741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1642503660512334123755827 2463755490768501185633741)
                    ·
                      refine ⟨923908309038187944612653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2463755490768501185633741 923908309038187944612653)
                      ·
                        rfl

theorem cell23_1799305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 1, 3].length) (baseStart_1799305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799305 prefixEnd_1799305 := by exact prefixLift 1799305
  have htrace : WordTrace (prefixWord ++ tailWord_1799305) baseStart_1799305 baseEnd_1799305 := by
    simpa [prefixWord, tailWord_1799305, baseEnd_1799305] using wordTrace_append hprefix tailTrace_1799305
  have hstable : (prefixWord ++ tailWord_1799305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799305).length < 2 ^ (prefixWord ++ tailWord_1799305).sum := by decide
  have hdescent : baseEnd_1799305 < baseStart_1799305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799311 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 4]
def baseStart_1799311 : Nat := 118140960795 + 1799311 * 2 ^ 59
def prefixEnd_1799311 : Nat := 4983230072969 + 3 ^ 40 * 1799311 * 2
def baseEnd_1799311 : Nat := 923911389922114921137625

theorem tailTrace_1799311 : CollatzResearch.WordTrace tailWord_1799311 prefixEnd_1799311 923911389922114921137625 := by
  unfold tailWord_1799311
  simp only [CollatzResearch.WordTrace]
  refine ⟨65626263584411019698677787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43750842389607346465785191 65626263584411019698677787)
  ·
    refine ⟨98439395376616529548016681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65626263584411019698677787 98439395376616529548016681)
    ·
      refine ⟨73829546532462397161012511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98439395376616529548016681 73829546532462397161012511)
      ·
        refine ⟨110744319798693595741518767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73829546532462397161012511 110744319798693595741518767)
        ·
          refine ⟨166116479698040393612278151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110744319798693595741518767 166116479698040393612278151)
          ·
            refine ⟨249174719547060590418417227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166116479698040393612278151 249174719547060590418417227)
            ·
              refine ⟨373762079320590885627625841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249174719547060590418417227 373762079320590885627625841)
              ·
                refine ⟨280321559490443164220719381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373762079320590885627625841 280321559490443164220719381)
                ·
                  refine ⟨13140073101114523322846221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 280321559490443164220719381 13140073101114523322846221)
                  ·
                    refine ⟨4927527412917946246067333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13140073101114523322846221 4927527412917946246067333)
                    ·
                      refine ⟨923911389922114921137625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4927527412917946246067333 923911389922114921137625)
                      ·
                        rfl

theorem cell23_1799311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_1799311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799311 prefixEnd_1799311 := by exact prefixLift 1799311
  have htrace : WordTrace (prefixWord ++ tailWord_1799311) baseStart_1799311 baseEnd_1799311 := by
    simpa [prefixWord, tailWord_1799311, baseEnd_1799311] using wordTrace_append hprefix tailTrace_1799311
  have hstable : (prefixWord ++ tailWord_1799311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799311).length < 2 ^ (prefixWord ++ tailWord_1799311).sum := by decide
  have hdescent : baseEnd_1799311 < baseStart_1799311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799322 : List Nat := [3, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3]
def baseStart_1799322 : Nat := 118140960795 + 1799322 * 2 ^ 59
def prefixEnd_1799322 : Nat := 4983230072969 + 3 ^ 40 * 1799322 * 2
def baseEnd_1799322 : Nat := 923917038209314378100075

theorem tailTrace_1799322 : CollatzResearch.WordTrace tailWord_1799322 prefixEnd_1799322 923917038209314378100075 := by
  unfold tailWord_1799322
  simp only [CollatzResearch.WordTrace]
  refine ⟨16406666196842792144332055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43751109858247445718218813 16406666196842792144332055)
  ·
    refine ⟨24609999295264188216498083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16406666196842792144332055 24609999295264188216498083)
    ·
      refine ⟨36914998942896282324747125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24609999295264188216498083 36914998942896282324747125)
      ·
        refine ⟨3460781150896526467945043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36914998942896282324747125 3460781150896526467945043)
        ·
          refine ⟨5191171726344789701917565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3460781150896526467945043 5191171726344789701917565)
          ·
            refine ⟨1946689397379296138219087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5191171726344789701917565 1946689397379296138219087)
            ·
              refine ⟨2920034096068944207328631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1946689397379296138219087 2920034096068944207328631)
              ·
                refine ⟨4380051144103416310992947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2920034096068944207328631 4380051144103416310992947)
                ·
                  refine ⟨6570076716155124466489421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4380051144103416310992947 6570076716155124466489421)
                  ·
                    refine ⟨2463778768558171674933533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6570076716155124466489421 2463778768558171674933533)
                    ·
                      refine ⟨923917038209314378100075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2463778768558171674933533 923917038209314378100075)
                      ·
                        rfl

theorem cell23_1799322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_1799322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799322 prefixEnd_1799322 := by exact prefixLift 1799322
  have htrace : WordTrace (prefixWord ++ tailWord_1799322) baseStart_1799322 baseEnd_1799322 := by
    simpa [prefixWord, tailWord_1799322, baseEnd_1799322] using wordTrace_append hprefix tailTrace_1799322
  have hstable : (prefixWord ++ tailWord_1799322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799322).length < 2 ^ (prefixWord ++ tailWord_1799322).sum := by decide
  have hdescent : baseEnd_1799322 < baseStart_1799322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799331 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 5]
def baseStart_1799331 : Nat := 118140960795 + 1799331 * 2 ^ 59
def prefixEnd_1799331 : Nat := 4983230072969 + 3 ^ 40 * 1799331 * 2
def baseEnd_1799331 : Nat := 923921659535204842887533

theorem tailTrace_1799331 : CollatzResearch.WordTrace tailWord_1799331 prefixEnd_1799331 923921659535204842887533 := by
  unfold tailWord_1799331
  simp only [CollatzResearch.WordTrace]
  refine ⟨65626993044338563114405847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43751328696225708742937231 65626993044338563114405847)
  ·
    refine ⟨98440489566507844671608771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65626993044338563114405847 98440489566507844671608771)
    ·
      refine ⟨147660734349761767007413157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98440489566507844671608771 147660734349761767007413157)
      ·
        refine ⟨27686387690580331313889967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147660734349761767007413157 27686387690580331313889967)
        ·
          refine ⟨41529581535870496970834951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27686387690580331313889967 41529581535870496970834951)
          ·
            refine ⟨62294372303805745456252427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41529581535870496970834951 62294372303805745456252427)
            ·
              refine ⟨93441558455708618184378641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62294372303805745456252427 93441558455708618184378641)
              ·
                refine ⟨70081168841781463638283981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93441558455708618184378641 70081168841781463638283981)
                ·
                  refine ⟨26280438315668048864356493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70081168841781463638283981 26280438315668048864356493)
                  ·
                    refine ⟨9855164368375518324133685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26280438315668048864356493 9855164368375518324133685)
                    ·
                      refine ⟨923921659535204842887533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9855164368375518324133685 923921659535204842887533)
                      ·
                        rfl

theorem cell23_1799331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_1799331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799331 prefixEnd_1799331 := by exact prefixLift 1799331
  have htrace : WordTrace (prefixWord ++ tailWord_1799331) baseStart_1799331 baseEnd_1799331 := by
    simpa [prefixWord, tailWord_1799331, baseEnd_1799331] using wordTrace_append hprefix tailTrace_1799331
  have hstable : (prefixWord ++ tailWord_1799331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799331).length < 2 ^ (prefixWord ++ tailWord_1799331).sum := by decide
  have hdescent : baseEnd_1799331 < baseStart_1799331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799332 : List Nat := [2, 3, 1, 2, 3, 1, 1, 4, 1, 3, 2]
def baseStart_1799332 : Nat := 118140960795 + 1799332 * 2 ^ 59
def prefixEnd_1799332 : Nat := 4983230072969 + 3 ^ 40 * 1799332 * 2
def baseEnd_1799332 : Nat := 923922173015859338975029

theorem tailTrace_1799332 : CollatzResearch.WordTrace tailWord_1799332 prefixEnd_1799332 923922173015859338975029 := by
  unfold tailWord_1799332
  simp only [CollatzResearch.WordTrace]
  refine ⟨32813514758667470142596125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43751353011556626856794833 32813514758667470142596125)
  ·
    refine ⟨12305068034500301303473547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32813514758667470142596125 12305068034500301303473547)
    ·
      refine ⟨18457602051750451955210321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12305068034500301303473547 18457602051750451955210321)
      ·
        refine ⟨13843201538812838966407741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18457602051750451955210321 13843201538812838966407741)
        ·
          refine ⟨5191200577054814612402903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13843201538812838966407741 5191200577054814612402903)
          ·
            refine ⟨7786800865582221918604355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5191200577054814612402903 7786800865582221918604355)
            ·
              refine ⟨11680201298373332877906533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7786800865582221918604355 11680201298373332877906533)
              ·
                refine ⟨2190037743444999914607475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11680201298373332877906533 2190037743444999914607475)
                ·
                  refine ⟨3285056615167499871911213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2190037743444999914607475 3285056615167499871911213)
                  ·
                    refine ⟨1231896230687812451966705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3285056615167499871911213 1231896230687812451966705)
                    ·
                      refine ⟨923922173015859338975029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231896230687812451966705 923922173015859338975029)
                      ·
                        rfl

theorem cell23_1799332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_1799332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799332 prefixEnd_1799332 := by exact prefixLift 1799332
  have htrace : WordTrace (prefixWord ++ tailWord_1799332) baseStart_1799332 baseEnd_1799332 := by
    simpa [prefixWord, tailWord_1799332, baseEnd_1799332] using wordTrace_append hprefix tailTrace_1799332
  have hstable : (prefixWord ++ tailWord_1799332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799332).length < 2 ^ (prefixWord ++ tailWord_1799332).sum := by decide
  have hdescent : baseEnd_1799332 < baseStart_1799332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799368 : List Nat := [2, 1, 3, 1, 2, 1, 5, 1, 7]
def baseStart_1799368 : Nat := 118140960795 + 1799368 * 2 ^ 59
def prefixEnd_1799368 : Nat := 4983230072969 + 3 ^ 40 * 1799368 * 2
def baseEnd_1799368 : Nat := 102660073146602355347207

theorem tailTrace_1799368 : CollatzResearch.WordTrace tailWord_1799368 prefixEnd_1799368 102660073146602355347207 := by
  unfold tailWord_1799368
  simp only [CollatzResearch.WordTrace]
  refine ⟨32814171272602259216751379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43752228363469678955668505 32814171272602259216751379)
  ·
    refine ⟨49221256908903388825127069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32814171272602259216751379 49221256908903388825127069)
    ·
      refine ⟨18457971340838770809422651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49221256908903388825127069 18457971340838770809422651)
      ·
        refine ⟨27686957011258156214133977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18457971340838770809422651 27686957011258156214133977)
        ·
          refine ⟨20765217758443617160600483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27686957011258156214133977 20765217758443617160600483)
          ·
            refine ⟨31147826637665425740900725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20765217758443617160600483 31147826637665425740900725)
            ·
              refine ⟨2920108747281133663209443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31147826637665425740900725 2920108747281133663209443)
              ·
                refine ⟨4380163120921700494814165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2920108747281133663209443 4380163120921700494814165)
                ·
                  refine ⟨102660073146602355347207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4380163120921700494814165 102660073146602355347207)
                  ·
                    rfl

theorem cell23_1799368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 7].length) (baseStart_1799368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799368 prefixEnd_1799368 := by exact prefixLift 1799368
  have htrace : WordTrace (prefixWord ++ tailWord_1799368) baseStart_1799368 baseEnd_1799368 := by
    simpa [prefixWord, tailWord_1799368, baseEnd_1799368] using wordTrace_append hprefix tailTrace_1799368
  have hstable : (prefixWord ++ tailWord_1799368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799368).length < 2 ^ (prefixWord ++ tailWord_1799368).sum := by decide
  have hdescent : baseEnd_1799368 < baseStart_1799368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799371 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 8]
def baseStart_1799371 : Nat := 118140960795 + 1799371 * 2 ^ 59
def prefixEnd_1799371 : Nat := 4983230072969 + 3 ^ 40 * 1799371 * 2
def baseEnd_1799371 : Nat := 923942198761384686387349

theorem tailTrace_1799371 : CollatzResearch.WordTrace tailWord_1799371 prefixEnd_1799371 923942198761384686387349 := by
  unfold tailWord_1799371
  simp only [CollatzResearch.WordTrace]
  refine ⟨65628451964193649945861967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43752301309462433297241311 65628451964193649945861967)
  ·
    refine ⟨98442677946290474918792951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65628451964193649945861967 98442677946290474918792951)
    ·
      refine ⟨147664016919435712378189427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98442677946290474918792951 147664016919435712378189427)
      ·
        refine ⟨221496025379153568567284141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147664016919435712378189427 221496025379153568567284141)
        ·
          refine ⟨83061009517182588212731553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221496025379153568567284141 83061009517182588212731553)
          ·
            refine ⟨62295757137886941159548665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83061009517182588212731553 62295757137886941159548665)
            ·
              refine ⟨46721817853415205869661499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62295757137886941159548665 46721817853415205869661499)
              ·
                refine ⟨70082726780122808804492249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46721817853415205869661499 70082726780122808804492249)
                ·
                  refine ⟨52562045085092106603369187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70082726780122808804492249 52562045085092106603369187)
                  ·
                    refine ⟨78843067627638159905053781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52562045085092106603369187 78843067627638159905053781)
                    ·
                      refine ⟨923942198761384686387349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 78843067627638159905053781 923942198761384686387349)
                      ·
                        rfl

theorem cell23_1799371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 8].length) (baseStart_1799371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799371 prefixEnd_1799371 := by exact prefixLift 1799371
  have htrace : WordTrace (prefixWord ++ tailWord_1799371) baseStart_1799371 baseEnd_1799371 := by
    simpa [prefixWord, tailWord_1799371, baseEnd_1799371] using wordTrace_append hprefix tailTrace_1799371
  have hstable : (prefixWord ++ tailWord_1799371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799371).length < 2 ^ (prefixWord ++ tailWord_1799371).sum := by decide
  have hdescent : baseEnd_1799371 < baseStart_1799371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799422 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_1799422 : Nat := 118140960795 + 1799422 * 2 ^ 59
def prefixEnd_1799422 : Nat := 4983230072969 + 3 ^ 40 * 1799422 * 2
def baseEnd_1799422 : Nat := 923968386274763986849615

theorem tailTrace_1799422 : CollatzResearch.WordTrace tailWord_1799422 prefixEnd_1799422 923968386274763986849615 := by
  unfold tailWord_1799422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8203789010876110706996065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43753541391339257103979013 8203789010876110706996065)
  ·
    refine ⟨6152841758157083030247049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8203789010876110706996065 6152841758157083030247049)
    ·
      refine ⟨4614631318617812272685287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6152841758157083030247049 4614631318617812272685287)
      ·
        refine ⟨6921946977926718409027931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4614631318617812272685287 6921946977926718409027931)
        ·
          refine ⟨10382920466890077613541897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6921946977926718409027931 10382920466890077613541897)
          ·
            refine ⟨7787190350167558210156423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10382920466890077613541897 7787190350167558210156423)
            ·
              refine ⟨11680785525251337315234635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7787190350167558210156423 11680785525251337315234635)
              ·
                refine ⟨17521178287877005972851953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11680785525251337315234635 17521178287877005972851953)
                ·
                  refine ⟨13140883715907754479638965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17521178287877005972851953 13140883715907754479638965)
                  ·
                    refine ⟨1231957848366351982466153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13140883715907754479638965 1231957848366351982466153)
                    ·
                      refine ⟨923968386274763986849615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231957848366351982466153 923968386274763986849615)
                      ·
                        rfl

theorem cell23_1799422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_1799422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799422 prefixEnd_1799422 := by exact prefixLift 1799422
  have htrace : WordTrace (prefixWord ++ tailWord_1799422) baseStart_1799422 baseEnd_1799422 := by
    simpa [prefixWord, tailWord_1799422, baseEnd_1799422] using wordTrace_append hprefix tailTrace_1799422
  have hstable : (prefixWord ++ tailWord_1799422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799422).length < 2 ^ (prefixWord ++ tailWord_1799422).sum := by decide
  have hdescent : baseEnd_1799422 < baseStart_1799422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799435 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 1, 6, 2]
def baseStart_1799435 : Nat := 118140960795 + 1799435 * 2 ^ 59
def prefixEnd_1799435 : Nat := 4983230072969 + 3 ^ 40 * 1799435 * 2
def baseEnd_1799435 : Nat := 923975061523272435987055

theorem tailTrace_1799435 : CollatzResearch.WordTrace tailWord_1799435 prefixEnd_1799435 923975061523272435987055 := by
  unfold tailWord_1799435
  simp only [CollatzResearch.WordTrace]
  refine ⟨65630786235961788876191759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43753857490641192584127839 65630786235961788876191759)
  ·
    refine ⟨98446179353942683314287639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65630786235961788876191759 98446179353942683314287639)
    ·
      refine ⟨147669269030914024971431459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98446179353942683314287639 147669269030914024971431459)
      ·
        refine ⟨221503903546371037457147189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147669269030914024971431459 221503903546371037457147189)
        ·
          refine ⟨20765990957472284761607549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221503903546371037457147189 20765990957472284761607549)
          ·
            refine ⟨7787246609052106785602831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20765990957472284761607549 7787246609052106785602831)
            ·
              refine ⟨11680869913578160178404247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7787246609052106785602831 11680869913578160178404247)
              ·
                refine ⟨17521304870367240267606371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11680869913578160178404247 17521304870367240267606371)
                ·
                  refine ⟨26281957305550860401409557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17521304870367240267606371 26281957305550860401409557)
                  ·
                    refine ⟨1231966748697696581316073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26281957305550860401409557 1231966748697696581316073)
                    ·
                      refine ⟨923975061523272435987055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231966748697696581316073 923975061523272435987055)
                      ·
                        rfl

theorem cell23_1799435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 6, 2].length) (baseStart_1799435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799435 prefixEnd_1799435 := by exact prefixLift 1799435
  have htrace : WordTrace (prefixWord ++ tailWord_1799435) baseStart_1799435 baseEnd_1799435 := by
    simpa [prefixWord, tailWord_1799435, baseEnd_1799435] using wordTrace_append hprefix tailTrace_1799435
  have hstable : (prefixWord ++ tailWord_1799435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799435).length < 2 ^ (prefixWord ++ tailWord_1799435).sum := by decide
  have hdescent : baseEnd_1799435 < baseStart_1799435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799469 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_1799469 : Nat := 118140960795 + 1799469 * 2 ^ 59
def prefixEnd_1799469 : Nat := 4983230072969 + 3 ^ 40 * 1799469 * 2
def baseEnd_1799469 : Nat := 923992519865525302961899

theorem tailTrace_1799469 : CollatzResearch.WordTrace tailWord_1799469 prefixEnd_1799469 923992519865525302961899 := by
  unfold tailWord_1799469
  simp only [CollatzResearch.WordTrace]
  refine ⟨65632026317838612682929461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43754684211892408455286307 65632026317838612682929461)
  ·
    refine ⟨6153002467297369939024637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65632026317838612682929461 6153002467297369939024637)
    ·
      refine ⟨2307375925236513727134239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6153002467297369939024637 2307375925236513727134239)
      ·
        refine ⟨3461063887854770590701359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2307375925236513727134239 3461063887854770590701359)
        ·
          refine ⟨5191595831782155886052039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3461063887854770590701359 5191595831782155886052039)
          ·
            refine ⟨7787393747673233829078059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5191595831782155886052039 7787393747673233829078059)
            ·
              refine ⟨11681090621509850743617089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7787393747673233829078059 11681090621509850743617089)
              ·
                refine ⟨8760817966132388057712817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11681090621509850743617089 8760817966132388057712817)
                ·
                  refine ⟨6570613474599291043284613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8760817966132388057712817 6570613474599291043284613)
                  ·
                    refine ⟨1231990026487367070615865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6570613474599291043284613 1231990026487367070615865)
                    ·
                      refine ⟨923992519865525302961899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231990026487367070615865 923992519865525302961899)
                      ·
                        rfl

theorem cell23_1799469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_1799469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799469 prefixEnd_1799469 := by exact prefixLift 1799469
  have htrace : WordTrace (prefixWord ++ tailWord_1799469) baseStart_1799469 baseEnd_1799469 := by
    simpa [prefixWord, tailWord_1799469, baseEnd_1799469] using wordTrace_append hprefix tailTrace_1799469
  have hstable : (prefixWord ++ tailWord_1799469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799469).length < 2 ^ (prefixWord ++ tailWord_1799469).sum := by decide
  have hdescent : baseEnd_1799469 < baseStart_1799469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799475 : List Nat := [1, 1, 1, 2, 5, 2, 3, 2, 6]
def baseStart_1799475 : Nat := 118140960795 + 1799475 * 2 ^ 59
def prefixEnd_1799475 : Nat := 4983230072969 + 3 ^ 40 * 1799475 * 2
def baseEnd_1799475 : Nat := 102666177861050253276319

theorem tailTrace_1799475 : CollatzResearch.WordTrace tailWord_1799475 prefixEnd_1799475 102666177861050253276319 := by
  unfold tailWord_1799475
  simp only [CollatzResearch.WordTrace]
  refine ⟨65632245155816875707647879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43754830103877917138431919 65632245155816875707647879)
  ·
    refine ⟨98448367733725313561471819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65632245155816875707647879 98448367733725313561471819)
    ·
      refine ⟨147672551600587970342207729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98448367733725313561471819 147672551600587970342207729)
      ·
        refine ⟨110754413700440977756655797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147672551600587970342207729 110754413700440977756655797)
        ·
          refine ⟨10383226284416341664686481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110754413700440977756655797 10383226284416341664686481)
          ·
            refine ⟨7787419713312256248514861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10383226284416341664686481 7787419713312256248514861)
            ·
              refine ⟨2920282392492096093193073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7787419713312256248514861 2920282392492096093193073)
              ·
                refine ⟨2190211794369072069894805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2920282392492096093193073 2190211794369072069894805)
                ·
                  refine ⟨102666177861050253276319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2190211794369072069894805 102666177861050253276319)
                  ·
                    rfl

theorem cell23_1799475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 6].length) (baseStart_1799475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799475 prefixEnd_1799475 := by exact prefixLift 1799475
  have htrace : WordTrace (prefixWord ++ tailWord_1799475) baseStart_1799475 baseEnd_1799475 := by
    simpa [prefixWord, tailWord_1799475, baseEnd_1799475] using wordTrace_append hprefix tailTrace_1799475
  have hstable : (prefixWord ++ tailWord_1799475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799475).length < 2 ^ (prefixWord ++ tailWord_1799475).sum := by decide
  have hdescent : baseEnd_1799475 < baseStart_1799475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799498 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_1799498 : Nat := 118140960795 + 1799498 * 2 ^ 59
def prefixEnd_1799498 : Nat := 4983230072969 + 3 ^ 40 * 1799498 * 2
def baseEnd_1799498 : Nat := 924007410804505689499265

theorem tailTrace_1799498 : CollatzResearch.WordTrace tailWord_1799498 prefixEnd_1799498 924007410804505689499265 := by
  unfold tailWord_1799498
  simp only [CollatzResearch.WordTrace]
  refine ⟨16408271008683387658933787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43755389356489033757156765 16408271008683387658933787)
  ·
    refine ⟨24612406513025081488400681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16408271008683387658933787 24612406513025081488400681)
    ·
      refine ⟨18459304884768811116300511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24612406513025081488400681 18459304884768811116300511)
      ·
        refine ⟨27688957327153216674450767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18459304884768811116300511 27688957327153216674450767)
        ·
          refine ⟨41533435990729825011676151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27688957327153216674450767 41533435990729825011676151)
          ·
            refine ⟨62300153986094737517514227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41533435990729825011676151 62300153986094737517514227)
            ·
              refine ⟨93450230979142106276271341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62300153986094737517514227 93450230979142106276271341)
              ·
                refine ⟨35043836617178289853601753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93450230979142106276271341 35043836617178289853601753)
                ·
                  refine ⟨26282877462883717390201315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35043836617178289853601753 26282877462883717390201315)
                  ·
                    refine ⟨39424316194325576085301973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26282877462883717390201315 39424316194325576085301973)
                    ·
                      refine ⟨924007410804505689499265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39424316194325576085301973 924007410804505689499265)
                      ·
                        rfl

theorem cell23_1799498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_1799498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799498 prefixEnd_1799498 := by exact prefixLift 1799498
  have htrace : WordTrace (prefixWord ++ tailWord_1799498) baseStart_1799498 baseEnd_1799498 := by
    simpa [prefixWord, tailWord_1799498, baseEnd_1799498] using wordTrace_append hprefix tailTrace_1799498
  have hstable : (prefixWord ++ tailWord_1799498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799498).length < 2 ^ (prefixWord ++ tailWord_1799498).sum := by decide
  have hdescent : baseEnd_1799498 < baseStart_1799498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799502 : List Nat := [4, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3]
def baseStart_1799502 : Nat := 118140960795 + 1799502 * 2 ^ 59
def prefixEnd_1799502 : Nat := 4983230072969 + 3 ^ 40 * 1799502 * 2
def baseEnd_1799502 : Nat := 924009464727123673849247

theorem tailTrace_1799502 : CollatzResearch.WordTrace tailWord_1799502 prefixEnd_1799502 924009464727123673849247 := by
  unfold tailWord_1799502
  simp only [CollatzResearch.WordTrace]
  refine ⟨8204153740839882414860095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43755486617812706212587173 8204153740839882414860095)
  ·
    refine ⟨12306230611259823622290143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8204153740839882414860095 12306230611259823622290143)
    ·
      refine ⟨18459345916889735433435215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12306230611259823622290143 18459345916889735433435215)
      ·
        refine ⟨27689018875334603150152823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18459345916889735433435215 27689018875334603150152823)
        ·
          refine ⟨41533528313001904725229235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27689018875334603150152823 41533528313001904725229235)
          ·
            refine ⟨62300292469502857087843853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41533528313001904725229235 62300292469502857087843853)
            ·
              refine ⟨23362609676063571407941445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62300292469502857087843853 23362609676063571407941445)
              ·
                refine ⟨4380489314261919638989021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23362609676063571407941445 4380489314261919638989021)
                ·
                  refine ⟨1642683492848219864620883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4380489314261919638989021 1642683492848219864620883)
                  ·
                    refine ⟨2464025239272329796931325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1642683492848219864620883 2464025239272329796931325)
                    ·
                      refine ⟨924009464727123673849247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2464025239272329796931325 924009464727123673849247)
                      ·
                        rfl

theorem cell23_1799502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_1799502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799502 prefixEnd_1799502 := by exact prefixLift 1799502
  have htrace : WordTrace (prefixWord ++ tailWord_1799502) baseStart_1799502 baseEnd_1799502 := by
    simpa [prefixWord, tailWord_1799502, baseEnd_1799502] using wordTrace_append hprefix tailTrace_1799502
  have hstable : (prefixWord ++ tailWord_1799502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799502).length < 2 ^ (prefixWord ++ tailWord_1799502).sum := by decide
  have hdescent : baseEnd_1799502 < baseStart_1799502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799512 : List Nat := [2, 1, 2, 2, 1, 1, 4, 3, 2, 3, 2]
def baseStart_1799512 : Nat := 118140960795 + 1799512 * 2 ^ 59
def prefixEnd_1799512 : Nat := 4983230072969 + 3 ^ 40 * 1799512 * 2
def baseEnd_1799512 : Nat := 924014599533668634724201

theorem tailTrace_1799512 : CollatzResearch.WordTrace tailWord_1799512 prefixEnd_1799512 924014599533668634724201 := by
  unfold tailWord_1799512
  simp only [CollatzResearch.WordTrace]
  refine ⟨32816797328341415513372395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43755729771121887351163193 32816797328341415513372395)
  ·
    refine ⟨49225195992512123270058593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32816797328341415513372395 49225195992512123270058593)
    ·
      refine ⟨36918896994384092452543945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49225195992512123270058593 36918896994384092452543945)
      ·
        refine ⟨27689172745788069339407959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36918896994384092452543945 27689172745788069339407959)
        ·
          refine ⟨41533759118682104009111939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27689172745788069339407959 41533759118682104009111939)
          ·
            refine ⟨62300638678023156013667909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41533759118682104009111939 62300638678023156013667909)
            ·
              refine ⟨11681369752129341752562733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62300638678023156013667909 11681369752129341752562733)
              ·
                refine ⟨4380513657048503157211025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11681369752129341752562733 4380513657048503157211025)
                ·
                  refine ⟨3285385242786377367908269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4380513657048503157211025 3285385242786377367908269)
                  ·
                    refine ⟨1232019466044891512965601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3285385242786377367908269 1232019466044891512965601)
                    ·
                      refine ⟨924014599533668634724201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1232019466044891512965601 924014599533668634724201)
                      ·
                        rfl

theorem cell23_1799512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_1799512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799512 prefixEnd_1799512 := by exact prefixLift 1799512
  have htrace : WordTrace (prefixWord ++ tailWord_1799512) baseStart_1799512 baseEnd_1799512 := by
    simpa [prefixWord, tailWord_1799512, baseEnd_1799512] using wordTrace_append hprefix tailTrace_1799512
  have hstable : (prefixWord ++ tailWord_1799512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799512).length < 2 ^ (prefixWord ++ tailWord_1799512).sum := by decide
  have hdescent : baseEnd_1799512 < baseStart_1799512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799522 : List Nat := [3, 3, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_1799522 : Nat := 118140960795 + 1799522 * 2 ^ 59
def prefixEnd_1799522 : Nat := 4983230072969 + 3 ^ 40 * 1799522 * 2
def baseEnd_1799522 : Nat := 308006578113404531866385

theorem tailTrace_1799522 : CollatzResearch.WordTrace tailWord_1799522 prefixEnd_1799522 308006578113404531866385 := by
  unfold tailWord_1799522
  simp only [CollatzResearch.WordTrace]
  refine ⟨16408489846661650683652205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43755972924431068489739213 16408489846661650683652205)
  ·
    refine ⟨6153183692498119006369577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16408489846661650683652205 6153183692498119006369577)
    ·
      refine ⟨4614887769373589254777183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6153183692498119006369577 4614887769373589254777183)
      ·
        refine ⟨6922331654060383882165775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4614887769373589254777183 6922331654060383882165775)
        ·
          refine ⟨10383497481090575823248663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6922331654060383882165775 10383497481090575823248663)
          ·
            refine ⟨15575246221635863734872995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10383497481090575823248663 15575246221635863734872995)
            ·
              refine ⟨23362869332453795602309493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15575246221635863734872995 23362869332453795602309493)
              ·
                refine ⟨2190268999917543337716515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23362869332453795602309493 2190268999917543337716515)
                ·
                  refine ⟨3285403499876315006574773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2190268999917543337716515 3285403499876315006574773)
                  ·
                    refine ⟨308006578113404531866385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3285403499876315006574773 308006578113404531866385)
                    ·
                      rfl

theorem cell23_1799522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_1799522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799522 prefixEnd_1799522 := by exact prefixLift 1799522
  have htrace : WordTrace (prefixWord ++ tailWord_1799522) baseStart_1799522 baseEnd_1799522 := by
    simpa [prefixWord, tailWord_1799522, baseEnd_1799522] using wordTrace_append hprefix tailTrace_1799522
  have hstable : (prefixWord ++ tailWord_1799522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799522).length < 2 ^ (prefixWord ++ tailWord_1799522).sum := by decide
  have hdescent : baseEnd_1799522 < baseStart_1799522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799535 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 4, 4]
def baseStart_1799535 : Nat := 118140960795 + 1799535 * 2 ^ 59
def prefixEnd_1799535 : Nat := 4983230072969 + 3 ^ 40 * 1799535 * 2
def baseEnd_1799535 : Nat := 308008803196240681578865

theorem tailTrace_1799535 : CollatzResearch.WordTrace tailWord_1799535 prefixEnd_1799535 308008803196240681578865 := by
  unfold tailWord_1799535
  simp only [CollatzResearch.WordTrace]
  refine ⟨65634433535599505954832059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43756289023733003969888039 65634433535599505954832059)
  ·
    refine ⟨98451650303399258932248089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65634433535599505954832059 98451650303399258932248089)
    ·
      refine ⟨73838737727549444199186067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98451650303399258932248089 73838737727549444199186067)
      ·
        refine ⟨110758106591324166298779101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73838737727549444199186067 110758106591324166298779101)
        ·
          refine ⟨41534289971746562362042163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110758106591324166298779101 41534289971746562362042163)
          ·
            refine ⟨62301434957619843543063245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41534289971746562362042163 62301434957619843543063245)
            ·
              refine ⟨23363038109107441328648717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62301434957619843543063245 23363038109107441328648717)
              ·
                refine ⟨8761139290915290498243269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23363038109107441328648717 8761139290915290498243269)
                ·
                  refine ⟨1642713617046616968420613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8761139290915290498243269 1642713617046616968420613)
                  ·
                    refine ⟨308008803196240681578865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1642713617046616968420613 308008803196240681578865)
                    ·
                      rfl

theorem cell23_1799535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 4].length) (baseStart_1799535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799535 prefixEnd_1799535 := by exact prefixLift 1799535
  have htrace : WordTrace (prefixWord ++ tailWord_1799535) baseStart_1799535 baseEnd_1799535 := by
    simpa [prefixWord, tailWord_1799535, baseEnd_1799535] using wordTrace_append hprefix tailTrace_1799535
  have hstable : (prefixWord ++ tailWord_1799535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799535).length < 2 ^ (prefixWord ++ tailWord_1799535).sum := by decide
  have hdescent : baseEnd_1799535 < baseStart_1799535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799536 : List Nat := [2, 1, 1, 1, 4, 2, 5, 2, 1, 1, 3]
def baseStart_1799536 : Nat := 118140960795 + 1799536 * 2 ^ 59
def prefixEnd_1799536 : Nat := 4983230072969 + 3 ^ 40 * 1799536 * 2
def baseEnd_1799536 : Nat := 924026923069376540824091

theorem tailTrace_1799536 : CollatzResearch.WordTrace tailWord_1799536 prefixEnd_1799536 924026923069376540824091 := by
  unfold tailWord_1799536
  simp only [CollatzResearch.WordTrace]
  refine ⟨32817235004297941562809231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43756313339063922083745641 32817235004297941562809231)
  ·
    refine ⟨49225852506446912344213847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32817235004297941562809231 49225852506446912344213847)
    ·
      refine ⟨73838778759670368516320771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49225852506446912344213847 73838778759670368516320771)
      ·
        refine ⟨110758168139505552774481157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73838778759670368516320771 110758168139505552774481157)
        ·
          refine ⟨20767156526157291145215217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110758168139505552774481157 20767156526157291145215217)
          ·
            refine ⟨15575367394617968358911413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20767156526157291145215217 15575367394617968358911413)
            ·
              refine ⟨1460190693245434533647945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15575367394617968358911413 1460190693245434533647945)
              ·
                refine ⟨1095143019934075900235959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1460190693245434533647945 1095143019934075900235959)
                ·
                  refine ⟨1642714529901113850353939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1095143019934075900235959 1642714529901113850353939)
                  ·
                    refine ⟨2464071794851670775530909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1642714529901113850353939 2464071794851670775530909)
                    ·
                      refine ⟨924026923069376540824091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2464071794851670775530909 924026923069376540824091)
                      ·
                        rfl

theorem cell23_1799536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 1, 1, 3].length) (baseStart_1799536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799536 prefixEnd_1799536 := by exact prefixLift 1799536
  have htrace : WordTrace (prefixWord ++ tailWord_1799536) baseStart_1799536 baseEnd_1799536 := by
    simpa [prefixWord, tailWord_1799536, baseEnd_1799536] using wordTrace_append hprefix tailTrace_1799536
  have hstable : (prefixWord ++ tailWord_1799536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799536).length < 2 ^ (prefixWord ++ tailWord_1799536).sum := by decide
  have hdescent : baseEnd_1799536 < baseStart_1799536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799545 : List Nat := [1, 2, 1, 3, 2, 1, 4, 2, 1, 1, 5]
def baseStart_1799545 : Nat := 118140960795 + 1799545 * 2 ^ 59
def prefixEnd_1799545 : Nat := 4983230072969 + 3 ^ 40 * 1799545 * 2
def baseEnd_1799545 : Nat := 924031544395267005611549

theorem tailTrace_1799545 : CollatzResearch.WordTrace tailWord_1799545 prefixEnd_1799545 924031544395267005611549 := by
  unfold tailWord_1799545
  simp only [CollatzResearch.WordTrace]
  refine ⟨65634798265563277662696089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43756532177042185108464059 65634798265563277662696089)
  ·
    refine ⟨49226098699172458247022067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65634798265563277662696089 49226098699172458247022067)
    ·
      refine ⟨73839148048758687370533101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49226098699172458247022067 73839148048758687370533101)
      ·
        refine ⟨27689680518284507763949913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73839148048758687370533101 27689680518284507763949913)
        ·
          refine ⟨20767260388713380822962435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27689680518284507763949913 20767260388713380822962435)
          ·
            refine ⟨31150890583070071234443653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20767260388713380822962435 31150890583070071234443653)
            ·
              refine ⟨5840791984325638356458185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31150890583070071234443653 5840791984325638356458185)
              ·
                refine ⟨4380593988244228767343639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5840791984325638356458185 4380593988244228767343639)
                ·
                  refine ⟨6570890982366343151015459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4380593988244228767343639 6570890982366343151015459)
                  ·
                    refine ⟨9856336473549514726523189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6570890982366343151015459 9856336473549514726523189)
                    ·
                      refine ⟨924031544395267005611549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9856336473549514726523189 924031544395267005611549)
                      ·
                        rfl

theorem cell23_1799545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_1799545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799545 prefixEnd_1799545 := by exact prefixLift 1799545
  have htrace : WordTrace (prefixWord ++ tailWord_1799545) baseStart_1799545 baseEnd_1799545 := by
    simpa [prefixWord, tailWord_1799545, baseEnd_1799545] using wordTrace_append hprefix tailTrace_1799545
  have hstable : (prefixWord ++ tailWord_1799545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799545).length < 2 ^ (prefixWord ++ tailWord_1799545).sum := by decide
  have hdescent : baseEnd_1799545 < baseStart_1799545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799555 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 6]
def baseStart_1799555 : Nat := 118140960795 + 1799555 * 2 ^ 59
def prefixEnd_1799555 : Nat := 4983230072969 + 3 ^ 40 * 1799555 * 2
def baseEnd_1799555 : Nat := 924036679201811966486503

theorem tailTrace_1799555 : CollatzResearch.WordTrace tailWord_1799555 prefixEnd_1799555 924036679201811966486503 := by
  unfold tailWord_1799555
  simp only [CollatzResearch.WordTrace]
  refine ⟨65635162995527049370560119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43756775330351366247040079 65635162995527049370560119)
  ·
    refine ⟨98452744493290574055840179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65635162995527049370560119 98452744493290574055840179)
    ·
      refine ⟨147679116739935861083760269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98452744493290574055840179 147679116739935861083760269)
      ·
        refine ⟨55379668777475947906410101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147679116739935861083760269 55379668777475947906410101)
        ·
          refine ⟨5191843947888370116225947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55379668777475947906410101 5191843947888370116225947)
          ·
            refine ⟨7787765921832555174338921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5191843947888370116225947 7787765921832555174338921)
            ·
              refine ⟨5840824441374416380754191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7787765921832555174338921 5840824441374416380754191)
              ·
                refine ⟨8761236662061624571131287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5840824441374416380754191 8761236662061624571131287)
                ·
                  refine ⟨13141854993092436856696931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8761236662061624571131287 13141854993092436856696931)
                  ·
                    refine ⟨19712782489638655285045397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13141854993092436856696931 19712782489638655285045397)
                    ·
                      refine ⟨924036679201811966486503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19712782489638655285045397 924036679201811966486503)
                      ·
                        rfl

theorem cell23_1799555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_1799555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799555 prefixEnd_1799555 := by exact prefixLift 1799555
  have htrace : WordTrace (prefixWord ++ tailWord_1799555) baseStart_1799555 baseEnd_1799555 := by
    simpa [prefixWord, tailWord_1799555, baseEnd_1799555] using wordTrace_append hprefix tailTrace_1799555
  have hstable : (prefixWord ++ tailWord_1799555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799555).length < 2 ^ (prefixWord ++ tailWord_1799555).sum := by decide
  have hdescent : baseEnd_1799555 < baseStart_1799555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799559 : List Nat := [1, 1, 4, 2, 2, 4, 1, 2, 1, 1, 4]
def baseStart_1799559 : Nat := 118140960795 + 1799559 * 2 ^ 59
def prefixEnd_1799559 : Nat := 4983230072969 + 3 ^ 40 * 1799559 * 2
def baseEnd_1799559 : Nat := 924038733124429950836485

theorem tailTrace_1799559 : CollatzResearch.WordTrace tailWord_1799559 prefixEnd_1799559 924038733124429950836485 := by
  unfold tailWord_1799559
  simp only [CollatzResearch.WordTrace]
  refine ⟨65635308887512558053705731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43756872591675038702470487 65635308887512558053705731)
  ·
    refine ⟨98452963331268837080558597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65635308887512558053705731 98452963331268837080558597)
    ·
      refine ⟨18459930624612906952604737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98452963331268837080558597 18459930624612906952604737)
      ·
        refine ⟨13844947968459680214453553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18459930624612906952604737 13844947968459680214453553)
        ·
          refine ⟨10383710976344760160840165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13844947968459680214453553 10383710976344760160840165)
          ·
            refine ⟨1946945808064642530157531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10383710976344760160840165 1946945808064642530157531)
            ·
              refine ⟨2920418712096963795236297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1946945808064642530157531 2920418712096963795236297)
              ·
                refine ⟨2190314034072722846427223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2920418712096963795236297 2190314034072722846427223)
                ·
                  refine ⟨3285471051109084269640835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2190314034072722846427223 3285471051109084269640835)
                  ·
                    refine ⟨4928206576663626404461253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3285471051109084269640835 4928206576663626404461253)
                    ·
                      refine ⟨924038733124429950836485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4928206576663626404461253 924038733124429950836485)
                      ·
                        rfl

theorem cell23_1799559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_1799559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799559 prefixEnd_1799559 := by exact prefixLift 1799559
  have htrace : WordTrace (prefixWord ++ tailWord_1799559) baseStart_1799559 baseEnd_1799559 := by
    simpa [prefixWord, tailWord_1799559, baseEnd_1799559] using wordTrace_append hprefix tailTrace_1799559
  have hstable : (prefixWord ++ tailWord_1799559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799559).length < 2 ^ (prefixWord ++ tailWord_1799559).sum := by decide
  have hdescent : baseEnd_1799559 < baseStart_1799559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799572 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_1799572 : Nat := 118140960795 + 1799572 * 2 ^ 59
def prefixEnd_1799572 : Nat := 4983230072969 + 3 ^ 40 * 1799572 * 2
def baseEnd_1799572 : Nat := 924045408372938399973925

theorem tailTrace_1799572 : CollatzResearch.WordTrace tailWord_1799572 prefixEnd_1799572 924045408372938399973925 := by
  unfold tailWord_1799572
  simp only [CollatzResearch.WordTrace]
  refine ⟨32817891518232730636964485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43757188690976974182619313 32817891518232730636964485)
  ·
    refine ⟨6153354659668636994430841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32817891518232730636964485 6153354659668636994430841)
    ·
      refine ⟨4615015994751477745823131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6153354659668636994430841 4615015994751477745823131)
      ·
        refine ⟨6922523992127216618734697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4615015994751477745823131 6922523992127216618734697)
        ·
          refine ⟨5191892994095412464051023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6922523992127216618734697 5191892994095412464051023)
          ·
            refine ⟨7787839491143118696076535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5191892994095412464051023 7787839491143118696076535)
            ·
              refine ⟨11681759236714678044114803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7787839491143118696076535 11681759236714678044114803)
              ·
                refine ⟨17522638855072017066172205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11681759236714678044114803 17522638855072017066172205)
                ·
                  refine ⟨6570989570652006399814577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17522638855072017066172205 6570989570652006399814577)
                  ·
                    refine ⟨4928242177989004799860933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6570989570652006399814577 4928242177989004799860933)
                    ·
                      refine ⟨924045408372938399973925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4928242177989004799860933 924045408372938399973925)
                      ·
                        rfl

theorem cell23_1799572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_1799572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799572 prefixEnd_1799572 := by exact prefixLift 1799572
  have htrace : WordTrace (prefixWord ++ tailWord_1799572) baseStart_1799572 baseEnd_1799572 := by
    simpa [prefixWord, tailWord_1799572, baseEnd_1799572] using wordTrace_append hprefix tailTrace_1799572
  have hstable : (prefixWord ++ tailWord_1799572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799572).length < 2 ^ (prefixWord ++ tailWord_1799572).sum := by decide
  have hdescent : baseEnd_1799572 < baseStart_1799572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799576 : List Nat := [2, 1, 2, 5, 2, 1, 3, 1, 1, 1, 4]
def baseStart_1799576 : Nat := 118140960795 + 1799576 * 2 ^ 59
def prefixEnd_1799576 : Nat := 4983230072969 + 3 ^ 40 * 1799576 * 2
def baseEnd_1799576 : Nat := 924047462295556384323907

theorem tailTrace_1799576 : CollatzResearch.WordTrace tailWord_1799576 prefixEnd_1799576 924047462295556384323907 := by
  unfold tailWord_1799576
  simp only [CollatzResearch.WordTrace]
  refine ⟨32817964464225484978537291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43757285952300646638049721 32817964464225484978537291)
  ·
    refine ⟨49226946696338227467805937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32817964464225484978537291 49226946696338227467805937)
    ·
      refine ⟨36920210022253670600854453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49226946696338227467805937 36920210022253670600854453)
      ·
        refine ⟨3461269689586281618830105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36920210022253670600854453 3461269689586281618830105)
        ·
          refine ⟨2595952267189711214122579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3461269689586281618830105 2595952267189711214122579)
          ·
            refine ⟨3893928400784566821183869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2595952267189711214122579 3893928400784566821183869)
            ·
              refine ⟨1460223150294212557943951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3893928400784566821183869 1460223150294212557943951)
              ·
                refine ⟨2190334725441318836915927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1460223150294212557943951 2190334725441318836915927)
                ·
                  refine ⟨3285502088161978255373891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2190334725441318836915927 3285502088161978255373891)
                  ·
                    refine ⟨4928253132242967383060837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3285502088161978255373891 4928253132242967383060837)
                    ·
                      refine ⟨924047462295556384323907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4928253132242967383060837 924047462295556384323907)
                      ·
                        rfl

theorem cell23_1799576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_1799576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799576 prefixEnd_1799576 := by exact prefixLift 1799576
  have htrace : WordTrace (prefixWord ++ tailWord_1799576) baseStart_1799576 baseEnd_1799576 := by
    simpa [prefixWord, tailWord_1799576, baseEnd_1799576] using wordTrace_append hprefix tailTrace_1799576
  have hstable : (prefixWord ++ tailWord_1799576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799576).length < 2 ^ (prefixWord ++ tailWord_1799576).sum := by decide
  have hdescent : baseEnd_1799576 < baseStart_1799576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799582 : List Nat := [4, 3, 1, 2, 2, 11]
def baseStart_1799582 : Nat := 118140960795 + 1799582 * 2 ^ 59
def prefixEnd_1799582 : Nat := 4983230072969 + 3 ^ 40 * 1799582 * 2
def baseEnd_1799582 : Nat := 3802677132425857452053

theorem tailTrace_1799582 : CollatzResearch.WordTrace tailWord_1799582 prefixEnd_1799582 3802677132425857452053 := by
  unfold tailWord_1799582
  simp only [CollatzResearch.WordTrace]
  refine ⟨8204518470803654122724125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43757431844286155321195333 8204518470803654122724125)
  ·
    refine ⟨3076694426551370296021547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8204518470803654122724125 3076694426551370296021547)
    ·
      refine ⟨4615041639827055444032321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3076694426551370296021547 4615041639827055444032321)
      ·
        refine ⟨3461281229870291583024241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4615041639827055444032321 3461281229870291583024241)
        ·
          refine ⟨2595960922402718687268181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3461281229870291583024241 2595960922402718687268181)
          ·
            refine ⟨3802677132425857452053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2595960922402718687268181 3802677132425857452053)
            ·
              rfl

theorem cell23_1799582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 11].length) (baseStart_1799582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799582 prefixEnd_1799582 := by exact prefixLift 1799582
  have htrace : WordTrace (prefixWord ++ tailWord_1799582) baseStart_1799582 baseEnd_1799582 := by
    simpa [prefixWord, tailWord_1799582, baseEnd_1799582] using wordTrace_append hprefix tailTrace_1799582
  have hstable : (prefixWord ++ tailWord_1799582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799582).length < 2 ^ (prefixWord ++ tailWord_1799582).sum := by decide
  have hdescent : baseEnd_1799582 < baseStart_1799582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799609 : List Nat := [1, 2, 1, 4, 4, 1, 2, 1, 1, 3, 3]
def baseStart_1799609 : Nat := 118140960795 + 1799609 * 2 ^ 59
def prefixEnd_1799609 : Nat := 4983230072969 + 3 ^ 40 * 1799609 * 2
def baseEnd_1799609 : Nat := 924064407157154755211255

theorem tailTrace_1799609 : CollatzResearch.WordTrace tailWord_1799609 prefixEnd_1799609 924064407157154755211255 := by
  unfold tailWord_1799609
  simp only [CollatzResearch.WordTrace]
  refine ⟨65637132537331416593025881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43758088358220944395350587 65637132537331416593025881)
  ·
    refine ⟨49227849402998562444769411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65637132537331416593025881 49227849402998562444769411)
    ·
      refine ⟨73841774104497843667154117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49227849402998562444769411 73841774104497843667154117)
      ·
        refine ⟨13845332644593345687591397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73841774104497843667154117 13845332644593345687591397)
        ·
          refine ⟨2595999870861252316423387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13845332644593345687591397 2595999870861252316423387)
          ·
            refine ⟨3893999806291878474635081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2595999870861252316423387 3893999806291878474635081)
            ·
              refine ⟨2920499854718908855976311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3893999806291878474635081 2920499854718908855976311)
              ·
                refine ⟨4380749782078363283964467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2920499854718908855976311 4380749782078363283964467)
                ·
                  refine ⟨6571124673117544925946701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4380749782078363283964467 6571124673117544925946701)
                  ·
                    refine ⟨2464171752419079347230013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6571124673117544925946701 2464171752419079347230013)
                    ·
                      refine ⟨924064407157154755211255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2464171752419079347230013 924064407157154755211255)
                      ·
                        rfl

theorem cell23_1799609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_1799609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799609 prefixEnd_1799609 := by exact prefixLift 1799609
  have htrace : WordTrace (prefixWord ++ tailWord_1799609) baseStart_1799609 baseEnd_1799609 := by
    simpa [prefixWord, tailWord_1799609, baseEnd_1799609] using wordTrace_append hprefix tailTrace_1799609
  have hstable : (prefixWord ++ tailWord_1799609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799609).length < 2 ^ (prefixWord ++ tailWord_1799609).sum := by decide
  have hdescent : baseEnd_1799609 < baseStart_1799609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799662 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_1799662 : Nat := 118140960795 + 1799662 * 2 ^ 59
def prefixEnd_1799662 : Nat := 4983230072969 + 3 ^ 40 * 1799662 * 2
def baseEnd_1799662 : Nat := 924091621631843047848511

theorem tailTrace_1799662 : CollatzResearch.WordTrace tailWord_1799662 prefixEnd_1799662 924091621631843047848511 := by
  unfold tailWord_1799662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8204883200767425830588155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43759377070759604429803493 8204883200767425830588155)
  ·
    refine ⟨12307324801151138745882233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8204883200767425830588155 12307324801151138745882233)
    ·
      refine ⟨9230493600863354059411675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12307324801151138745882233 9230493600863354059411675)
      ·
        refine ⟨13845740401295031089117513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9230493600863354059411675 13845740401295031089117513)
        ·
          refine ⟨10384305300971273316838135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13845740401295031089117513 10384305300971273316838135)
          ·
            refine ⟨15576457951456909975257203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10384305300971273316838135 15576457951456909975257203)
            ·
              refine ⟨23364686927185364962885805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15576457951456909975257203 23364686927185364962885805)
              ·
                refine ⟨8761757597694511861082177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23364686927185364962885805 8761757597694511861082177)
                ·
                  refine ⟨6571318198270883895811633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8761757597694511861082177 6571318198270883895811633)
                  ·
                    refine ⟨4928488648703162921858725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6571318198270883895811633 4928488648703162921858725)
                    ·
                      refine ⟨924091621631843047848511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4928488648703162921858725 924091621631843047848511)
                      ·
                        rfl

theorem cell23_1799662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_1799662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799662 prefixEnd_1799662 := by exact prefixLift 1799662
  have htrace : WordTrace (prefixWord ++ tailWord_1799662) baseStart_1799662 baseEnd_1799662 := by
    simpa [prefixWord, tailWord_1799662, baseEnd_1799662] using wordTrace_append hprefix tailTrace_1799662
  have hstable : (prefixWord ++ tailWord_1799662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799662).length < 2 ^ (prefixWord ++ tailWord_1799662).sum := by decide
  have hdescent : baseEnd_1799662 < baseStart_1799662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799666 : List Nat := [3, 2, 1, 4, 1, 1, 3, 1, 1, 4, 2]
def baseStart_1799666 : Nat := 118140960795 + 1799666 * 2 ^ 59
def prefixEnd_1799666 : Nat := 4983230072969 + 3 ^ 40 * 1799666 * 2
def baseEnd_1799666 : Nat := 924093675554461032198493

theorem tailTrace_1799666 : CollatzResearch.WordTrace tailWord_1799666 prefixEnd_1799666 924093675554461032198493 := by
  unfold tailWord_1799666
  simp only [CollatzResearch.WordTrace]
  refine ⟨16409802874531228831962713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43759474332083276885233901 16409802874531228831962713)
  ·
    refine ⟨12307352155898421623972035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16409802874531228831962713 12307352155898421623972035)
    ·
      refine ⟨18461028233847632435958053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12307352155898421623972035 18461028233847632435958053)
      ·
        refine ⟨3461442793846431081742135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18461028233847632435958053 3461442793846431081742135)
        ·
          refine ⟨5192164190769646622613203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3461442793846431081742135 5192164190769646622613203)
          ·
            refine ⟨7788246286154469933919805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5192164190769646622613203 7788246286154469933919805)
            ·
              refine ⟨2920592357307926225219927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7788246286154469933919805 2920592357307926225219927)
              ·
                refine ⟨4380888535961889337829891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2920592357307926225219927 4380888535961889337829891)
                ·
                  refine ⟨6571332803942834006744837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4380888535961889337829891 6571332803942834006744837)
                  ·
                    refine ⟨1232124900739281376264657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6571332803942834006744837 1232124900739281376264657)
                    ·
                      refine ⟨924093675554461032198493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1232124900739281376264657 924093675554461032198493)
                      ·
                        rfl

theorem cell23_1799666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_1799666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799666 prefixEnd_1799666 := by exact prefixLift 1799666
  have htrace : WordTrace (prefixWord ++ tailWord_1799666) baseStart_1799666 baseEnd_1799666 := by
    simpa [prefixWord, tailWord_1799666, baseEnd_1799666] using wordTrace_append hprefix tailTrace_1799666
  have hstable : (prefixWord ++ tailWord_1799666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799666).length < 2 ^ (prefixWord ++ tailWord_1799666).sum := by decide
  have hdescent : baseEnd_1799666 < baseStart_1799666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799709 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 2, 5, 2]
def baseStart_1799709 : Nat := 118140960795 + 1799709 * 2 ^ 59
def prefixEnd_1799709 : Nat := 4983230072969 + 3 ^ 40 * 1799709 * 2
def baseEnd_1799709 : Nat := 924115755222604363960795

theorem tailTrace_1799709 : CollatzResearch.WordTrace tailWord_1799709 prefixEnd_1799709 924115755222604363960795 := by
  unfold tailWord_1799709
  simp only [CollatzResearch.WordTrace]
  refine ⟨65640779836969133671666181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43760519891312755781110787 65640779836969133671666181)
  ·
    refine ⟨12307646219431712563437409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65640779836969133671666181 12307646219431712563437409)
    ·
      refine ⟨9230734664573784422578057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12307646219431712563437409 9230734664573784422578057)
      ·
        refine ⟨6923050998430338316933543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9230734664573784422578057 6923050998430338316933543)
        ·
          refine ⟨10384576497645507475400315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6923050998430338316933543 10384576497645507475400315)
          ·
            refine ⟨15576864746468261213100473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10384576497645507475400315 15576864746468261213100473)
            ·
              refine ⟨11682648559851195909825355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15576864746468261213100473 11682648559851195909825355)
              ·
                refine ⟨17523972839776793864738033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11682648559851195909825355 17523972839776793864738033)
                ·
                  refine ⟨13142979629832595398553525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17523972839776793864738033 13142979629832595398553525)
                  ·
                    refine ⟨1232154340296805818614393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13142979629832595398553525 1232154340296805818614393)
                    ·
                      refine ⟨924115755222604363960795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1232154340296805818614393 924115755222604363960795)
                      ·
                        rfl

theorem cell23_1799709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_1799709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799709 prefixEnd_1799709 := by exact prefixLift 1799709
  have htrace : WordTrace (prefixWord ++ tailWord_1799709) baseStart_1799709 baseEnd_1799709 := by
    simpa [prefixWord, tailWord_1799709, baseEnd_1799709] using wordTrace_append hprefix tailTrace_1799709
  have hstable : (prefixWord ++ tailWord_1799709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799709).length < 2 ^ (prefixWord ++ tailWord_1799709).sum := by decide
  have hdescent : baseEnd_1799709 < baseStart_1799709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799712 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1799712 : Nat := 118140960795 + 1799712 * 2 ^ 59
def prefixEnd_1799712 : Nat := 4983230072969 + 3 ^ 40 * 1799712 * 2
def baseEnd_1799712 : Nat := 924117295664567852223281

theorem tailTrace_1799712 : CollatzResearch.WordTrace tailWord_1799712 prefixEnd_1799712 924117295664567852223281 := by
  unfold tailWord_1799712
  simp only [CollatzResearch.WordTrace]
  refine ⟨32820444627979132592012695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43760592837305510122683593 32820444627979132592012695)
  ·
    refine ⟨49230666941968698888019043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32820444627979132592012695 49230666941968698888019043)
    ·
      refine ⟨73846000412953048332028565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49230666941968698888019043 73846000412953048332028565)
      ·
        refine ⟨3461531269357174140563839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 73846000412953048332028565 3461531269357174140563839)
        ·
          refine ⟨5192296904035761210845759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3461531269357174140563839 5192296904035761210845759)
          ·
            refine ⟨7788445356053641816268639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5192296904035761210845759 7788445356053641816268639)
            ·
              refine ⟨11682668034080462724402959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7788445356053641816268639 11682668034080462724402959)
              ·
                refine ⟨17524002051120694086604439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11682668034080462724402959 17524002051120694086604439)
                ·
                  refine ⟨26286003076681041129906659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17524002051120694086604439 26286003076681041129906659)
                  ·
                    refine ⟨39429004615021561694859989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26286003076681041129906659 39429004615021561694859989)
                    ·
                      refine ⟨924117295664567852223281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39429004615021561694859989 924117295664567852223281)
                      ·
                        rfl

theorem cell23_1799712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1799712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799712 prefixEnd_1799712 := by exact prefixLift 1799712
  have htrace : WordTrace (prefixWord ++ tailWord_1799712) baseStart_1799712 baseEnd_1799712 := by
    simpa [prefixWord, tailWord_1799712, baseEnd_1799712] using wordTrace_append hprefix tailTrace_1799712
  have hstable : (prefixWord ++ tailWord_1799712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799712).length < 2 ^ (prefixWord ++ tailWord_1799712).sum := by decide
  have hdescent : baseEnd_1799712 < baseStart_1799712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799866 : List Nat := [3, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3]
def baseStart_1799866 : Nat := 118140960795 + 1799866 * 2 ^ 59
def prefixEnd_1799866 : Nat := 4983230072969 + 3 ^ 40 * 1799866 * 2
def baseEnd_1799866 : Nat := 924196371685360249697573

theorem tailTrace_1799866 : CollatzResearch.WordTrace tailWord_1799866 prefixEnd_1799866 924196371685360249697573 := by
  unfold tailWord_1799866
  simp only [CollatzResearch.WordTrace]
  refine ⟨16411626524350087371282863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43764337398266899656754301 16411626524350087371282863)
  ·
    refine ⟨24617439786525131056924295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16411626524350087371282863 24617439786525131056924295)
    ·
      refine ⟨36926159679787696585386443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24617439786525131056924295 36926159679787696585386443)
      ·
        refine ⟨55389239519681544878079665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36926159679787696585386443 55389239519681544878079665)
        ·
          refine ⟨41541929639761158658559749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55389239519681544878079665 41541929639761158658559749)
          ·
            refine ⟨7789111807455217248479953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41541929639761158658559749 7789111807455217248479953)
            ·
              refine ⟨5841833855591412936359965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7789111807455217248479953 5841833855591412936359965)
              ·
                refine ⟨2190687695846779851134987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5841833855591412936359965 2190687695846779851134987)
                ·
                  refine ⟨3286031543770169776702481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2190687695846779851134987 3286031543770169776702481)
                  ·
                    refine ⟨2464523657827627332526861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3286031543770169776702481 2464523657827627332526861)
                    ·
                      refine ⟨924196371685360249697573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2464523657827627332526861 924196371685360249697573)
                      ·
                        rfl

theorem cell23_1799866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3].length) (baseStart_1799866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799866 prefixEnd_1799866 := by exact prefixLift 1799866
  have htrace : WordTrace (prefixWord ++ tailWord_1799866) baseStart_1799866 baseEnd_1799866 := by
    simpa [prefixWord, tailWord_1799866, baseEnd_1799866] using wordTrace_append hprefix tailTrace_1799866
  have hstable : (prefixWord ++ tailWord_1799866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799866).length < 2 ^ (prefixWord ++ tailWord_1799866).sum := by decide
  have hdescent : baseEnd_1799866 < baseStart_1799866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799874 : List Nat := [3, 5, 1, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_1799874 : Nat := 118140960795 + 1799874 * 2 ^ 59
def prefixEnd_1799874 : Nat := 4983230072969 + 3 ^ 40 * 1799874 * 2
def baseEnd_1799874 : Nat := 924200479530596218397537

theorem tailTrace_1799874 : CollatzResearch.WordTrace tailWord_1799874 prefixEnd_1799874 924200479530596218397537 := by
  unfold tailWord_1799874
  simp only [CollatzResearch.WordTrace]
  refine ⟨16411699470342841712855669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43764531920914244567615117 16411699470342841712855669)
  ·
    refine ⟨1538596825344641410580219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16411699470342841712855669 1538596825344641410580219)
    ·
      refine ⟨2307895238016962115870329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1538596825344641410580219 2307895238016962115870329)
      ·
        refine ⟨1730921428512721586902747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2307895238016962115870329 1730921428512721586902747)
        ·
          refine ⟨2596382142769082380354121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1730921428512721586902747 2596382142769082380354121)
          ·
            refine ⟨1947286607076811785265591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2596382142769082380354121 1947286607076811785265591)
            ·
              refine ⟨2920929910615217677898387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1947286607076811785265591 2920929910615217677898387)
              ·
                refine ⟨4381394865922826516847581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2920929910615217677898387 4381394865922826516847581)
                ·
                  refine ⟨1643023074721059943817843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4381394865922826516847581 1643023074721059943817843)
                  ·
                    refine ⟨2464534612081589915726765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1643023074721059943817843 2464534612081589915726765)
                    ·
                      refine ⟨924200479530596218397537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2464534612081589915726765 924200479530596218397537)
                      ·
                        rfl

theorem cell23_1799874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_1799874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799874 prefixEnd_1799874 := by exact prefixLift 1799874
  have htrace : WordTrace (prefixWord ++ tailWord_1799874) baseStart_1799874 baseEnd_1799874 := by
    simpa [prefixWord, tailWord_1799874, baseEnd_1799874] using wordTrace_append hprefix tailTrace_1799874
  have hstable : (prefixWord ++ tailWord_1799874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799874).length < 2 ^ (prefixWord ++ tailWord_1799874).sum := by decide
  have hdescent : baseEnd_1799874 < baseStart_1799874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799890 : List Nat := [3, 2, 2, 2, 2, 3, 2, 1, 2, 4]
def baseStart_1799890 : Nat := 118140960795 + 1799890 * 2 ^ 59
def prefixEnd_1799890 : Nat := 4983230072969 + 3 ^ 40 * 1799890 * 2
def baseEnd_1799890 : Nat := 308069565073689385265821

theorem tailTrace_1799890 : CollatzResearch.WordTrace tailWord_1799890 prefixEnd_1799890 308069565073689385265821 := by
  unfold tailWord_1799890
  simp only [CollatzResearch.WordTrace]
  refine ⟨16411845362328350396001281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43764920966208934389336749 16411845362328350396001281)
  ·
    refine ⟨12308884021746262797000961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16411845362328350396001281 12308884021746262797000961)
    ·
      refine ⟨9231663016309697097750721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12308884021746262797000961 9231663016309697097750721)
      ·
        refine ⟨6923747262232272823313041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9231663016309697097750721 6923747262232272823313041)
        ·
          refine ⟨5192810446674204617484781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6923747262232272823313041 5192810446674204617484781)
          ·
            refine ⟨1947303917502826731556793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5192810446674204617484781 1947303917502826731556793)
            ·
              refine ⟨1460477938127120048667595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1947303917502826731556793 1460477938127120048667595)
              ·
                refine ⟨2190716907190680073001393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1460477938127120048667595 2190716907190680073001393)
                ·
                  refine ⟨1643037680393010054751045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2190716907190680073001393 1643037680393010054751045)
                  ·
                    refine ⟨308069565073689385265821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1643037680393010054751045 308069565073689385265821)
                    ·
                      rfl

theorem cell23_1799890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_1799890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799890 prefixEnd_1799890 := by exact prefixLift 1799890
  have htrace : WordTrace (prefixWord ++ tailWord_1799890) baseStart_1799890 baseEnd_1799890 := by
    simpa [prefixWord, tailWord_1799890, baseEnd_1799890] using wordTrace_append hprefix tailTrace_1799890
  have hstable : (prefixWord ++ tailWord_1799890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799890).length < 2 ^ (prefixWord ++ tailWord_1799890).sum := by decide
  have hdescent : baseEnd_1799890 < baseStart_1799890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799939 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 3]
def baseStart_1799939 : Nat := 118140960795 + 1799939 * 2 ^ 59
def prefixEnd_1799939 : Nat := 4983230072969 + 3 ^ 40 * 1799939 * 2
def baseEnd_1799939 : Nat := 924233855773138464084737

theorem tailTrace_1799939 : CollatzResearch.WordTrace tailWord_1799939 prefixEnd_1799939 924233855773138464084737 := by
  unfold tailWord_1799939
  simp only [CollatzResearch.WordTrace]
  refine ⟨65649168626135882952538871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43766112417423921968359247 65649168626135882952538871)
  ·
    refine ⟨98473752939203824428808307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65649168626135882952538871 98473752939203824428808307)
    ·
      refine ⟨147710629408805736643212461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98473752939203824428808307 147710629408805736643212461)
      ·
        refine ⟨55391486028302151241204673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147710629408805736643212461 55391486028302151241204673)
        ·
          refine ⟨41543614521226613430903505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55391486028302151241204673 41543614521226613430903505)
          ·
            refine ⟨31157710890919960073177629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41543614521226613430903505 31157710890919960073177629)
            ·
              refine ⟨11684141584094985027441611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31157710890919960073177629 11684141584094985027441611)
              ·
                refine ⟨17526212376142477541162417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11684141584094985027441611 17526212376142477541162417)
                ·
                  refine ⟨13144659282106858155871813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17526212376142477541162417 13144659282106858155871813)
                  ·
                    refine ⟨2464623615395035904225965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13144659282106858155871813 2464623615395035904225965)
                    ·
                      refine ⟨924233855773138464084737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2464623615395035904225965 924233855773138464084737)
                      ·
                        rfl

theorem cell23_1799939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_1799939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799939 prefixEnd_1799939 := by exact prefixLift 1799939
  have htrace : WordTrace (prefixWord ++ tailWord_1799939) baseStart_1799939 baseEnd_1799939 := by
    simpa [prefixWord, tailWord_1799939, baseEnd_1799939] using wordTrace_append hprefix tailTrace_1799939
  have hstable : (prefixWord ++ tailWord_1799939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799939).length < 2 ^ (prefixWord ++ tailWord_1799939).sum := by decide
  have hdescent : baseEnd_1799939 < baseStart_1799939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799959 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 9]
def baseStart_1799959 : Nat := 118140960795 + 1799959 * 2 ^ 59
def prefixEnd_1799959 : Nat := 4983230072969 + 3 ^ 40 * 1799959 * 2
def baseEnd_1799959 : Nat := 102693791709580931759405

theorem tailTrace_1799959 : CollatzResearch.WordTrace tailWord_1799959 prefixEnd_1799959 102693791709580931759405 := by
  unfold tailWord_1799959
  simp only [CollatzResearch.WordTrace]
  refine ⟨65649898086063426368266931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43766598724042284245511287 65649898086063426368266931)
  ·
    refine ⟨98474847129095139552400397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65649898086063426368266931 98474847129095139552400397)
    ·
      refine ⟨36928067673410677332150149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98474847129095139552400397 36928067673410677332150149)
      ·
        refine ⟨6924012688764501999778153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36928067673410677332150149 6924012688764501999778153)
        ·
          refine ⟨5193009516573376499833615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6924012688764501999778153 5193009516573376499833615)
          ·
            refine ⟨7789514274860064749750423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5193009516573376499833615 7789514274860064749750423)
            ·
              refine ⟨11684271412290097124625635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7789514274860064749750423 11684271412290097124625635)
              ·
                refine ⟨17526407118435145686938453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11684271412290097124625635 17526407118435145686938453)
                ·
                  refine ⟨102693791709580931759405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17526407118435145686938453 102693791709580931759405)
                  ·
                    rfl

theorem cell23_1799959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 9].length) (baseStart_1799959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799959 prefixEnd_1799959 := by exact prefixLift 1799959
  have htrace : WordTrace (prefixWord ++ tailWord_1799959) baseStart_1799959 baseEnd_1799959 := by
    simpa [prefixWord, tailWord_1799959, baseEnd_1799959] using wordTrace_append hprefix tailTrace_1799959
  have hstable : (prefixWord ++ tailWord_1799959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799959).length < 2 ^ (prefixWord ++ tailWord_1799959).sum := by decide
  have hdescent : baseEnd_1799959 < baseStart_1799959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799986 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3]
def baseStart_1799986 : Nat := 118140960795 + 1799986 * 2 ^ 59
def prefixEnd_1799986 : Nat := 4983230072969 + 3 ^ 40 * 1799986 * 2
def baseEnd_1799986 : Nat := 924257989363899780197021

theorem tailTrace_1799986 : CollatzResearch.WordTrace tailWord_1799986 prefixEnd_1799986 924257989363899780197021 := by
  unfold tailWord_1799986
  simp only [CollatzResearch.WordTrace]
  refine ⟨16412720714241402494874953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43767255237977073319666541 16412720714241402494874953)
  ·
    refine ⟨12309540535681051871156215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16412720714241402494874953 12309540535681051871156215)
    ·
      refine ⟨18464310803521577806734323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12309540535681051871156215 18464310803521577806734323)
      ·
        refine ⟨27696466205282366710101485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18464310803521577806734323 27696466205282366710101485)
        ·
          refine ⟨10386174826980887516288057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27696466205282366710101485 10386174826980887516288057)
          ·
            refine ⟨7789631120235665637216043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10386174826980887516288057 7789631120235665637216043)
            ·
              refine ⟨11684446680353498455824065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7789631120235665637216043 11684446680353498455824065)
              ·
                refine ⟨8763335010265123841868049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11684446680353498455824065 8763335010265123841868049)
                ·
                  refine ⟨6572501257698842881401037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8763335010265123841868049 6572501257698842881401037)
                  ·
                    refine ⟨2464687971637066080525389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6572501257698842881401037 2464687971637066080525389)
                    ·
                      refine ⟨924257989363899780197021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2464687971637066080525389 924257989363899780197021)
                      ·
                        rfl

theorem cell23_1799986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_1799986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799986 prefixEnd_1799986 := by exact prefixLift 1799986
  have htrace : WordTrace (prefixWord ++ tailWord_1799986) baseStart_1799986 baseEnd_1799986 := by
    simpa [prefixWord, tailWord_1799986, baseEnd_1799986] using wordTrace_append hprefix tailTrace_1799986
  have hstable : (prefixWord ++ tailWord_1799986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799986).length < 2 ^ (prefixWord ++ tailWord_1799986).sum := by decide
  have hdescent : baseEnd_1799986 < baseStart_1799986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799987 : List Nat := [1, 1, 1, 2, 7, 2, 1, 2, 2, 2, 2]
def baseStart_1799987 : Nat := 118140960795 + 1799987 * 2 ^ 59
def prefixEnd_1799987 : Nat := 4983230072969 + 3 ^ 40 * 1799987 * 2
def baseEnd_1799987 : Nat := 924258502844554276284517

theorem tailTrace_1799987 : CollatzResearch.WordTrace tailWord_1799987 prefixEnd_1799987 924258502844554276284517 := by
  unfold tailWord_1799987
  simp only [CollatzResearch.WordTrace]
  refine ⟨65650919329961987150286215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43767279553307991433524143 65650919329961987150286215)
  ·
    refine ⟨98476378994942980725429323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65650919329961987150286215 98476378994942980725429323)
    ·
      refine ⟨147714568492414471088143985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98476378994942980725429323 147714568492414471088143985)
      ·
        refine ⟨110785926369310853316107989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147714568492414471088143985 110785926369310853316107989)
        ·
          refine ⟨2596545149280723124596281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 110785926369310853316107989 2596545149280723124596281)
          ·
            refine ⟨1947408861960542343447211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2596545149280723124596281 1947408861960542343447211)
            ·
              refine ⟨2921113292940813515170817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1947408861960542343447211 2921113292940813515170817)
              ·
                refine ⟨2190834969705610136378113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2921113292940813515170817 2190834969705610136378113)
                ·
                  refine ⟨1643126227279207602283585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2190834969705610136378113 1643126227279207602283585)
                  ·
                    refine ⟨1232344670459405701712689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1643126227279207602283585 1232344670459405701712689)
                    ·
                      refine ⟨924258502844554276284517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1232344670459405701712689 924258502844554276284517)
                      ·
                        rfl

theorem cell23_1799987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 2, 2].length) (baseStart_1799987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799987 prefixEnd_1799987 := by exact prefixLift 1799987
  have htrace : WordTrace (prefixWord ++ tailWord_1799987) baseStart_1799987 baseEnd_1799987 := by
    simpa [prefixWord, tailWord_1799987, baseEnd_1799987] using wordTrace_append hprefix tailTrace_1799987
  have hstable : (prefixWord ++ tailWord_1799987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799987).length < 2 ^ (prefixWord ++ tailWord_1799987).sum := by decide
  have hdescent : baseEnd_1799987 < baseStart_1799987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799993 : List Nat := [1, 2, 1, 7, 1, 1, 2, 1, 7]
def baseStart_1799993 : Nat := 118140960795 + 1799993 * 2 ^ 59
def prefixEnd_1799993 : Nat := 4983230072969 + 3 ^ 40 * 1799993 * 2
def baseEnd_1799993 : Nat := 102695731525386805867721

theorem tailTrace_1799993 : CollatzResearch.WordTrace tailWord_1799993 prefixEnd_1799993 102695731525386805867721 := by
  unfold tailWord_1799993
  simp only [CollatzResearch.WordTrace]
  refine ⟨65651138167940250175004633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43767425445293500116669755 65651138167940250175004633)
  ·
    refine ⟨49238353625955187631253475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65651138167940250175004633 49238353625955187631253475)
    ·
      refine ⟨73857530438932781446880213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49238353625955187631253475 73857530438932781446880213)
      ·
        refine ⟨1731035869662487065161255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 73857530438932781446880213 1731035869662487065161255)
        ·
          refine ⟨2596553804493730597741883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1731035869662487065161255 2596553804493730597741883)
          ·
            refine ⟨3894830706740595896612825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2596553804493730597741883 3894830706740595896612825)
            ·
              refine ⟨2921123030055446922459619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3894830706740595896612825 2921123030055446922459619)
              ·
                refine ⟨4381684545083170383689429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2921123030055446922459619 4381684545083170383689429)
                ·
                  refine ⟨102695731525386805867721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4381684545083170383689429 102695731525386805867721)
                  ·
                    rfl

theorem cell23_1799993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 7].length) (baseStart_1799993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799993 prefixEnd_1799993 := by exact prefixLift 1799993
  have htrace : WordTrace (prefixWord ++ tailWord_1799993) baseStart_1799993 baseEnd_1799993 := by
    simpa [prefixWord, tailWord_1799993, baseEnd_1799993] using wordTrace_append hprefix tailTrace_1799993
  have hstable : (prefixWord ++ tailWord_1799993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799993).length < 2 ^ (prefixWord ++ tailWord_1799993).sum := by decide
  have hdescent : baseEnd_1799993 < baseStart_1799993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799996 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 1, 7, 2]
def baseStart_1799996 : Nat := 118140960795 + 1799996 * 2 ^ 59
def prefixEnd_1799996 : Nat := 4983230072969 + 3 ^ 40 * 1799996 * 2
def baseEnd_1799996 : Nat := 924263124170444741071975

theorem tailTrace_1799996 : CollatzResearch.WordTrace tailWord_1799996 prefixEnd_1799996 924263124170444741071975 := by
  unfold tailWord_1799996
  simp only [CollatzResearch.WordTrace]
  refine ⟨32825623793464690843681921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43767498391286254458242561 32825623793464690843681921)
  ·
    refine ⟨24619217845098518132761441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32825623793464690843681921 24619217845098518132761441)
    ·
      refine ⟨18464413383823888599571081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24619217845098518132761441 18464413383823888599571081)
      ·
        refine ⟨13848310037867916449678311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18464413383823888599571081 13848310037867916449678311)
        ·
          refine ⟨20772465056801874674517467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13848310037867916449678311 20772465056801874674517467)
          ·
            refine ⟨31158697585202812011776201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20772465056801874674517467 31158697585202812011776201)
            ·
              refine ⟨23369023188902109008832151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31158697585202812011776201 23369023188902109008832151)
              ·
                refine ⟨35053534783353163513248227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23369023188902109008832151 35053534783353163513248227)
                ·
                  refine ⟨52580302175029745269872341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35053534783353163513248227 52580302175029745269872341)
                  ·
                    refine ⟨1232350832227259654762633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52580302175029745269872341 1232350832227259654762633)
                    ·
                      refine ⟨924263124170444741071975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1232350832227259654762633 924263124170444741071975)
                      ·
                        rfl

theorem cell23_1799996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_1799996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1799996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1799996 prefixEnd_1799996 := by exact prefixLift 1799996
  have htrace : WordTrace (prefixWord ++ tailWord_1799996) baseStart_1799996 baseEnd_1799996 := by
    simpa [prefixWord, tailWord_1799996, baseEnd_1799996] using wordTrace_append hprefix tailTrace_1799996
  have hstable : (prefixWord ++ tailWord_1799996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799996).length < 2 ^ (prefixWord ++ tailWord_1799996).sum := by decide
  have hdescent : baseEnd_1799996 < baseStart_1799996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800009 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 3, 3, 4]
def baseStart_1800009 : Nat := 118140960795 + 1800009 * 2 ^ 59
def prefixEnd_1800009 : Nat := 4983230072969 + 3 ^ 40 * 1800009 * 2
def baseEnd_1800009 : Nat := 924269799418953190209415

theorem tailTrace_1800009 : CollatzResearch.WordTrace tailWord_1800009 prefixEnd_1800009 924269799418953190209415 := by
  unfold tailWord_1800009
  simp only [CollatzResearch.WordTrace]
  refine ⟨65651721735882284907587081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43767814490588189938391387 65651721735882284907587081)
  ·
    refine ⟨49238791301911713680690311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65651721735882284907587081 49238791301911713680690311)
    ·
      refine ⟨73858186952867570521035467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49238791301911713680690311 73858186952867570521035467)
      ·
        refine ⟨110787280429301355781553201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73858186952867570521035467 110787280429301355781553201)
        ·
          refine ⟨83090460321976016836164901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110787280429301355781553201 83090460321976016836164901)
          ·
            refine ⟨15579461310370503156780919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83090460321976016836164901 15579461310370503156780919)
            ·
              refine ⟨23369191965555754735171379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15579461310370503156780919 23369191965555754735171379)
              ·
                refine ⟨35053787948333632102757069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23369191965555754735171379 35053787948333632102757069)
                ·
                  refine ⟨13145170480625112038533901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35053787948333632102757069 13145170480625112038533901)
                  ·
                    refine ⟨4929438930234417014450213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13145170480625112038533901 4929438930234417014450213)
                    ·
                      refine ⟨924269799418953190209415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4929438930234417014450213 924269799418953190209415)
                      ·
                        rfl

theorem cell23_1800009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_1800009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800009 prefixEnd_1800009 := by exact prefixLift 1800009
  have htrace : WordTrace (prefixWord ++ tailWord_1800009) baseStart_1800009 baseEnd_1800009 := by
    simpa [prefixWord, tailWord_1800009, baseEnd_1800009] using wordTrace_append hprefix tailTrace_1800009
  have hstable : (prefixWord ++ tailWord_1800009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800009).length < 2 ^ (prefixWord ++ tailWord_1800009).sum := by decide
  have hdescent : baseEnd_1800009 < baseStart_1800009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800026 : List Nat := [3, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4]
def baseStart_1800026 : Nat := 118140960795 + 1800026 * 2 ^ 59
def prefixEnd_1800026 : Nat := 4983230072969 + 3 ^ 40 * 1800026 * 2
def baseEnd_1800026 : Nat := 924278528590079623696837

theorem tailTrace_1800026 : CollatzResearch.WordTrace tailWord_1800026 prefixEnd_1800026 924278528590079623696837 := by
  unfold tailWord_1800026
  simp only [CollatzResearch.WordTrace]
  refine ⟨16413085444205174202738983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43768227851213797873970621 16413085444205174202738983)
  ·
    refine ⟨24619628166307761304108475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16413085444205174202738983 24619628166307761304108475)
    ·
      refine ⟨36929442249461641956162713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24619628166307761304108475 36929442249461641956162713)
      ·
        refine ⟨27697081687096231467122035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36929442249461641956162713 27697081687096231467122035)
        ·
          refine ⟨41545622530644347200683053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27697081687096231467122035 41545622530644347200683053)
          ·
            refine ⟨15579608448991630200256145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41545622530644347200683053 15579608448991630200256145)
            ·
              refine ⟨11684706336743722650192109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15579608448991630200256145 11684706336743722650192109)
              ·
                refine ⟨4381764876278895993822041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11684706336743722650192109 4381764876278895993822041)
                ·
                  refine ⟨3286323657209171995366531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4381764876278895993822041 3286323657209171995366531)
                  ·
                    refine ⟨4929485485813757993049797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3286323657209171995366531 4929485485813757993049797)
                    ·
                      refine ⟨924278528590079623696837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4929485485813757993049797 924278528590079623696837)
                      ·
                        rfl

theorem cell23_1800026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_1800026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800026 prefixEnd_1800026 := by exact prefixLift 1800026
  have htrace : WordTrace (prefixWord ++ tailWord_1800026) baseStart_1800026 baseEnd_1800026 := by
    simpa [prefixWord, tailWord_1800026, baseEnd_1800026] using wordTrace_append hprefix tailTrace_1800026
  have hstable : (prefixWord ++ tailWord_1800026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800026).length < 2 ^ (prefixWord ++ tailWord_1800026).sum := by decide
  have hdescent : baseEnd_1800026 < baseStart_1800026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800049 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 8]
def baseStart_1800049 : Nat := 118140960795 + 1800049 * 2 ^ 59
def prefixEnd_1800049 : Nat := 4983230072969 + 3 ^ 40 * 1800049 * 2
def baseEnd_1800049 : Nat := 102698926516125892634359

theorem tailTrace_1800049 : CollatzResearch.WordTrace tailWord_1800049 prefixEnd_1800049 102698926516125892634359 := by
  unfold tailWord_1800049
  simp only [CollatzResearch.WordTrace]
  refine ⟨65653180655737371739043201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43768787103824914492695467 65653180655737371739043201)
  ·
    refine ⟨49239885491803028804282401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65653180655737371739043201 49239885491803028804282401)
    ·
      refine ⟨36929914118852271603211801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49239885491803028804282401 36929914118852271603211801)
      ·
        refine ⟨27697435589139203702408851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36929914118852271603211801 27697435589139203702408851)
        ·
          refine ⟨41546153383708805553613277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27697435589139203702408851 41546153383708805553613277)
          ·
            refine ⟨15579807518890802082604979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41546153383708805553613277 15579807518890802082604979)
            ·
              refine ⟨23369711278336203123907469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15579807518890802082604979 23369711278336203123907469)
              ·
                refine ⟨8763641729376076171465301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23369711278336203123907469 8763641729376076171465301)
                ·
                  refine ⟨102698926516125892634359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8763641729376076171465301 102698926516125892634359)
                  ·
                    rfl

theorem cell23_1800049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 8].length) (baseStart_1800049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800049 prefixEnd_1800049 := by exact prefixLift 1800049
  have htrace : WordTrace (prefixWord ++ tailWord_1800049) baseStart_1800049 baseEnd_1800049 := by
    simpa [prefixWord, tailWord_1800049, baseEnd_1800049] using wordTrace_append hprefix tailTrace_1800049
  have hstable : (prefixWord ++ tailWord_1800049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800049).length < 2 ^ (prefixWord ++ tailWord_1800049).sum := by decide
  have hdescent : baseEnd_1800049 < baseStart_1800049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800104 : List Nat := [2, 1, 6, 2, 1, 1, 1, 4, 1, 4]
def baseStart_1800104 : Nat := 118140960795 + 1800104 * 2 ^ 59
def prefixEnd_1800104 : Nat := 4983230072969 + 3 ^ 40 * 1800104 * 2
def baseEnd_1800104 : Nat := 308106193360376772840493

theorem tailTrace_1800104 : CollatzResearch.WordTrace tailWord_1800104 prefixEnd_1800104 308106193360376772840493 := by
  unfold tailWord_1800104
  simp only [CollatzResearch.WordTrace]
  refine ⟨32827593335269058066147683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43770124447025410754863577 32827593335269058066147683)
  ·
    refine ⟨49241390002903587099221525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32827593335269058066147683 49241390002903587099221525)
    ·
      refine ⟨2308190156386105645276009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49241390002903587099221525 2308190156386105645276009)
      ·
        refine ⟨1731142617289579233957007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2308190156386105645276009 1731142617289579233957007)
        ·
          refine ⟨2596713925934368850935511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1731142617289579233957007 2596713925934368850935511)
          ·
            refine ⟨3895070888901553276403267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2596713925934368850935511 3895070888901553276403267)
            ·
              refine ⟨5842606333352329914604901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3895070888901553276403267 5842606333352329914604901)
              ·
                refine ⟨1095488687503561858988419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5842606333352329914604901 1095488687503561858988419)
                ·
                  refine ⟨1643233031255342788482629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1095488687503561858988419 1643233031255342788482629)
                  ·
                    refine ⟨308106193360376772840493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1643233031255342788482629 308106193360376772840493)
                    ·
                      rfl

theorem cell23_1800104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_1800104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800104 prefixEnd_1800104 := by exact prefixLift 1800104
  have htrace : WordTrace (prefixWord ++ tailWord_1800104) baseStart_1800104 baseEnd_1800104 := by
    simpa [prefixWord, tailWord_1800104, baseEnd_1800104] using wordTrace_append hprefix tailTrace_1800104
  have hstable : (prefixWord ++ tailWord_1800104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800104).length < 2 ^ (prefixWord ++ tailWord_1800104).sum := by decide
  have hdescent : baseEnd_1800104 < baseStart_1800104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800177 : List Nat := [1, 2, 2, 2, 5, 1, 3, 1, 2, 4]
def baseStart_1800177 : Nat := 118140960795 + 1800177 * 2 ^ 59
def prefixEnd_1800177 : Nat := 4983230072969 + 3 ^ 40 * 1800177 * 2
def baseEnd_1800177 : Nat := 308118688056302844302881

theorem tailTrace_1800177 : CollatzResearch.WordTrace tailWord_1800177 prefixEnd_1800177 308118688056302844302881 := by
  unfold tailWord_1800177
  simp only [CollatzResearch.WordTrace]
  refine ⟨65657849199273649599702785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43771899466182433066468523 65657849199273649599702785)
  ·
    refine ⟨49243386899455237199777089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65657849199273649599702785 49243386899455237199777089)
    ·
      refine ⟨36932540174591427899832817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49243386899455237199777089 36932540174591427899832817)
      ·
        refine ⟨27699405130943570924874613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36932540174591427899832817 27699405130943570924874613)
        ·
          refine ⟨2596819231025959774206995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27699405130943570924874613 2596819231025959774206995)
          ·
            refine ⟨3895228846538939661310493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2596819231025959774206995 3895228846538939661310493)
            ·
              refine ⟨1460710817452102372991435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3895228846538939661310493 1460710817452102372991435)
              ·
                refine ⟨2191066226178153559487153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1460710817452102372991435 2191066226178153559487153)
                ·
                  refine ⟨1643299669633615169615365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2191066226178153559487153 1643299669633615169615365)
                  ·
                    refine ⟨308118688056302844302881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1643299669633615169615365 308118688056302844302881)
                    ·
                      rfl

theorem cell23_1800177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 2, 4].length) (baseStart_1800177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800177 prefixEnd_1800177 := by exact prefixLift 1800177
  have htrace : WordTrace (prefixWord ++ tailWord_1800177) baseStart_1800177 baseEnd_1800177 := by
    simpa [prefixWord, tailWord_1800177, baseEnd_1800177] using wordTrace_append hprefix tailTrace_1800177
  have hstable : (prefixWord ++ tailWord_1800177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800177).length < 2 ^ (prefixWord ++ tailWord_1800177).sum := by decide
  have hdescent : baseEnd_1800177 < baseStart_1800177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800190 : List Nat := [4, 2, 2, 2, 1, 1, 4, 7]
def baseStart_1800190 : Nat := 118140960795 + 1800190 * 2 ^ 59
def prefixEnd_1800190 : Nat := 4983230072969 + 3 ^ 40 * 1800190 * 2
def baseEnd_1800190 : Nat := 34235657015459888223929

theorem tailTrace_1800190 : CollatzResearch.WordTrace tailWord_1800190 prefixEnd_1800190 34235657015459888223929 := by
  unfold tailWord_1800190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8207290418528319102490753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43772215565484368546617349 8207290418528319102490753)
  ·
    refine ⟨6155467813896239326868065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8207290418528319102490753 6155467813896239326868065)
    ·
      refine ⟨4616600860422179495151049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6155467813896239326868065 4616600860422179495151049)
      ·
        refine ⟨3462450645316634621363287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4616600860422179495151049 3462450645316634621363287)
        ·
          refine ⟨5193675967974951932044931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3462450645316634621363287 5193675967974951932044931)
          ·
            refine ⟨7790513951962427898067397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5193675967974951932044931 7790513951962427898067397)
            ·
              refine ⟨1460721365992955230887637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7790513951962427898067397 1460721365992955230887637)
              ·
                refine ⟨34235657015459888223929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1460721365992955230887637 34235657015459888223929)
                ·
                  rfl

theorem cell23_1800190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 7].length) (baseStart_1800190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800190 prefixEnd_1800190 := by exact prefixLift 1800190
  have htrace : WordTrace (prefixWord ++ tailWord_1800190) baseStart_1800190 baseEnd_1800190 := by
    simpa [prefixWord, tailWord_1800190, baseEnd_1800190] using wordTrace_append hprefix tailTrace_1800190
  have hstable : (prefixWord ++ tailWord_1800190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800190).length < 2 ^ (prefixWord ++ tailWord_1800190).sum := by decide
  have hdescent : baseEnd_1800190 < baseStart_1800190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800234 : List Nat := [3, 1, 4, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_1800234 : Nat := 118140960795 + 1800234 * 2 ^ 59
def prefixEnd_1800234 : Nat := 4983230072969 + 3 ^ 40 * 1800234 * 2
def baseEnd_1800234 : Nat := 924385332566214809895881

theorem tailTrace_1800234 : CollatzResearch.WordTrace tailWord_1800234 prefixEnd_1800234 924385332566214809895881 := by
  unfold tailWord_1800234
  simp only [CollatzResearch.WordTrace]
  refine ⟨16414982040016787083631939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43773285440044765556351837 16414982040016787083631939)
  ·
    refine ⟨24622473060025180625447909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16414982040016787083631939 24622473060025180625447909)
    ·
      refine ⟨4616713698754721367271483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24622473060025180625447909 4616713698754721367271483)
      ·
        refine ⟨6925070548132082050907225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4616713698754721367271483 6925070548132082050907225)
        ·
          refine ⟨5193802911099061538180419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6925070548132082050907225 5193802911099061538180419)
          ·
            refine ⟨7790704366648592307270629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5193802911099061538180419 7790704366648592307270629)
            ·
              refine ⟨1460757068746611057613243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7790704366648592307270629 1460757068746611057613243)
              ·
                refine ⟨2191135603119916586419865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1460757068746611057613243 2191135603119916586419865)
                ·
                  refine ⟨1643351702339937439814899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2191135603119916586419865 1643351702339937439814899)
                  ·
                    refine ⟨2465027553509906159722349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1643351702339937439814899 2465027553509906159722349)
                    ·
                      refine ⟨924385332566214809895881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2465027553509906159722349 924385332566214809895881)
                      ·
                        rfl

theorem cell23_1800234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_1800234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800234 prefixEnd_1800234 := by exact prefixLift 1800234
  have htrace : WordTrace (prefixWord ++ tailWord_1800234) baseStart_1800234 baseEnd_1800234 := by
    simpa [prefixWord, tailWord_1800234, baseEnd_1800234] using wordTrace_append hprefix tailTrace_1800234
  have hstable : (prefixWord ++ tailWord_1800234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800234).length < 2 ^ (prefixWord ++ tailWord_1800234).sum := by decide
  have hdescent : baseEnd_1800234 < baseStart_1800234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800244 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_1800244 : Nat := 118140960795 + 1800244 * 2 ^ 59
def prefixEnd_1800244 : Nat := 4983230072969 + 3 ^ 40 * 1800244 * 2
def baseEnd_1800244 : Nat := 924390467372759770770835

theorem tailTrace_1800244 : CollatzResearch.WordTrace tailWord_1800244 prefixEnd_1800244 924390467372759770770835 := by
  unfold tailWord_1800244
  simp only [CollatzResearch.WordTrace]
  refine ⟨32830146445015460021195893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43773528593353946694927857 32830146445015460021195893)
  ·
    refine ⟨3077826229220199376987115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32830146445015460021195893 3077826229220199376987115)
    ·
      refine ⟨4616739343830299065480673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3077826229220199376987115 4616739343830299065480673)
      ·
        refine ⟨3462554507872724299110505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4616739343830299065480673 3462554507872724299110505)
        ·
          refine ⟨2596915880904543224332879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3462554507872724299110505 2596915880904543224332879)
          ·
            refine ⟨3895373821356814836499319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2596915880904543224332879 3895373821356814836499319)
            ·
              refine ⟨5843060732035222254748979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3895373821356814836499319 5843060732035222254748979)
              ·
                refine ⟨8764591098052833382123469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5843060732035222254748979 8764591098052833382123469)
                ·
                  refine ⟨3286721661769812518296301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8764591098052833382123469 3286721661769812518296301)
                  ·
                    refine ⟨1232520623163679694361113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3286721661769812518296301 1232520623163679694361113)
                    ·
                      refine ⟨924390467372759770770835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1232520623163679694361113 924390467372759770770835)
                      ·
                        rfl

theorem cell23_1800244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_1800244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800244 prefixEnd_1800244 := by exact prefixLift 1800244
  have htrace : WordTrace (prefixWord ++ tailWord_1800244) baseStart_1800244 baseEnd_1800244 := by
    simpa [prefixWord, tailWord_1800244, baseEnd_1800244] using wordTrace_append hprefix tailTrace_1800244
  have hstable : (prefixWord ++ tailWord_1800244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800244).length < 2 ^ (prefixWord ++ tailWord_1800244).sum := by decide
  have hdescent : baseEnd_1800244 < baseStart_1800244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800257 : List Nat := [1, 2, 5, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_1800257 : Nat := 118140960795 + 1800257 * 2 ^ 59
def prefixEnd_1800257 : Nat := 4983230072969 + 3 ^ 40 * 1800257 * 2
def baseEnd_1800257 : Nat := 924397142621268219908275

theorem tailTrace_1800257 : CollatzResearch.WordTrace tailWord_1800257 prefixEnd_1800257 924397142621268219908275 := by
  unfold tailWord_1800257
  simp only [CollatzResearch.WordTrace]
  refine ⟨65660767038983823262615025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43773844692655882175076683 65660767038983823262615025)
  ·
    refine ⟨49245575279237867446961269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65660767038983823262615025 49245575279237867446961269)
    ·
      refine ⟨4616772682428550073152619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49245575279237867446961269 4616772682428550073152619)
      ·
        refine ⟨6925159023642825109728929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4616772682428550073152619 6925159023642825109728929)
        ·
          refine ⟨5193869267732118832296697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6925159023642825109728929 5193869267732118832296697)
          ·
            refine ⟨3895401950799089124222523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5193869267732118832296697 3895401950799089124222523)
            ·
              refine ⟨5843102926198633686333785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3895401950799089124222523 5843102926198633686333785)
              ·
                refine ⟨4382327194648975264750339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5843102926198633686333785 4382327194648975264750339)
                ·
                  refine ⟨6573490791973462897125509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4382327194648975264750339 6573490791973462897125509)
                  ·
                    refine ⟨1232529523495024293211033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6573490791973462897125509 1232529523495024293211033)
                    ·
                      refine ⟨924397142621268219908275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1232529523495024293211033 924397142621268219908275)
                      ·
                        rfl

theorem cell23_1800257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_1800257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800257 prefixEnd_1800257 := by exact prefixLift 1800257
  have htrace : WordTrace (prefixWord ++ tailWord_1800257) baseStart_1800257 baseEnd_1800257 := by
    simpa [prefixWord, tailWord_1800257, baseEnd_1800257] using wordTrace_append hprefix tailTrace_1800257
  have hstable : (prefixWord ++ tailWord_1800257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800257).length < 2 ^ (prefixWord ++ tailWord_1800257).sum := by decide
  have hdescent : baseEnd_1800257 < baseStart_1800257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800273 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 2, 3, 3]
def baseStart_1800273 : Nat := 118140960795 + 1800273 * 2 ^ 59
def prefixEnd_1800273 : Nat := 4983230072969 + 3 ^ 40 * 1800273 * 2
def baseEnd_1800273 : Nat := 924405358311740157308201

theorem tailTrace_1800273 : CollatzResearch.WordTrace tailWord_1800273 prefixEnd_1800273 924405358311740157308201 := by
  unfold tailWord_1800273
  simp only [CollatzResearch.WordTrace]
  refine ⟨65661350606925857995197473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43774233737950571996798315 65661350606925857995197473)
  ·
    refine ⟨49246012955194393496398105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65661350606925857995197473 49246012955194393496398105)
    ·
      refine ⟨36934509716395795122298579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49246012955194393496398105 36934509716395795122298579)
      ·
        refine ⟨55401764574593692683447869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36934509716395795122298579 55401764574593692683447869)
        ·
          refine ⟨20775661715472634756292951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55401764574593692683447869 20775661715472634756292951)
          ·
            refine ⟨31163492573208952134439427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20775661715472634756292951 31163492573208952134439427)
            ·
              refine ⟨46745238859813428201659141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31163492573208952134439427 46745238859813428201659141)
              ·
                refine ⟨8764732286215017787811089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46745238859813428201659141 8764732286215017787811089)
                ·
                  refine ⟨6573549214661263340858317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8764732286215017787811089 6573549214661263340858317)
                  ·
                    refine ⟨2465080955497973752821869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6573549214661263340858317 2465080955497973752821869)
                    ·
                      refine ⟨924405358311740157308201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2465080955497973752821869 924405358311740157308201)
                      ·
                        rfl

theorem cell23_1800273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_1800273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800273 prefixEnd_1800273 := by exact prefixLift 1800273
  have htrace : WordTrace (prefixWord ++ tailWord_1800273) baseStart_1800273 baseEnd_1800273 := by
    simpa [prefixWord, tailWord_1800273, baseEnd_1800273] using wordTrace_append hprefix tailTrace_1800273
  have hstable : (prefixWord ++ tailWord_1800273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800273).length < 2 ^ (prefixWord ++ tailWord_1800273).sum := by decide
  have hdescent : baseEnd_1800273 < baseStart_1800273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800280 : List Nat := [2, 1, 2, 2, 1, 5, 1, 4, 5]
def baseStart_1800280 : Nat := 118140960795 + 1800280 * 2 ^ 59
def prefixEnd_1800280 : Nat := 4983230072969 + 3 ^ 40 * 1800280 * 2
def baseEnd_1800280 : Nat := 102712105852924625546741

theorem tailTrace_1800280 : CollatzResearch.WordTrace tailWord_1800280 prefixEnd_1800280 102712105852924625546741 := by
  unfold tailWord_1800280
  simp only [CollatzResearch.WordTrace]
  refine ⟨32830802958950249095351147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43774403945266998793801529 32830802958950249095351147)
  ·
    refine ⟨49246204438425373643026721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32830802958950249095351147 49246204438425373643026721)
    ·
      refine ⟨36934653328819030232270041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49246204438425373643026721 36934653328819030232270041)
      ·
        refine ⟨27700989996614272674202531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36934653328819030232270041 27700989996614272674202531)
        ·
          refine ⟨41551484994921409011303797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27700989996614272674202531 41551484994921409011303797)
          ·
            refine ⟨3895451718273882094809731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41551484994921409011303797 3895451718273882094809731)
            ·
              refine ⟨5843177577410823142214597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3895451718273882094809731 5843177577410823142214597)
              ·
                refine ⟨1095595795764529339165237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5843177577410823142214597 1095595795764529339165237)
                ·
                  refine ⟨102712105852924625546741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1095595795764529339165237 102712105852924625546741)
                  ·
                    rfl

theorem cell23_1800280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 5].length) (baseStart_1800280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800280 prefixEnd_1800280 := by exact prefixLift 1800280
  have htrace : WordTrace (prefixWord ++ tailWord_1800280) baseStart_1800280 baseEnd_1800280 := by
    simpa [prefixWord, tailWord_1800280, baseEnd_1800280] using wordTrace_append hprefix tailTrace_1800280
  have hstable : (prefixWord ++ tailWord_1800280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800280).length < 2 ^ (prefixWord ++ tailWord_1800280).sum := by decide
  have hdescent : baseEnd_1800280 < baseStart_1800280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800310 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_1800310 : Nat := 118140960795 + 1800310 * 2 ^ 59
def prefixEnd_1800310 : Nat := 4983230072969 + 3 ^ 40 * 1800310 * 2
def baseEnd_1800310 : Nat := 308141452365318837515177

theorem tailTrace_1800310 : CollatzResearch.WordTrace tailWord_1800310 prefixEnd_1800310 308141452365318837515177 := by
  unfold tailWord_1800310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4103918756736988332143399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43775133405194542209529589 4103918756736988332143399)
  ·
    refine ⟨6155878135105482498215099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4103918756736988332143399 6155878135105482498215099)
    ·
      refine ⟨9233817202658223747322649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6155878135105482498215099 9233817202658223747322649)
      ·
        refine ⟨6925362901993667810491987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9233817202658223747322649 6925362901993667810491987)
        ·
          refine ⟨10388044352990501715737981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6925362901993667810491987 10388044352990501715737981)
          ·
            refine ⟨3895516632371438143401743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10388044352990501715737981 3895516632371438143401743)
            ·
              refine ⟨5843274948557157215102615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3895516632371438143401743 5843274948557157215102615)
              ·
                refine ⟨8764912422835735822653923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5843274948557157215102615 8764912422835735822653923)
                ·
                  refine ⟨13147368634253603733980885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8764912422835735822653923 13147368634253603733980885)
                  ·
                    refine ⟨308141452365318837515177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13147368634253603733980885 308141452365318837515177)
                    ·
                      rfl

theorem cell23_1800310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_1800310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800310 prefixEnd_1800310 := by exact prefixLift 1800310
  have htrace : WordTrace (prefixWord ++ tailWord_1800310) baseStart_1800310 baseEnd_1800310 := by
    simpa [prefixWord, tailWord_1800310, baseEnd_1800310] using wordTrace_append hprefix tailTrace_1800310
  have hstable : (prefixWord ++ tailWord_1800310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800310).length < 2 ^ (prefixWord ++ tailWord_1800310).sum := by decide
  have hdescent : baseEnd_1800310 < baseStart_1800310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800342 : List Nat := [5, 3, 2, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_1800342 : Nat := 118140960795 + 1800342 * 2 ^ 59
def prefixEnd_1800342 : Nat := 4983230072969 + 3 ^ 40 * 1800342 * 2
def baseEnd_1800342 : Nat := 924440788476900387345385

theorem tailTrace_1800342 : CollatzResearch.WordTrace tailWord_1800342 prefixEnd_1800342 924440788476900387345385 := by
  unfold tailWord_1800342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4103991702729742673716205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43775911495783921852972853 4103991702729742673716205)
  ·
    refine ⟨1538996888523653502643577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4103991702729742673716205 1538996888523653502643577)
    ·
      refine ⟨1154247666392740126982683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1538996888523653502643577 1154247666392740126982683)
      ·
        refine ⟨1731371499589110190474025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1154247666392740126982683 1731371499589110190474025)
        ·
          refine ⟨1298528624691832642855519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1731371499589110190474025 1298528624691832642855519)
          ·
            refine ⟨1947792937037748964283279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298528624691832642855519 1947792937037748964283279)
            ·
              refine ⟨2921689405556623446424919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1947792937037748964283279 2921689405556623446424919)
              ·
                refine ⟨4382534108334935169637379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2921689405556623446424919 4382534108334935169637379)
                ·
                  refine ⟨6573801162502402754456069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4382534108334935169637379 6573801162502402754456069)
                  ·
                    refine ⟨1232587717969200516460513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6573801162502402754456069 1232587717969200516460513)
                    ·
                      refine ⟨924440788476900387345385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1232587717969200516460513 924440788476900387345385)
                      ·
                        rfl

theorem cell23_1800342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_1800342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800342 prefixEnd_1800342 := by exact prefixLift 1800342
  have htrace : WordTrace (prefixWord ++ tailWord_1800342) baseStart_1800342 baseEnd_1800342 := by
    simpa [prefixWord, tailWord_1800342, baseEnd_1800342] using wordTrace_append hprefix tailTrace_1800342
  have hstable : (prefixWord ++ tailWord_1800342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800342).length < 2 ^ (prefixWord ++ tailWord_1800342).sum := by decide
  have hdescent : baseEnd_1800342 < baseStart_1800342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800383 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 5, 5]
def baseStart_1800383 : Nat := 118140960795 + 1800383 * 2 ^ 59
def prefixEnd_1800383 : Nat := 4983230072969 + 3 ^ 40 * 1800383 * 2
def baseEnd_1800383 : Nat := 308153947061244908977565

theorem tailTrace_1800383 : CollatzResearch.WordTrace tailWord_1800383 prefixEnd_1800383 308153947061244908977565 := by
  unfold tailWord_1800383
  simp only [CollatzResearch.WordTrace]
  refine ⟨65665362636527346781701803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43776908424351564521134535 65665362636527346781701803)
  ·
    refine ⟨98498043954791020172552705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65665362636527346781701803 98498043954791020172552705)
    ·
      refine ⟨73873532966093265129414529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98498043954791020172552705 73873532966093265129414529)
      ·
        refine ⟨55405149724569948847060897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73873532966093265129414529 55405149724569948847060897)
        ·
          refine ⟨41553862293427461635295673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55405149724569948847060897 41553862293427461635295673)
          ·
            refine ⟨31165396720070596226471755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41553862293427461635295673 31165396720070596226471755)
            ·
              refine ⟨46748095080105894339707633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31165396720070596226471755 46748095080105894339707633)
              ·
                refine ⟨35061071310079420754780725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46748095080105894339707633 35061071310079420754780725)
                ·
                  refine ⟨3286975435319945695760693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35061071310079420754780725 3286975435319945695760693)
                  ·
                    refine ⟨308153947061244908977565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3286975435319945695760693 308153947061244908977565)
                    ·
                      rfl

theorem cell23_1800383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 5].length) (baseStart_1800383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800383 prefixEnd_1800383 := by exact prefixLift 1800383
  have htrace : WordTrace (prefixWord ++ tailWord_1800383) baseStart_1800383 baseEnd_1800383 := by
    simpa [prefixWord, tailWord_1800383, baseEnd_1800383] using wordTrace_append hprefix tailTrace_1800383
  have hstable : (prefixWord ++ tailWord_1800383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800383).length < 2 ^ (prefixWord ++ tailWord_1800383).sum := by decide
  have hdescent : baseEnd_1800383 < baseStart_1800383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800418 : List Nat := [3, 3, 4, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1800418 : Nat := 118140960795 + 1800418 * 2 ^ 59
def prefixEnd_1800418 : Nat := 4983230072969 + 3 ^ 40 * 1800418 * 2
def baseEnd_1800418 : Nat := 924479813006642089995035

theorem tailTrace_1800418 : CollatzResearch.WordTrace tailWord_1800418 prefixEnd_1800418 924479813006642089995035 := by
  unfold tailWord_1800418
  simp only [CollatzResearch.WordTrace]
  refine ⟨16416659797850136939806477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43777759460933698506150605 16416659797850136939806477)
  ·
    refine ⟨6156247424193801352427429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16416659797850136939806477 6156247424193801352427429)
    ·
      refine ⟨1154296392036337753580143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6156247424193801352427429 1154296392036337753580143)
      ·
        refine ⟨1731444588054506630370215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1154296392036337753580143 1731444588054506630370215)
        ·
          refine ⟨2597166882081759945555323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1731444588054506630370215 2597166882081759945555323)
          ·
            refine ⟨3895750323122639918332985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2597166882081759945555323 3895750323122639918332985)
            ·
              refine ⟨2921812742341979938749739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3895750323122639918332985 2921812742341979938749739)
              ·
                refine ⟨4382719113512969908124609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2921812742341979938749739 4382719113512969908124609)
                ·
                  refine ⟨3287039335134727431093457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4382719113512969908124609 3287039335134727431093457)
                  ·
                    refine ⟨2465279501351045573320093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3287039335134727431093457 2465279501351045573320093)
                    ·
                      refine ⟨924479813006642089995035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2465279501351045573320093 924479813006642089995035)
                      ·
                        rfl

theorem cell23_1800418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1800418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800418 prefixEnd_1800418 := by exact prefixLift 1800418
  have htrace : WordTrace (prefixWord ++ tailWord_1800418) baseStart_1800418 baseEnd_1800418 := by
    simpa [prefixWord, tailWord_1800418, baseEnd_1800418] using wordTrace_append hprefix tailTrace_1800418
  have hstable : (prefixWord ++ tailWord_1800418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800418).length < 2 ^ (prefixWord ++ tailWord_1800418).sum := by decide
  have hdescent : baseEnd_1800418 < baseStart_1800418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800424 : List Nat := [2, 1, 4, 1, 2, 3, 2, 1, 2, 3, 2]
def baseStart_1800424 : Nat := 118140960795 + 1800424 * 2 ^ 59
def prefixEnd_1800424 : Nat := 4983230072969 + 3 ^ 40 * 1800424 * 2
def baseEnd_1800424 : Nat := 924482893890569066520007

theorem tailTrace_1800424 : CollatzResearch.WordTrace tailWord_1800424 prefixEnd_1800424 924482893890569066520007 := by
  unfold tailWord_1800424
  simp only [CollatzResearch.WordTrace]
  refine ⟨32833429014689405391972163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43777905352919207189296217 32833429014689405391972163)
  ·
    refine ⟨49250143522034108087958245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32833429014689405391972163 49250143522034108087958245)
    ·
      refine ⟨9234401910381395266492171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49250143522034108087958245 9234401910381395266492171)
      ·
        refine ⟨13851602865572092899738257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9234401910381395266492171 13851602865572092899738257)
        ·
          refine ⟨10388702149179069674803693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13851602865572092899738257 10388702149179069674803693)
          ·
            refine ⟨3895763305942151128051385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10388702149179069674803693 3895763305942151128051385)
            ·
              refine ⟨2921822479456613346038539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3895763305942151128051385 2921822479456613346038539)
              ·
                refine ⟨4382733719184920019057809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2921822479456613346038539 4382733719184920019057809)
                ·
                  refine ⟨3287050289388690014293357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4382733719184920019057809 3287050289388690014293357)
                  ·
                    refine ⟨1232643858520758755360009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3287050289388690014293357 1232643858520758755360009)
                    ·
                      refine ⟨924482893890569066520007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1232643858520758755360009 924482893890569066520007)
                      ·
                        rfl

theorem cell23_1800424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_1800424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800424 prefixEnd_1800424 := by exact prefixLift 1800424
  have htrace : WordTrace (prefixWord ++ tailWord_1800424) baseStart_1800424 baseEnd_1800424 := by
    simpa [prefixWord, tailWord_1800424, baseEnd_1800424] using wordTrace_append hprefix tailTrace_1800424
  have hstable : (prefixWord ++ tailWord_1800424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800424).length < 2 ^ (prefixWord ++ tailWord_1800424).sum := by decide
  have hdescent : baseEnd_1800424 < baseStart_1800424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800434 : List Nat := [3, 2, 1, 3, 2, 2, 3, 1, 1, 5]
def baseStart_1800434 : Nat := 118140960795 + 1800434 * 2 ^ 59
def prefixEnd_1800434 : Nat := 4983230072969 + 3 ^ 40 * 1800434 * 2
def baseEnd_1800434 : Nat := 308162676232371342464987

theorem tailTrace_1800434 : CollatzResearch.WordTrace tailWord_1800434 prefixEnd_1800434 308162676232371342464987 := by
  unfold tailWord_1800434
  simp only [CollatzResearch.WordTrace]
  refine ⟨16416805689835645622952089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43778148506228388327872237 16416805689835645622952089)
  ·
    refine ⟨12312604267376734217214067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16416805689835645622952089 12312604267376734217214067)
    ·
      refine ⟨18468906401065101325821101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12312604267376734217214067 18468906401065101325821101)
      ·
        refine ⟨6925839900399412997182913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18468906401065101325821101 6925839900399412997182913)
        ·
          refine ⟨5194379925299559747887185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6925839900399412997182913 5194379925299559747887185)
          ·
            refine ⟨3895784943974669810915389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5194379925299559747887185 3895784943974669810915389)
            ·
              refine ⟨1460919353990501179093271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3895784943974669810915389 1460919353990501179093271)
              ·
                refine ⟨2191379030985751768639907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1460919353990501179093271 2191379030985751768639907)
                ·
                  refine ⟨3287068546478627652959861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2191379030985751768639907 3287068546478627652959861)
                  ·
                    refine ⟨308162676232371342464987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3287068546478627652959861 308162676232371342464987)
                    ·
                      rfl

theorem cell23_1800434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_1800434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800434 prefixEnd_1800434 := by exact prefixLift 1800434
  have htrace : WordTrace (prefixWord ++ tailWord_1800434) baseStart_1800434 baseEnd_1800434 := by
    simpa [prefixWord, tailWord_1800434, baseEnd_1800434] using wordTrace_append hprefix tailTrace_1800434
  have hstable : (prefixWord ++ tailWord_1800434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800434).length < 2 ^ (prefixWord ++ tailWord_1800434).sum := by decide
  have hdescent : baseEnd_1800434 < baseStart_1800434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800447 : List Nat := [1, 1, 2, 2, 1, 4, 4, 2, 2, 4]
def baseStart_1800447 : Nat := 118140960795 + 1800447 * 2 ^ 59
def prefixEnd_1800447 : Nat := 4983230072969 + 3 ^ 40 * 1800447 * 2
def baseEnd_1800447 : Nat := 308164901315207492177467

theorem tailTrace_1800447 : CollatzResearch.WordTrace tailWord_1800447 prefixEnd_1800447 308164901315207492177467 := by
  unfold tailWord_1800447
  simp only [CollatzResearch.WordTrace]
  refine ⟨65667696908295485712031595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43778464605530323808021063 65667696908295485712031595)
  ·
    refine ⟨98501545362443228568047393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65667696908295485712031595 98501545362443228568047393)
    ·
      refine ⟨73876159021832421426035545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98501545362443228568047393 73876159021832421426035545)
      ·
        refine ⟨55407119266374316069526659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73876159021832421426035545 55407119266374316069526659)
        ·
          refine ⟨83110678899561474104289989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55407119266374316069526659 83110678899561474104289989)
          ·
            refine ⟨15583252293667776394554373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83110678899561474104289989 15583252293667776394554373)
            ·
              refine ⟨2921859805062708073978945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15583252293667776394554373 2921859805062708073978945)
              ·
                refine ⟨2191394853797031055484209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2921859805062708073978945 2191394853797031055484209)
                ·
                  refine ⟨1643546140347773291613157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2191394853797031055484209 1643546140347773291613157)
                  ·
                    refine ⟨308164901315207492177467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1643546140347773291613157 308164901315207492177467)
                    ·
                      rfl

theorem cell23_1800447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 4].length) (baseStart_1800447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800447 prefixEnd_1800447 := by exact prefixLift 1800447
  have htrace : WordTrace (prefixWord ++ tailWord_1800447) baseStart_1800447 baseEnd_1800447 := by
    simpa [prefixWord, tailWord_1800447, baseEnd_1800447] using wordTrace_append hprefix tailTrace_1800447
  have hstable : (prefixWord ++ tailWord_1800447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800447).length < 2 ^ (prefixWord ++ tailWord_1800447).sum := by decide
  have hdescent : baseEnd_1800447 < baseStart_1800447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800453 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 2, 2, 7]
def baseStart_1800453 : Nat := 118140960795 + 1800453 * 2 ^ 59
def prefixEnd_1800453 : Nat := 4983230072969 + 3 ^ 40 * 1800453 * 2
def baseEnd_1800453 : Nat := 924497784829549453057373

theorem tailTrace_1800453 : CollatzResearch.WordTrace tailWord_1800453 prefixEnd_1800453 924497784829549453057373 := by
  unfold tailWord_1800453
  simp only [CollatzResearch.WordTrace]
  refine ⟨65667915746273748736750013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43778610497515832491166675 65667915746273748736750013)
  ·
    refine ⟨24625468404852655776281255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65667915746273748736750013 24625468404852655776281255)
    ·
      refine ⟨36938202607278983664421883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24625468404852655776281255 36938202607278983664421883)
      ·
        refine ⟨55407303910918475496632825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36938202607278983664421883 55407303910918475496632825)
        ·
          refine ⟨41555477933188856622474619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55407303910918475496632825 41555477933188856622474619)
          ·
            refine ⟨62333216899783284933711929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41555477933188856622474619 62333216899783284933711929)
            ·
              refine ⟨46749912674837463700283947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62333216899783284933711929 46749912674837463700283947)
              ·
                refine ⟨70124869012256195550425921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46749912674837463700283947 70124869012256195550425921)
                ·
                  refine ⟨52593651759192146662819441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70124869012256195550425921 52593651759192146662819441)
                  ·
                    refine ⟨39445238819394109997114581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52593651759192146662819441 39445238819394109997114581)
                    ·
                      refine ⟨924497784829549453057373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39445238819394109997114581 924497784829549453057373)
                      ·
                        rfl

theorem cell23_1800453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_1800453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800453 prefixEnd_1800453 := by exact prefixLift 1800453
  have htrace : WordTrace (prefixWord ++ tailWord_1800453) baseStart_1800453 baseEnd_1800453 := by
    simpa [prefixWord, tailWord_1800453, baseEnd_1800453] using wordTrace_append hprefix tailTrace_1800453
  have hstable : (prefixWord ++ tailWord_1800453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800453).length < 2 ^ (prefixWord ++ tailWord_1800453).sum := by decide
  have hdescent : baseEnd_1800453 < baseStart_1800453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800463 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 6]
def baseStart_1800463 : Nat := 118140960795 + 1800463 * 2 ^ 59
def prefixEnd_1800463 : Nat := 4983230072969 + 3 ^ 40 * 1800463 * 2
def baseEnd_1800463 : Nat := 924502919636094413932327

theorem tailTrace_1800463 : CollatzResearch.WordTrace tailWord_1800463 prefixEnd_1800463 924502919636094413932327 := by
  unfold tailWord_1800463
  simp only [CollatzResearch.WordTrace]
  refine ⟨65668280476237520444614043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43778853650825013629742695 65668280476237520444614043)
  ·
    refine ⟨98502420714356280666921065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65668280476237520444614043 98502420714356280666921065)
    ·
      refine ⟨73876815535767210500190799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98502420714356280666921065 73876815535767210500190799)
      ·
        refine ⟨110815223303650815750286199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73876815535767210500190799 110815223303650815750286199)
        ·
          refine ⟨166222834955476223625429299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110815223303650815750286199 166222834955476223625429299)
          ·
            refine ⟨249334252433214335438143949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166222834955476223625429299 249334252433214335438143949)
            ·
              refine ⟨93500344662455375789303981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249334252433214335438143949 93500344662455375789303981)
              ·
                refine ⟨35062629248420765920988993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93500344662455375789303981 35062629248420765920988993)
                ·
                  refine ⟨26296971936315574440741745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35062629248420765920988993 26296971936315574440741745)
                  ·
                    refine ⟨19722728952236680830556309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26296971936315574440741745 19722728952236680830556309)
                    ·
                      refine ⟨924502919636094413932327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19722728952236680830556309 924502919636094413932327)
                      ·
                        rfl

theorem cell23_1800463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_1800463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800463 prefixEnd_1800463 := by exact prefixLift 1800463
  have htrace : WordTrace (prefixWord ++ tailWord_1800463) baseStart_1800463 baseEnd_1800463 := by
    simpa [prefixWord, tailWord_1800463, baseEnd_1800463] using wordTrace_append hprefix tailTrace_1800463
  have hstable : (prefixWord ++ tailWord_1800463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800463).length < 2 ^ (prefixWord ++ tailWord_1800463).sum := by decide
  have hdescent : baseEnd_1800463 < baseStart_1800463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800488 : List Nat := [2, 1, 5, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_1800488 : Nat := 118140960795 + 1800488 * 2 ^ 59
def prefixEnd_1800488 : Nat := 4983230072969 + 3 ^ 40 * 1800488 * 2
def baseEnd_1800488 : Nat := 924515756652456816119713

theorem tailTrace_1800488 : CollatzResearch.WordTrace tailWord_1800488 prefixEnd_1800488 924515756652456816119713 := by
  unfold tailWord_1800488
  simp only [CollatzResearch.WordTrace]
  refine ⟨32834596150573474857137059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43779461534097966476182745 32834596150573474857137059)
  ·
    refine ⟨49251894225860212285705589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32834596150573474857137059 49251894225860212285705589)
    ·
      refine ⟨4617365083674394901784899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49251894225860212285705589 4617365083674394901784899)
      ·
        refine ⟨6926047625511592352677349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4617365083674394901784899 6926047625511592352677349)
        ·
          refine ⟨1298633929783423566127003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6926047625511592352677349 1298633929783423566127003)
          ·
            refine ⟨1947950894675135349190505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298633929783423566127003 1947950894675135349190505)
            ·
              refine ⟨1460963171006351511892879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1947950894675135349190505 1460963171006351511892879)
              ·
                refine ⟨2191444756509527267839319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1460963171006351511892879 2191444756509527267839319)
                ·
                  refine ⟨3287167134764290901758979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2191444756509527267839319 3287167134764290901758979)
                  ·
                    refine ⟨4930750702146436352638469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3287167134764290901758979 4930750702146436352638469)
                    ·
                      refine ⟨924515756652456816119713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4930750702146436352638469 924515756652456816119713)
                      ·
                        rfl

theorem cell23_1800488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_1800488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800488 prefixEnd_1800488 := by exact prefixLift 1800488
  have htrace : WordTrace (prefixWord ++ tailWord_1800488) baseStart_1800488 baseEnd_1800488 := by
    simpa [prefixWord, tailWord_1800488, baseEnd_1800488] using wordTrace_append hprefix tailTrace_1800488
  have hstable : (prefixWord ++ tailWord_1800488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800488).length < 2 ^ (prefixWord ++ tailWord_1800488).sum := by decide
  have hdescent : baseEnd_1800488 < baseStart_1800488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800504 : List Nat := [2, 1, 2, 1, 3, 1, 5, 2, 2, 1, 3]
def baseStart_1800504 : Nat := 118140960795 + 1800504 * 2 ^ 59
def prefixEnd_1800504 : Nat := 4983230072969 + 3 ^ 40 * 1800504 * 2
def baseEnd_1800504 : Nat := 924523972342928753519639

theorem tailTrace_1800504 : CollatzResearch.WordTrace tailWord_1800504 prefixEnd_1800504 924523972342928753519639 := by
  unfold tailWord_1800504
  simp only [CollatzResearch.WordTrace]
  refine ⟨32834887934544492223428283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43779850579392656297904377 32834887934544492223428283)
  ·
    refine ⟨49252331901816738335142425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32834887934544492223428283 49252331901816738335142425)
    ·
      refine ⟨36939248926362553751356819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49252331901816738335142425 36939248926362553751356819)
      ·
        refine ⟨55408873389543830627035229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36939248926362553751356819 55408873389543830627035229)
        ·
          refine ⟨20778327521078936485138211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55408873389543830627035229 20778327521078936485138211)
          ·
            refine ⟨31167491281618404727707317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20778327521078936485138211 31167491281618404727707317)
            ·
              refine ⟨2921952307651725443222561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31167491281618404727707317 2921952307651725443222561)
              ·
                refine ⟨2191464230738794082416921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2921952307651725443222561 2191464230738794082416921)
                ·
                  refine ⟨1643598173054095561812691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2191464230738794082416921 1643598173054095561812691)
                  ·
                    refine ⟨2465397259581143342719037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1643598173054095561812691 2465397259581143342719037)
                    ·
                      refine ⟨924523972342928753519639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2465397259581143342719037 924523972342928753519639)
                      ·
                        rfl

theorem cell23_1800504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 2, 1, 3].length) (baseStart_1800504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800504 prefixEnd_1800504 := by exact prefixLift 1800504
  have htrace : WordTrace (prefixWord ++ tailWord_1800504) baseStart_1800504 baseEnd_1800504 := by
    simpa [prefixWord, tailWord_1800504, baseEnd_1800504] using wordTrace_append hprefix tailTrace_1800504
  have hstable : (prefixWord ++ tailWord_1800504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800504).length < 2 ^ (prefixWord ++ tailWord_1800504).sum := by decide
  have hdescent : baseEnd_1800504 < baseStart_1800504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800520 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 2, 6]
def baseStart_1800520 : Nat := 118140960795 + 1800520 * 2 ^ 59
def prefixEnd_1800520 : Nat := 4983230072969 + 3 ^ 40 * 1800520 * 2
def baseEnd_1800520 : Nat := 308177396011133563639855

theorem tailTrace_1800520 : CollatzResearch.WordTrace tailWord_1800520 prefixEnd_1800520 308177396011133563639855 := by
  unfold tailWord_1800520
  simp only [CollatzResearch.WordTrace]
  refine ⟨32835179718515509589719507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43780239624687346119626009 32835179718515509589719507)
  ·
    refine ⟨49252769577773264384579261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32835179718515509589719507 49252769577773264384579261)
    ·
      refine ⟨18469788591664974144217223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49252769577773264384579261 18469788591664974144217223)
      ·
        refine ⟨27704682887497461216325835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18469788591664974144217223 27704682887497461216325835)
        ·
          refine ⟨41557024331246191824488753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27704682887497461216325835 41557024331246191824488753)
          ·
            refine ⟨31167768248434643868366565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41557024331246191824488753 31167768248434643868366565)
            ·
              refine ⟨5843956546581495725318731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31167768248434643868366565 5843956546581495725318731)
              ·
                refine ⟨8765934819872243587978097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5843956546581495725318731 8765934819872243587978097)
                ·
                  refine ⟨6574451114904182690983573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8765934819872243587978097 6574451114904182690983573)
                  ·
                    refine ⟨308177396011133563639855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6574451114904182690983573 308177396011133563639855)
                    ·
                      rfl

theorem cell23_1800520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_1800520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800520 prefixEnd_1800520 := by exact prefixLift 1800520
  have htrace : WordTrace (prefixWord ++ tailWord_1800520) baseStart_1800520 baseEnd_1800520 := by
    simpa [prefixWord, tailWord_1800520, baseEnd_1800520] using wordTrace_append hprefix tailTrace_1800520
  have hstable : (prefixWord ++ tailWord_1800520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800520).length < 2 ^ (prefixWord ++ tailWord_1800520).sum := by decide
  have hdescent : baseEnd_1800520 < baseStart_1800520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800527 : List Nat := [1, 1, 2, 1, 1, 2, 1, 7, 1, 4, 2]
def baseStart_1800527 : Nat := 118140960795 + 1800527 * 2 ^ 59
def prefixEnd_1800527 : Nat := 4983230072969 + 3 ^ 40 * 1800527 * 2
def baseEnd_1800527 : Nat := 924535782397982163532033

theorem tailTrace_1800527 : CollatzResearch.WordTrace tailWord_1800527 prefixEnd_1800527 924535782397982163532033 := by
  unfold tailWord_1800527
  simp only [CollatzResearch.WordTrace]
  refine ⟨65670614748005659374943835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43780409832003772916629223 65670614748005659374943835)
  ·
    refine ⟨98505922122008489062415753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65670614748005659374943835 98505922122008489062415753)
    ·
      refine ⟨73879441591506366796811815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98505922122008489062415753 73879441591506366796811815)
      ·
        refine ⟨110819162387259550195217723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73879441591506366796811815 110819162387259550195217723)
        ·
          refine ⟨166228743580889325292826585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110819162387259550195217723 166228743580889325292826585)
          ·
            refine ⟨124671557685666993969619939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166228743580889325292826585 124671557685666993969619939)
            ·
              refine ⟨187007336528500490954429909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124671557685666993969619939 187007336528500490954429909)
              ·
                refine ⟨4382984449886730256744451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 187007336528500490954429909 4382984449886730256744451)
                ·
                  refine ⟨6574476674830095385116677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4382984449886730256744451 6574476674830095385116677)
                  ·
                    refine ⟨1232714376530642884709377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6574476674830095385116677 1232714376530642884709377)
                    ·
                      refine ⟨924535782397982163532033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1232714376530642884709377 924535782397982163532033)
                      ·
                        rfl

theorem cell23_1800527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 4, 2].length) (baseStart_1800527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800527 prefixEnd_1800527 := by exact prefixLift 1800527
  have htrace : WordTrace (prefixWord ++ tailWord_1800527) baseStart_1800527 baseEnd_1800527 := by
    simpa [prefixWord, tailWord_1800527, baseEnd_1800527] using wordTrace_append hprefix tailTrace_1800527
  have hstable : (prefixWord ++ tailWord_1800527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800527).length < 2 ^ (prefixWord ++ tailWord_1800527).sum := by decide
  have hdescent : baseEnd_1800527 < baseStart_1800527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800617 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 3, 6, 2]
def baseStart_1800617 : Nat := 118140960795 + 1800617 * 2 ^ 59
def prefixEnd_1800617 : Nat := 4983230072969 + 3 ^ 40 * 1800617 * 2
def baseEnd_1800617 : Nat := 924581995656886811406619

theorem tailTrace_1800617 : CollatzResearch.WordTrace tailWord_1800617 prefixEnd_1800617 924581995656886811406619 := by
  unfold tailWord_1800617
  simp only [CollatzResearch.WordTrace]
  refine ⟨65673897317679604745720105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43782598211786403163813403 65673897317679604745720105)
  ·
    refine ⟨49255422988259703559290079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65673897317679604745720105 49255422988259703559290079)
    ·
      refine ⟨73883134482389555338935119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49255422988259703559290079 73883134482389555338935119)
      ·
        refine ⟨110824701723584333008402679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73883134482389555338935119 110824701723584333008402679)
        ·
          refine ⟨166237052585376499512604019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110824701723584333008402679 166237052585376499512604019)
          ·
            refine ⟨249355578878064749268906029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166237052585376499512604019 249355578878064749268906029)
            ·
              refine ⟨93508342079274280975839761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249355578878064749268906029 93508342079274280975839761)
              ·
                refine ⟨70131256559455710731879821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93508342079274280975839761 70131256559455710731879821)
                ·
                  refine ⟨26299221209795891524454933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70131256559455710731879821 26299221209795891524454933)
                  ·
                    refine ⟨1232775994209182415208825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26299221209795891524454933 1232775994209182415208825)
                    ·
                      refine ⟨924581995656886811406619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1232775994209182415208825 924581995656886811406619)
                      ·
                        rfl

theorem cell23_1800617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 6, 2].length) (baseStart_1800617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800617 prefixEnd_1800617 := by exact prefixLift 1800617
  have htrace : WordTrace (prefixWord ++ tailWord_1800617) baseStart_1800617 baseEnd_1800617 := by
    simpa [prefixWord, tailWord_1800617, baseEnd_1800617] using wordTrace_append hprefix tailTrace_1800617
  have hstable : (prefixWord ++ tailWord_1800617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800617).length < 2 ^ (prefixWord ++ tailWord_1800617).sum := by decide
  have hdescent : baseEnd_1800617 < baseStart_1800617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800620 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 5]
def baseStart_1800620 : Nat := 118140960795 + 1800620 * 2 ^ 59
def prefixEnd_1800620 : Nat := 4983230072969 + 3 ^ 40 * 1800620 * 2
def baseEnd_1800620 : Nat := 924583536098850299669105

theorem tailTrace_1800620 : CollatzResearch.WordTrace tailWord_1800620 prefixEnd_1800620 924583536098850299669105 := by
  unfold tailWord_1800620
  simp only [CollatzResearch.WordTrace]
  refine ⟨32837003368334368129039657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43782671157779157505386209 32837003368334368129039657)
  ·
    refine ⟨24627752526250776096779743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32837003368334368129039657 24627752526250776096779743)
    ·
      refine ⟨36941628789376164145169615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24627752526250776096779743 36941628789376164145169615)
      ·
        refine ⟨55412443184064246217754423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36941628789376164145169615 55412443184064246217754423)
        ·
          refine ⟨83118664776096369326631635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55412443184064246217754423 83118664776096369326631635)
          ·
            refine ⟨124677997164144553989947453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83118664776096369326631635 124677997164144553989947453)
            ·
              refine ⟨46754248936554207746230295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124677997164144553989947453 46754248936554207746230295)
              ·
                refine ⟨70131373404831311619345443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46754248936554207746230295 70131373404831311619345443)
                ·
                  refine ⟨105197060107246967429018165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70131373404831311619345443 105197060107246967429018165)
                  ·
                    refine ⟨9862224385054403196470453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105197060107246967429018165 9862224385054403196470453)
                    ·
                      refine ⟨924583536098850299669105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9862224385054403196470453 924583536098850299669105)
                      ·
                        rfl

theorem cell23_1800620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_1800620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800620 prefixEnd_1800620 := by exact prefixLift 1800620
  have htrace : WordTrace (prefixWord ++ tailWord_1800620) baseStart_1800620 baseEnd_1800620 := by
    simpa [prefixWord, tailWord_1800620, baseEnd_1800620] using wordTrace_append hprefix tailTrace_1800620
  have hstable : (prefixWord ++ tailWord_1800620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800620).length < 2 ^ (prefixWord ++ tailWord_1800620).sum := by decide
  have hdescent : baseEnd_1800620 < baseStart_1800620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800628 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_1800628 : Nat := 118140960795 + 1800628 * 2 ^ 59
def prefixEnd_1800628 : Nat := 4983230072969 + 3 ^ 40 * 1800628 * 2
def baseEnd_1800628 : Nat := 924587643944086268369069

theorem tailTrace_1800628 : CollatzResearch.WordTrace tailWord_1800628 prefixEnd_1800628 924587643944086268369069 := by
  unfold tailWord_1800628
  simp only [CollatzResearch.WordTrace]
  refine ⟨32837149260319876812185269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43782865680426502416247025 32837149260319876812185269)
  ·
    refine ⟨3078482743154988451142369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32837149260319876812185269 3078482743154988451142369)
    ·
      refine ⟨2308862057366241338356777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3078482743154988451142369 2308862057366241338356777)
      ·
        refine ⟨1731646543024681003767583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2308862057366241338356777 1731646543024681003767583)
        ·
          refine ⟨2597469814537021505651375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1731646543024681003767583 2597469814537021505651375)
          ·
            refine ⟨3896204721805532258477063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2597469814537021505651375 3896204721805532258477063)
            ·
              refine ⟨5844307082708298387715595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3896204721805532258477063 5844307082708298387715595)
              ·
                refine ⟨8766460624062447581573393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5844307082708298387715595 8766460624062447581573393)
                ·
                  refine ⟨6574845468046835686180045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8766460624062447581573393 6574845468046835686180045)
                  ·
                    refine ⟨2465567050517563382317517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6574845468046835686180045 2465567050517563382317517)
                    ·
                      refine ⟨924587643944086268369069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2465567050517563382317517 924587643944086268369069)
                      ·
                        rfl

theorem cell23_1800628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_1800628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800628 prefixEnd_1800628 := by exact prefixLift 1800628
  have htrace : WordTrace (prefixWord ++ tailWord_1800628) baseStart_1800628 baseEnd_1800628 := by
    simpa [prefixWord, tailWord_1800628, baseEnd_1800628] using wordTrace_append hprefix tailTrace_1800628
  have hstable : (prefixWord ++ tailWord_1800628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800628).length < 2 ^ (prefixWord ++ tailWord_1800628).sum := by decide
  have hdescent : baseEnd_1800628 < baseStart_1800628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800640 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 10]
def baseStart_1800640 : Nat := 118140960795 + 1800640 * 2 ^ 59
def prefixEnd_1800640 : Nat := 4983230072969 + 3 ^ 40 * 1800640 * 2
def baseEnd_1800640 : Nat := 102732645079104469046557

theorem tailTrace_1800640 : CollatzResearch.WordTrace tailWord_1800640 prefixEnd_1800640 102732645079104469046557 := by
  unfold tailWord_1800640
  simp only [CollatzResearch.WordTrace]
  refine ⟨32837368098298139836903687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43783157464397519782538249 32837368098298139836903687)
  ·
    refine ⟨49256052147447209755355531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32837368098298139836903687 49256052147447209755355531)
    ·
      refine ⟨73884078221170814633033297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49256052147447209755355531 73884078221170814633033297)
      ·
        refine ⟨55413058665878110974774973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73884078221170814633033297 55413058665878110974774973)
        ·
          refine ⟨20779896999704291615540615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55413058665878110974774973 20779896999704291615540615)
          ·
            refine ⟨31169845499556437423310923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20779896999704291615540615 31169845499556437423310923)
            ·
              refine ⟨46754768249334656134966385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31169845499556437423310923 46754768249334656134966385)
              ·
                refine ⟨35066076187000992101224789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46754768249334656134966385 35066076187000992101224789)
                ·
                  refine ⟨102732645079104469046557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 35066076187000992101224789 102732645079104469046557)
                  ·
                    rfl

theorem cell23_1800640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 10].length) (baseStart_1800640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800640 prefixEnd_1800640 := by exact prefixLift 1800640
  have htrace : WordTrace (prefixWord ++ tailWord_1800640) baseStart_1800640 baseEnd_1800640 := by
    simpa [prefixWord, tailWord_1800640, baseEnd_1800640] using wordTrace_append hprefix tailTrace_1800640
  have hstable : (prefixWord ++ tailWord_1800640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800640).length < 2 ^ (prefixWord ++ tailWord_1800640).sum := by decide
  have hdescent : baseEnd_1800640 < baseStart_1800640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800661 : List Nat := [1, 3, 2, 3, 1, 2, 1, 5, 1, 4]
def baseStart_1800661 : Nat := 118140960795 + 1800661 * 2 ^ 59
def prefixEnd_1800661 : Nat := 4983230072969 + 3 ^ 40 * 1800661 * 2
def baseEnd_1800661 : Nat := 308201529601894879752139

theorem tailTrace_1800661 : CollatzResearch.WordTrace tailWord_1800661 prefixEnd_1800661 308201529601894879752139 := by
  unfold tailWord_1800661
  simp only [CollatzResearch.WordTrace]
  refine ⟨65675502129520200260321837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43783668086346800173547891 65675502129520200260321837)
  ·
    refine ⟨24628313298570075097620689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65675502129520200260321837 24628313298570075097620689)
    ·
      refine ⟨18471234973927556323215517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24628313298570075097620689 18471234973927556323215517)
      ·
        refine ⟨6926713115222833621205819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18471234973927556323215517 6926713115222833621205819)
        ·
          refine ⟨10390069672834250431808729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6926713115222833621205819 10390069672834250431808729)
          ·
            refine ⟨7792552254625687823856547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10390069672834250431808729 7792552254625687823856547)
            ·
              refine ⟨11688828381938531735784821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7792552254625687823856547 11688828381938531735784821)
              ·
                refine ⟨1095827660806737350229827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11688828381938531735784821 1095827660806737350229827)
                ·
                  refine ⟨1643741491210106025344741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1095827660806737350229827 1643741491210106025344741)
                  ·
                    refine ⟨308201529601894879752139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1643741491210106025344741 308201529601894879752139)
                    ·
                      rfl

theorem cell23_1800661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_1800661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800661 prefixEnd_1800661 := by exact prefixLift 1800661
  have htrace : WordTrace (prefixWord ++ tailWord_1800661) baseStart_1800661 baseEnd_1800661 := by
    simpa [prefixWord, tailWord_1800661, baseEnd_1800661] using wordTrace_append hprefix tailTrace_1800661
  have hstable : (prefixWord ++ tailWord_1800661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800661).length < 2 ^ (prefixWord ++ tailWord_1800661).sum := by decide
  have hdescent : baseEnd_1800661 < baseStart_1800661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800737 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_1800737 : Nat := 118140960795 + 1800737 * 2 ^ 59
def prefixEnd_1800737 : Nat := 4983230072969 + 3 ^ 40 * 1800737 * 2
def baseEnd_1800737 : Nat := 924643613335426341906067

theorem tailTrace_1800737 : CollatzResearch.WordTrace tailWord_1800737 prefixEnd_1800737 924643613335426341906067 := by
  unfold tailWord_1800737
  simp only [CollatzResearch.WordTrace]
  refine ⟨65678274077244865240088465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43785516051496576826725643 65678274077244865240088465)
  ·
    refine ⟨49258705557933648930066349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65678274077244865240088465 49258705557933648930066349)
    ·
      refine ⟨18472014584225118348774881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49258705557933648930066349 18472014584225118348774881)
      ·
        refine ⟨13854010938168838761581161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18472014584225118348774881 13854010938168838761581161)
        ·
          refine ⟨10390508203626629071185871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13854010938168838761581161 10390508203626629071185871)
          ·
            refine ⟨15585762305439943606778807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10390508203626629071185871 15585762305439943606778807)
            ·
              refine ⟨23378643458159915410168211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15585762305439943606778807 23378643458159915410168211)
              ·
                refine ⟨35067965187239873115252317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23378643458159915410168211 35067965187239873115252317)
                ·
                  refine ⟨13150486945214952418219619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35067965187239873115252317 13150486945214952418219619)
                  ·
                    refine ⟨19725730417822428627329429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13150486945214952418219619 19725730417822428627329429)
                    ·
                      refine ⟨924643613335426341906067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19725730417822428627329429 924643613335426341906067)
                      ·
                        rfl

theorem cell23_1800737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_1800737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800737 prefixEnd_1800737 := by exact prefixLift 1800737
  have htrace : WordTrace (prefixWord ++ tailWord_1800737) baseStart_1800737 baseEnd_1800737 := by
    simpa [prefixWord, tailWord_1800737, baseEnd_1800737] using wordTrace_append hprefix tailTrace_1800737
  have hstable : (prefixWord ++ tailWord_1800737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800737).length < 2 ^ (prefixWord ++ tailWord_1800737).sum := by decide
  have hdescent : baseEnd_1800737 < baseStart_1800737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800758 : List Nat := [5, 1, 2, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_1800758 : Nat := 118140960795 + 1800758 * 2 ^ 59
def prefixEnd_1800758 : Nat := 4983230072969 + 3 ^ 40 * 1800758 * 2
def baseEnd_1800758 : Nat := 924654396429170759743471

theorem tailTrace_1800758 : CollatzResearch.WordTrace tailWord_1800758 prefixEnd_1800758 924654396429170759743471 := by
  unfold tailWord_1800758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4104940000635549114162683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43786026673445857217735285 4104940000635549114162683)
  ·
    refine ⟨6157410000953323671244025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4104940000635549114162683 6157410000953323671244025)
    ·
      refine ⟨4618057500714992753433019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6157410000953323671244025 4618057500714992753433019)
      ·
        refine ⟨6927086251072489130149529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4618057500714992753433019 6927086251072489130149529)
        ·
          refine ⟨5195314688304366847612147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6927086251072489130149529 5195314688304366847612147)
          ·
            refine ⟨7792972032456550271418221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5195314688304366847612147 7792972032456550271418221)
            ·
              refine ⟨2922364512171206351781833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7792972032456550271418221 2922364512171206351781833)
              ·
                refine ⟨2191773384128404763836375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2922364512171206351781833 2191773384128404763836375)
                ·
                  refine ⟨3287660076192607145754563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2191773384128404763836375 3287660076192607145754563)
                  ·
                    refine ⟨4931490114288910718631845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3287660076192607145754563 4931490114288910718631845)
                    ·
                      refine ⟨924654396429170759743471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4931490114288910718631845 924654396429170759743471)
                      ·
                        rfl

theorem cell23_1800758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_1800758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800758 prefixEnd_1800758 := by exact prefixLift 1800758
  have htrace : WordTrace (prefixWord ++ tailWord_1800758) baseStart_1800758 baseEnd_1800758 := by
    simpa [prefixWord, tailWord_1800758, baseEnd_1800758] using wordTrace_append hprefix tailTrace_1800758
  have hstable : (prefixWord ++ tailWord_1800758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800758).length < 2 ^ (prefixWord ++ tailWord_1800758).sum := by decide
  have hdescent : baseEnd_1800758 < baseStart_1800758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800772 : List Nat := [2, 3, 5, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1800772 : Nat := 118140960795 + 1800772 * 2 ^ 59
def prefixEnd_1800772 : Nat := 4983230072969 + 3 ^ 40 * 1800772 * 2
def baseEnd_1800772 : Nat := 308220528386111234989469

theorem tailTrace_1800772 : CollatzResearch.WordTrace tailWord_1800772 prefixEnd_1800772 308220528386111234989469 := by
  unfold tailWord_1800772
  simp only [CollatzResearch.WordTrace]
  refine ⟨32839775316059033108806285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43786367088078710811741713 32839775316059033108806285)
  ·
    refine ⟨12314915743522137415802357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32839775316059033108806285 12314915743522137415802357)
    ·
      refine ⟨1154523350955200382731471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12314915743522137415802357 1154523350955200382731471)
      ·
        refine ⟨1731785026432800574097207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1154523350955200382731471 1731785026432800574097207)
        ·
          refine ⟨2597677539649200861145811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1731785026432800574097207 2597677539649200861145811)
          ·
            refine ⟨3896516309473801291718717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2597677539649200861145811 3896516309473801291718717)
            ·
              refine ⟨1461193616052675484394519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3896516309473801291718717 1461193616052675484394519)
              ·
                refine ⟨2191790424079013226591779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1461193616052675484394519 2191790424079013226591779)
                ·
                  refine ⟨3287685636118519839887669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2191790424079013226591779 3287685636118519839887669)
                  ·
                    refine ⟨308220528386111234989469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3287685636118519839887669 308220528386111234989469)
                    ·
                      rfl

theorem cell23_1800772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1800772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800772 prefixEnd_1800772 := by exact prefixLift 1800772
  have htrace : WordTrace (prefixWord ++ tailWord_1800772) baseStart_1800772 baseEnd_1800772 := by
    simpa [prefixWord, tailWord_1800772, baseEnd_1800772] using wordTrace_append hprefix tailTrace_1800772
  have hstable : (prefixWord ++ tailWord_1800772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800772).length < 2 ^ (prefixWord ++ tailWord_1800772).sum := by decide
  have hdescent : baseEnd_1800772 < baseStart_1800772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800778 : List Nat := [3, 1, 2, 1, 1, 5, 3, 1, 1, 2, 3]
def baseStart_1800778 : Nat := 118140960795 + 1800778 * 2 ^ 59
def prefixEnd_1800778 : Nat := 4983230072969 + 3 ^ 40 * 1800778 * 2
def baseEnd_1800778 : Nat := 924664666042260681493379

theorem tailTrace_1800778 : CollatzResearch.WordTrace tailWord_1800778 prefixEnd_1800778 924664666042260681493379 := by
  unfold tailWord_1800778
  simp only [CollatzResearch.WordTrace]
  refine ⟨16419942367524082310582747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43786512980064219494887325 16419942367524082310582747)
  ·
    refine ⟨24629913551286123465874121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16419942367524082310582747 24629913551286123465874121)
    ·
      refine ⟨18472435163464592599405591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24629913551286123465874121 18472435163464592599405591)
      ·
        refine ⟨27708652745196888899108387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18472435163464592599405591 27708652745196888899108387)
        ·
          refine ⟨41562979117795333348662581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27708652745196888899108387 41562979117795333348662581)
          ·
            refine ⟨3896529292293312501437117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41562979117795333348662581 3896529292293312501437117)
            ·
              refine ⟨1461198484609992188038919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3896529292293312501437117 1461198484609992188038919)
              ·
                refine ⟨2191797726914988282058379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1461198484609992188038919 2191797726914988282058379)
                ·
                  refine ⟨3287696590372482423087569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2191797726914988282058379 3287696590372482423087569)
                  ·
                    refine ⟨2465772442779361817315677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3287696590372482423087569 2465772442779361817315677)
                    ·
                      refine ⟨924664666042260681493379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2465772442779361817315677 924664666042260681493379)
                      ·
                        rfl

theorem cell23_1800778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_1800778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800778 prefixEnd_1800778 := by exact prefixLift 1800778
  have htrace : WordTrace (prefixWord ++ tailWord_1800778) baseStart_1800778 baseEnd_1800778 := by
    simpa [prefixWord, tailWord_1800778, baseEnd_1800778] using wordTrace_append hprefix tailTrace_1800778
  have hstable : (prefixWord ++ tailWord_1800778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800778).length < 2 ^ (prefixWord ++ tailWord_1800778).sum := by decide
  have hdescent : baseEnd_1800778 < baseStart_1800778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800801 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 3, 3, 2]
def baseStart_1800801 : Nat := 118140960795 + 1800801 * 2 ^ 59
def prefixEnd_1800801 : Nat := 4983230072969 + 3 ^ 40 * 1800801 * 2
def baseEnd_1800801 : Nat := 924676476097314091505773

theorem tailTrace_1800801 : CollatzResearch.WordTrace tailWord_1800801 prefixEnd_1800801 924676476097314091505773 := by
  unfold tailWord_1800801
  simp only [CollatzResearch.WordTrace]
  refine ⟨65680608349013004170418257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43787072232675336113612171 65680608349013004170418257)
  ·
    refine ⟨49260456261759753127813693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65680608349013004170418257 49260456261759753127813693)
    ·
      refine ⟨18472671098159907422930135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49260456261759753127813693 18472671098159907422930135)
      ·
        refine ⟨27709006647239861134395203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18472671098159907422930135 27709006647239861134395203)
        ·
          refine ⟨41563509970859791701592805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27709006647239861134395203 41563509970859791701592805)
          ·
            refine ⟨7793158119536210944048651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41563509970859791701592805 7793158119536210944048651)
            ·
              refine ⟨11689737179304316416072977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7793158119536210944048651 11689737179304316416072977)
              ·
                refine ⟨8767302884478237312054733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11689737179304316416072977 8767302884478237312054733)
                ·
                  refine ⟨3287738581679338992020525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8767302884478237312054733 3287738581679338992020525)
                  ·
                    refine ⟨1232901968129752122007697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3287738581679338992020525 1232901968129752122007697)
                    ·
                      refine ⟨924676476097314091505773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1232901968129752122007697 924676476097314091505773)
                      ·
                        rfl

theorem cell23_1800801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_1800801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800801 prefixEnd_1800801 := by exact prefixLift 1800801
  have htrace : WordTrace (prefixWord ++ tailWord_1800801) baseStart_1800801 baseEnd_1800801 := by
    simpa [prefixWord, tailWord_1800801, baseEnd_1800801] using wordTrace_append hprefix tailTrace_1800801
  have hstable : (prefixWord ++ tailWord_1800801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800801).length < 2 ^ (prefixWord ++ tailWord_1800801).sum := by decide
  have hdescent : baseEnd_1800801 < baseStart_1800801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800808 : List Nat := [2, 1, 4, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1800808 : Nat := 118140960795 + 1800808 * 2 ^ 59
def prefixEnd_1800808 : Nat := 4983230072969 + 3 ^ 40 * 1800808 * 2
def baseEnd_1800808 : Nat := 924680070461895564118241

theorem tailTrace_1800808 : CollatzResearch.WordTrace tailWord_1800808 prefixEnd_1800808 924680070461895564118241 := by
  unfold tailWord_1800808
  simp only [CollatzResearch.WordTrace]
  refine ⟨32840431829993822182961539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43787242439991762910615385 32840431829993822182961539)
  ·
    refine ⟨49260647744990733274442309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32840431829993822182961539 49260647744990733274442309)
    ·
      refine ⟨9236371452185762488957933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49260647744990733274442309 9236371452185762488957933)
      ·
        refine ⟨3463639294569660933359225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9236371452185762488957933 3463639294569660933359225)
        ·
          refine ⟨2597729470927245700019419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3463639294569660933359225 2597729470927245700019419)
          ·
            refine ⟨3896594206390868550029129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2597729470927245700019419 3896594206390868550029129)
            ·
              refine ⟨2922445654793151412521847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3896594206390868550029129 2922445654793151412521847)
              ·
                refine ⟨4383668482189727118782771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2922445654793151412521847 4383668482189727118782771)
                ·
                  refine ⟨6575502723284590678174157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4383668482189727118782771 6575502723284590678174157)
                  ·
                    refine ⟨2465813521231721504315309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6575502723284590678174157 2465813521231721504315309)
                    ·
                      refine ⟨924680070461895564118241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2465813521231721504315309 924680070461895564118241)
                      ·
                        rfl

theorem cell23_1800808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1800808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800808 prefixEnd_1800808 := by exact prefixLift 1800808
  have htrace : WordTrace (prefixWord ++ tailWord_1800808) baseStart_1800808 baseEnd_1800808 := by
    simpa [prefixWord, tailWord_1800808, baseEnd_1800808] using wordTrace_append hprefix tailTrace_1800808
  have hstable : (prefixWord ++ tailWord_1800808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800808).length < 2 ^ (prefixWord ++ tailWord_1800808).sum := by decide
  have hdescent : baseEnd_1800808 < baseStart_1800808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800842 : List Nat := [3, 1, 2, 3, 4, 1, 1, 2, 2, 1, 3]
def baseStart_1800842 : Nat := 118140960795 + 1800842 * 2 ^ 59
def prefixEnd_1800842 : Nat := 4983230072969 + 3 ^ 40 * 1800842 * 2
def baseEnd_1800842 : Nat := 924697528804148431093085

theorem tailTrace_1800842 : CollatzResearch.WordTrace tailWord_1800842 prefixEnd_1800842 924697528804148431093085 := by
  unfold tailWord_1800842
  simp only [CollatzResearch.WordTrace]
  refine ⟨16420525935466117043165195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43788069161242978781773853 16420525935466117043165195)
  ·
    refine ⟨24630788903199175564747793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16420525935466117043165195 24630788903199175564747793)
    ·
      refine ⟨18473091677399381673560845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24630788903199175564747793 18473091677399381673560845)
      ·
        refine ⟨6927409379024768127585317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18473091677399381673560845 6927409379024768127585317)
        ·
          refine ⟨1298889258567144023922247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6927409379024768127585317 1298889258567144023922247)
          ·
            refine ⟨1948333887850716035883371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298889258567144023922247 1948333887850716035883371)
            ·
              refine ⟨2922500831776074053825057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1948333887850716035883371 2922500831776074053825057)
              ·
                refine ⟨2191875623832055540368793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2922500831776074053825057 2191875623832055540368793)
                ·
                  refine ⟨1643906717874041655276595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2191875623832055540368793 1643906717874041655276595)
                  ·
                    refine ⟨2465860076811062482914893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1643906717874041655276595 2465860076811062482914893)
                    ·
                      refine ⟨924697528804148431093085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2465860076811062482914893 924697528804148431093085)
                      ·
                        rfl

theorem cell23_1800842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_1800842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800842 prefixEnd_1800842 := by exact prefixLift 1800842
  have htrace : WordTrace (prefixWord ++ tailWord_1800842) baseStart_1800842 baseEnd_1800842 := by
    simpa [prefixWord, tailWord_1800842, baseEnd_1800842] using wordTrace_append hprefix tailTrace_1800842
  have hstable : (prefixWord ++ tailWord_1800842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800842).length < 2 ^ (prefixWord ++ tailWord_1800842).sum := by decide
  have hdescent : baseEnd_1800842 < baseStart_1800842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800847 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 7]
def baseStart_1800847 : Nat := 118140960795 + 1800847 * 2 ^ 59
def prefixEnd_1800847 : Nat := 4983230072969 + 3 ^ 40 * 1800847 * 2
def baseEnd_1800847 : Nat := 924700096207420911530561

theorem tailTrace_1800847 : CollatzResearch.WordTrace tailWord_1800847 prefixEnd_1800847 924700096207420911530561 := by
  unfold tailWord_1800847
  simp only [CollatzResearch.WordTrace]
  refine ⟨65682286106846354026592795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43788190737897569351061863 65682286106846354026592795)
  ·
    refine ⟨98523429160269531039889193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65682286106846354026592795 98523429160269531039889193)
    ·
      refine ⟨73892571870202148279916895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98523429160269531039889193 73892571870202148279916895)
      ·
        refine ⟨110838857805303222419875343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73892571870202148279916895 110838857805303222419875343)
        ·
          refine ⟨166258286707954833629813015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110838857805303222419875343 166258286707954833629813015)
          ·
            refine ⟨249387430061932250444719523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166258286707954833629813015 249387430061932250444719523)
            ·
              refine ⟨374081145092898375667079285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249387430061932250444719523 374081145092898375667079285)
              ·
                refine ⟨35070107352459222718788683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 374081145092898375667079285 35070107352459222718788683)
                ·
                  refine ⟨52605161028688834078183025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35070107352459222718788683 52605161028688834078183025)
                  ·
                    refine ⟨39453870771516625558637269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52605161028688834078183025 39453870771516625558637269)
                    ·
                      refine ⟨924700096207420911530561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39453870771516625558637269 924700096207420911530561)
                      ·
                        rfl

theorem cell23_1800847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_1800847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800847 prefixEnd_1800847 := by exact prefixLift 1800847
  have htrace : WordTrace (prefixWord ++ tailWord_1800847) baseStart_1800847 baseEnd_1800847 := by
    simpa [prefixWord, tailWord_1800847, baseEnd_1800847] using wordTrace_append hprefix tailTrace_1800847
  have hstable : (prefixWord ++ tailWord_1800847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800847).length < 2 ^ (prefixWord ++ tailWord_1800847).sum := by decide
  have hdescent : baseEnd_1800847 < baseStart_1800847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800865 : List Nat := [1, 2, 3, 3, 3, 2, 1, 1, 1, 4, 2]
def baseStart_1800865 : Nat := 118140960795 + 1800865 * 2 ^ 59
def prefixEnd_1800865 : Nat := 4983230072969 + 3 ^ 40 * 1800865 * 2
def baseEnd_1800865 : Nat := 924709338859201841105479

theorem tailTrace_1800865 : CollatzResearch.WordTrace tailWord_1800865 prefixEnd_1800865 924709338859201841105479 := by
  unfold tailWord_1800865
  simp only [CollatzResearch.WordTrace]
  refine ⟨65682942620781143100748049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43788628413854095400498699 65682942620781143100748049)
  ·
    refine ⟨49262206965585857325561037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65682942620781143100748049 49262206965585857325561037)
    ·
      refine ⟨18473327612094696497085389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49262206965585857325561037 18473327612094696497085389)
      ·
        refine ⟨6927497854535511186407021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18473327612094696497085389 6927497854535511186407021)
        ·
          refine ⟨2597811695450816694902633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6927497854535511186407021 2597811695450816694902633)
          ·
            refine ⟨1948358771588112521176975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2597811695450816694902633 1948358771588112521176975)
            ·
              refine ⟨2922538157382168781765463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1948358771588112521176975 2922538157382168781765463)
              ·
                refine ⟨4383807236073253172648195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2922538157382168781765463 4383807236073253172648195)
                ·
                  refine ⟨6575710854109879758972293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4383807236073253172648195 6575710854109879758972293)
                  ·
                    refine ⟨1232945785145602454807305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6575710854109879758972293 1232945785145602454807305)
                    ·
                      refine ⟨924709338859201841105479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1232945785145602454807305 924709338859201841105479)
                      ·
                        rfl

theorem cell23_1800865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_1800865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800865 prefixEnd_1800865 := by exact prefixLift 1800865
  have htrace : WordTrace (prefixWord ++ tailWord_1800865) baseStart_1800865 baseEnd_1800865 := by
    simpa [prefixWord, tailWord_1800865, baseEnd_1800865] using wordTrace_append hprefix tailTrace_1800865
  have hstable : (prefixWord ++ tailWord_1800865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800865).length < 2 ^ (prefixWord ++ tailWord_1800865).sum := by decide
  have hdescent : baseEnd_1800865 < baseStart_1800865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800916 : List Nat := [2, 4, 1, 3, 3, 1, 2, 1, 2, 2, 2]
def baseStart_1800916 : Nat := 118140960795 + 1800916 * 2 ^ 59
def prefixEnd_1800916 : Nat := 4983230072969 + 3 ^ 40 * 1800916 * 2
def baseEnd_1800916 : Nat := 924735526372581141567745

theorem tailTrace_1800916 : CollatzResearch.WordTrace tailWord_1800916 prefixEnd_1800916 924735526372581141567745 := by
  unfold tailWord_1800916
  simp only [CollatzResearch.WordTrace]
  refine ⟨32842401371798189405427301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43789868495730919207236401 32842401371798189405427301)
  ·
    refine ⟨6157950257212160513517619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32842401371798189405427301 6157950257212160513517619)
    ·
      refine ⟨9236925385818240770276429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6157950257212160513517619 9236925385818240770276429)
      ·
        refine ⟨3463847019681840288853661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9236925385818240770276429 3463847019681840288853661)
        ·
          refine ⟨1298942632380690108320123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3463847019681840288853661 1298942632380690108320123)
          ·
            refine ⟨1948413948571035162480185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298942632380690108320123 1948413948571035162480185)
            ·
              refine ⟨1461310461428276371860139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1948413948571035162480185 1461310461428276371860139)
              ·
                refine ⟨2191965692142414557790209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1461310461428276371860139 2191965692142414557790209)
                ·
                  refine ⟨1643974269106810918342657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2191965692142414557790209 1643974269106810918342657)
                  ·
                    refine ⟨1232980701830108188756993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1643974269106810918342657 1232980701830108188756993)
                    ·
                      refine ⟨924735526372581141567745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1232980701830108188756993 924735526372581141567745)
                      ·
                        rfl

theorem cell23_1800916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_1800916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800916 prefixEnd_1800916 := by exact prefixLift 1800916
  have htrace : WordTrace (prefixWord ++ tailWord_1800916) baseStart_1800916 baseEnd_1800916 := by
    simpa [prefixWord, tailWord_1800916, baseEnd_1800916] using wordTrace_append hprefix tailTrace_1800916
  have hstable : (prefixWord ++ tailWord_1800916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800916).length < 2 ^ (prefixWord ++ tailWord_1800916).sum := by decide
  have hdescent : baseEnd_1800916 < baseStart_1800916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800921 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 1, 6, 2]
def baseStart_1800921 : Nat := 118140960795 + 1800921 * 2 ^ 59
def prefixEnd_1800921 : Nat := 4983230072969 + 3 ^ 40 * 1800921 * 2
def baseEnd_1800921 : Nat := 924738093775853622005221

theorem tailTrace_1800921 : CollatzResearch.WordTrace tailWord_1800921 prefixEnd_1800921 924738093775853622005221 := by
  unfold tailWord_1800921
  simp only [CollatzResearch.WordTrace]
  refine ⟨65684985108578264664786617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43789990072385509776524411 65684985108578264664786617)
  ·
    refine ⟨49263738831433698498589963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65684985108578264664786617 49263738831433698498589963)
    ·
      refine ⟨73895608247150547747884945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49263738831433698498589963 73895608247150547747884945)
      ·
        refine ⟨55421706185362910810913709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73895608247150547747884945 55421706185362910810913709)
        ·
          refine ⟨20783139819511091554092641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55421706185362910810913709 20783139819511091554092641)
          ·
            refine ⟨15587354864633318665569481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20783139819511091554092641 15587354864633318665569481)
            ·
              refine ⟨11690516148474988999177111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15587354864633318665569481 11690516148474988999177111)
              ·
                refine ⟨17535774222712483498765667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11690516148474988999177111 17535774222712483498765667)
                ·
                  refine ⟨26303661334068725248148501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17535774222712483498765667 26303661334068725248148501)
                  ·
                    refine ⟨1232984125034471496006961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26303661334068725248148501 1232984125034471496006961)
                    ·
                      refine ⟨924738093775853622005221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1232984125034471496006961 924738093775853622005221)
                      ·
                        rfl

theorem cell23_1800921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 6, 2].length) (baseStart_1800921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800921 prefixEnd_1800921 := by exact prefixLift 1800921
  have htrace : WordTrace (prefixWord ++ tailWord_1800921) baseStart_1800921 baseEnd_1800921 := by
    simpa [prefixWord, tailWord_1800921, baseEnd_1800921] using wordTrace_append hprefix tailTrace_1800921
  have hstable : (prefixWord ++ tailWord_1800921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800921).length < 2 ^ (prefixWord ++ tailWord_1800921).sum := by decide
  have hdescent : baseEnd_1800921 < baseStart_1800921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800984 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 1, 3, 7]
def baseStart_1800984 : Nat := 118140960795 + 1800984 * 2 ^ 59
def prefixEnd_1800984 : Nat := 4983230072969 + 3 ^ 40 * 1800984 * 2
def baseEnd_1800984 : Nat := 924770443057086875517431

theorem tailTrace_1800984 : CollatzResearch.WordTrace tailWord_1800984 prefixEnd_1800984 924770443057086875517431 := by
  unfold tailWord_1800984
  simp only [CollatzResearch.WordTrace]
  refine ⟨32843641453675013212165003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43791521938233350949553337 32843641453675013212165003)
  ·
    refine ⟨49265462180512519818247505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32843641453675013212165003 49265462180512519818247505)
    ·
      refine ⟨36949096635384389863685629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49265462180512519818247505 36949096635384389863685629)
      ·
        refine ⟨13855911238269146198882111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36949096635384389863685629 13855911238269146198882111)
        ·
          refine ⟨20783866857403719298323167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13855911238269146198882111 20783866857403719298323167)
          ·
            refine ⟨31175800286105578947484751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20783866857403719298323167 31175800286105578947484751)
            ·
              refine ⟨46763700429158368421227127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31175800286105578947484751 46763700429158368421227127)
              ·
                refine ⟨70145550643737552631840691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46763700429158368421227127 70145550643737552631840691)
                ·
                  refine ⟨105218325965606328947761037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70145550643737552631840691 105218325965606328947761037)
                  ·
                    refine ⟨39456872237102373355410389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105218325965606328947761037 39456872237102373355410389)
                    ·
                      refine ⟨924770443057086875517431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39456872237102373355410389 924770443057086875517431)
                      ·
                        rfl

theorem cell23_1800984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_1800984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800984 prefixEnd_1800984 := by exact prefixLift 1800984
  have htrace : WordTrace (prefixWord ++ tailWord_1800984) baseStart_1800984 baseEnd_1800984 := by
    simpa [prefixWord, tailWord_1800984, baseEnd_1800984] using wordTrace_append hprefix tailTrace_1800984
  have hstable : (prefixWord ++ tailWord_1800984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800984).length < 2 ^ (prefixWord ++ tailWord_1800984).sum := by decide
  have hdescent : baseEnd_1800984 < baseStart_1800984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800988 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_1800988 : Nat := 118140960795 + 1800988 * 2 ^ 59
def prefixEnd_1800988 : Nat := 4983230072969 + 3 ^ 40 * 1800988 * 2
def baseEnd_1800988 : Nat := 924772496979704859867413

theorem tailTrace_1800988 : CollatzResearch.WordTrace tailWord_1800988 prefixEnd_1800988 924772496979704859867413 := by
  unfold tailWord_1800988
  simp only [CollatzResearch.WordTrace]
  refine ⟨32843714399667767553737809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43791619199557023404983745 32843714399667767553737809)
  ·
    refine ⟨24632785799750825665303357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32843714399667767553737809 24632785799750825665303357)
    ·
      refine ⟨9237294674906559624488759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24632785799750825665303357 9237294674906559624488759)
      ·
        refine ⟨13855942012359839436733139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9237294674906559624488759 13855942012359839436733139)
        ·
          refine ⟨20783913018539759155099709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13855942012359839436733139 20783913018539759155099709)
          ·
            refine ⟨7793967381952409683162391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20783913018539759155099709 7793967381952409683162391)
            ·
              refine ⟨11690951072928614524743587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7793967381952409683162391 11690951072928614524743587)
              ·
                refine ⟨17536426609392921787115381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11690951072928614524743587 17536426609392921787115381)
                ·
                  refine ⟨1644039994630586417542067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17536426609392921787115381 1644039994630586417542067)
                  ·
                    refine ⟨2466059991945879626313101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1644039994630586417542067 2466059991945879626313101)
                    ·
                      refine ⟨924772496979704859867413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2466059991945879626313101 924772496979704859867413)
                      ·
                        rfl

theorem cell23_1800988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_1800988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800988 prefixEnd_1800988 := by exact prefixLift 1800988
  have htrace : WordTrace (prefixWord ++ tailWord_1800988) baseStart_1800988 baseEnd_1800988 := by
    simpa [prefixWord, tailWord_1800988, baseEnd_1800988] using wordTrace_append hprefix tailTrace_1800988
  have hstable : (prefixWord ++ tailWord_1800988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800988).length < 2 ^ (prefixWord ++ tailWord_1800988).sum := by decide
  have hdescent : baseEnd_1800988 < baseStart_1800988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800991 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 3, 5]
def baseStart_1800991 : Nat := 118140960795 + 1800991 * 2 ^ 59
def prefixEnd_1800991 : Nat := 4983230072969 + 3 ^ 40 * 1800991 * 2
def baseEnd_1800991 : Nat := 308258012473889449376633

theorem tailTrace_1800991 : CollatzResearch.WordTrace tailWord_1800991 prefixEnd_1800991 308258012473889449376633 := by
  unfold tailWord_1800991
  simp only [CollatzResearch.WordTrace]
  refine ⟨65687538218324666619834827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43791692145549777746556551 65687538218324666619834827)
  ·
    refine ⟨98531307327486999929752241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65687538218324666619834827 98531307327486999929752241)
    ·
      refine ⟨73898480495615249947314181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98531307327486999929752241 73898480495615249947314181)
      ·
        refine ⟨13855965092927859365121409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73898480495615249947314181 13855965092927859365121409)
        ·
          refine ⟨10391973819695894523841057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13855965092927859365121409 10391973819695894523841057)
          ·
            refine ⟨7793980364771920892880793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10391973819695894523841057 7793980364771920892880793)
            ·
              refine ⟨5845485273578940669660595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7793980364771920892880793 5845485273578940669660595)
              ·
                refine ⟨8768227910368411004490893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5845485273578940669660595 8768227910368411004490893)
                ·
                  refine ⟨3288085466388154126684085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8768227910368411004490893 3288085466388154126684085)
                  ·
                    refine ⟨308258012473889449376633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3288085466388154126684085 308258012473889449376633)
                    ·
                      rfl

theorem cell23_1800991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 5].length) (baseStart_1800991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1800991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1800991 prefixEnd_1800991 := by exact prefixLift 1800991
  have htrace : WordTrace (prefixWord ++ tailWord_1800991) baseStart_1800991 baseEnd_1800991 := by
    simpa [prefixWord, tailWord_1800991, baseEnd_1800991] using wordTrace_append hprefix tailTrace_1800991
  have hstable : (prefixWord ++ tailWord_1800991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800991).length < 2 ^ (prefixWord ++ tailWord_1800991).sum := by decide
  have hdescent : baseEnd_1800991 < baseStart_1800991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801012 : List Nat := [2, 5, 1, 1, 4, 1, 1, 2, 6]
def baseStart_1801012 : Nat := 118140960795 + 1801012 * 2 ^ 59
def prefixEnd_1801012 : Nat := 4983230072969 + 3 ^ 40 * 1801012 * 2
def baseEnd_1801012 : Nat := 102753868946156973996367

theorem tailTrace_1801012 : CollatzResearch.WordTrace tailWord_1801012 prefixEnd_1801012 102753868946156973996367 := by
  unfold tailWord_1801012
  simp only [CollatzResearch.WordTrace]
  refine ⟨32844152075624293603174645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43792202767499058137566193 32844152075624293603174645)
  ·
    refine ⟨3079139257089777525297623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32844152075624293603174645 3079139257089777525297623)
    ·
      refine ⟨4618708885634666287946435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3079139257089777525297623 4618708885634666287946435)
      ·
        refine ⟨6928063328451999431919653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4618708885634666287946435 6928063328451999431919653)
        ·
          refine ⟨1299011874084749893484935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6928063328451999431919653 1299011874084749893484935)
          ·
            refine ⟨1948517811127124840227403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1299011874084749893484935 1948517811127124840227403)
            ·
              refine ⟨2922776716690687260341105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1948517811127124840227403 2922776716690687260341105)
              ·
                refine ⟨2192082537518015445255829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2922776716690687260341105 2192082537518015445255829)
                ·
                  refine ⟨102753868946156973996367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2192082537518015445255829 102753868946156973996367)
                  ·
                    rfl

theorem cell23_1801012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_1801012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801012 prefixEnd_1801012 := by exact prefixLift 1801012
  have htrace : WordTrace (prefixWord ++ tailWord_1801012) baseStart_1801012 baseEnd_1801012 := by
    simpa [prefixWord, tailWord_1801012, baseEnd_1801012] using wordTrace_append hprefix tailTrace_1801012
  have hstable : (prefixWord ++ tailWord_1801012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801012).length < 2 ^ (prefixWord ++ tailWord_1801012).sum := by decide
  have hdescent : baseEnd_1801012 < baseStart_1801012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801022 : List Nat := [4, 2, 1, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_1801022 : Nat := 118140960795 + 1801022 * 2 ^ 59
def prefixEnd_1801022 : Nat := 4983230072969 + 3 ^ 40 * 1801022 * 2
def baseEnd_1801022 : Nat := 924789955321957726842257

theorem tailTrace_1801022 : CollatzResearch.WordTrace tailWord_1801022 prefixEnd_1801022 924789955321957726842257 := by
  unfold tailWord_1801022
  simp only [CollatzResearch.WordTrace]
  refine ⟨8211083610151544864276665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43792445920808239276142213 8211083610151544864276665)
  ·
    refine ⟨6158312707613658648207499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8211083610151544864276665 6158312707613658648207499)
    ·
      refine ⟨9237469061420487972311249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6158312707613658648207499 9237469061420487972311249)
      ·
        refine ⟨6928101796065365979233437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9237469061420487972311249 6928101796065365979233437)
        ·
          refine ⟨2598038173524512242212539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6928101796065365979233437 2598038173524512242212539)
          ·
            refine ⟨3897057260286768363318809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2598038173524512242212539 3897057260286768363318809)
            ·
              refine ⟨2922792945215076272489107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3897057260286768363318809 2922792945215076272489107)
              ·
                refine ⟨4384189417822614408733661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2922792945215076272489107 4384189417822614408733661)
                ·
                  refine ⟨1644071031683480403275123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4384189417822614408733661 1644071031683480403275123)
                  ·
                    refine ⟨2466106547525220604912685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1644071031683480403275123 2466106547525220604912685)
                    ·
                      refine ⟨924789955321957726842257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2466106547525220604912685 924789955321957726842257)
                      ·
                        rfl

theorem cell23_1801022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_1801022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801022 prefixEnd_1801022 := by exact prefixLift 1801022
  have htrace : WordTrace (prefixWord ++ tailWord_1801022) baseStart_1801022 baseEnd_1801022 := by
    simpa [prefixWord, tailWord_1801022, baseEnd_1801022] using wordTrace_append hprefix tailTrace_1801022
  have hstable : (prefixWord ++ tailWord_1801022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801022).length < 2 ^ (prefixWord ++ tailWord_1801022).sum := by decide
  have hdescent : baseEnd_1801022 < baseStart_1801022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801038 : List Nat := [4, 1, 1, 1, 1, 1, 1, 7, 2, 4]
def baseStart_1801038 : Nat := 118140960795 + 1801038 * 2 ^ 59
def prefixEnd_1801038 : Nat := 4983230072969 + 3 ^ 40 * 1801038 * 2
def baseEnd_1801038 : Nat := 308266057004143221414061

theorem tailTrace_1801038 : CollatzResearch.WordTrace tailWord_1801038 prefixEnd_1801038 308266057004143221414061 := by
  unfold tailWord_1801038
  simp only [CollatzResearch.WordTrace]
  refine ⟨8211156556144299205849471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43792834966102929097863845 8211156556144299205849471)
  ·
    refine ⟨12316734834216448808774207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8211156556144299205849471 12316734834216448808774207)
    ·
      refine ⟨18475102251324673213161311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12316734834216448808774207 18475102251324673213161311)
      ·
        refine ⟨27712653376987009819741967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18475102251324673213161311 27712653376987009819741967)
        ·
          refine ⟨41568980065480514729612951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27712653376987009819741967 41568980065480514729612951)
          ·
            refine ⟨62353470098220772094419427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41568980065480514729612951 62353470098220772094419427)
            ·
              refine ⟨93530205147331158141629141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62353470098220772094419427 93530205147331158141629141)
              ·
                refine ⟨2192114183140574018944433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 93530205147331158141629141 2192114183140574018944433)
                ·
                  refine ⟨1644085637355430514208325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2192114183140574018944433 1644085637355430514208325)
                  ·
                    refine ⟨308266057004143221414061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1644085637355430514208325 308266057004143221414061)
                    ·
                      rfl

theorem cell23_1801038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_1801038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801038 prefixEnd_1801038 := by exact prefixLift 1801038
  have htrace : WordTrace (prefixWord ++ tailWord_1801038) baseStart_1801038 baseEnd_1801038 := by
    simpa [prefixWord, tailWord_1801038, baseEnd_1801038] using wordTrace_append hprefix tailTrace_1801038
  have hstable : (prefixWord ++ tailWord_1801038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801038).length < 2 ^ (prefixWord ++ tailWord_1801038).sum := by decide
  have hdescent : baseEnd_1801038 < baseStart_1801038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801045 : List Nat := [1, 3, 2, 2, 2, 1, 1, 4, 3, 2, 2]
def baseStart_1801045 : Nat := 118140960795 + 1801045 * 2 ^ 59
def prefixEnd_1801045 : Nat := 4983230072969 + 3 ^ 40 * 1801045 * 2
def baseEnd_1801045 : Nat := 924801765377011136854651

theorem tailTrace_1801045 : CollatzResearch.WordTrace tailWord_1801045 prefixEnd_1801045 924801765377011136854651 := by
  unfold tailWord_1801045
  simp only [CollatzResearch.WordTrace]
  refine ⟨65689507760129033842300589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43793005173419355894867059 65689507760129033842300589)
  ·
    refine ⟨24633565410048387690862721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65689507760129033842300589 24633565410048387690862721)
    ·
      refine ⟨18475174057536290768147041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24633565410048387690862721 18475174057536290768147041)
      ·
        refine ⟨13856380543152218076110281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18475174057536290768147041 13856380543152218076110281)
        ·
          refine ⟨10392285407364163557082711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13856380543152218076110281 10392285407364163557082711)
          ·
            refine ⟨15588428111046245335624067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10392285407364163557082711 15588428111046245335624067)
            ·
              refine ⟨23382642166569368003436101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15588428111046245335624067 23382642166569368003436101)
              ·
                refine ⟨4384245406231756500644269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23382642166569368003436101 4384245406231756500644269)
                ·
                  refine ⟨1644092027336908687741601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4384245406231756500644269 1644092027336908687741601)
                  ·
                    refine ⟨1233069020502681515806201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1644092027336908687741601 1233069020502681515806201)
                    ·
                      refine ⟨924801765377011136854651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1233069020502681515806201 924801765377011136854651)
                      ·
                        rfl

theorem cell23_1801045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_1801045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801045 prefixEnd_1801045 := by exact prefixLift 1801045
  have htrace : WordTrace (prefixWord ++ tailWord_1801045) baseStart_1801045 baseEnd_1801045 := by
    simpa [prefixWord, tailWord_1801045, baseEnd_1801045] using wordTrace_append hprefix tailTrace_1801045
  have hstable : (prefixWord ++ tailWord_1801045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801045).length < 2 ^ (prefixWord ++ tailWord_1801045).sum := by decide
  have hdescent : baseEnd_1801045 < baseStart_1801045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801131 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 4]
def baseStart_1801131 : Nat := 118140960795 + 1801131 * 2 ^ 59
def prefixEnd_1801131 : Nat := 4983230072969 + 3 ^ 40 * 1801131 * 2
def baseEnd_1801131 : Nat := 924845924713297800379255

theorem tailTrace_1801131 : CollatzResearch.WordTrace tailWord_1801131 prefixEnd_1801131 924845924713297800379255 := by
  unfold tailWord_1801131
  simp only [CollatzResearch.WordTrace]
  refine ⟨65692644437817470529931247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43795096291878313686620831 65692644437817470529931247)
  ·
    refine ⟨98538966656726205794896871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65692644437817470529931247 98538966656726205794896871)
    ·
      refine ⟨147808449985089308692345307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98538966656726205794896871 147808449985089308692345307)
      ·
        refine ⟨221712674977633963038517961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147808449985089308692345307 221712674977633963038517961)
        ·
          refine ⟨166284506233225472278888471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221712674977633963038517961 166284506233225472278888471)
          ·
            refine ⟨249426759349838208418332707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166284506233225472278888471 249426759349838208418332707)
            ·
              refine ⟨374140139024757312627499061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249426759349838208418332707 374140139024757312627499061)
              ·
                refine ⟨35075638033570998058828037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 374140139024757312627499061 35075638033570998058828037)
                ·
                  refine ⟨6576682131294562136030257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35075638033570998058828037 6576682131294562136030257)
                  ·
                    refine ⟨4932511598470921602022693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6576682131294562136030257 4932511598470921602022693)
                    ·
                      refine ⟨924845924713297800379255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4932511598470921602022693 924845924713297800379255)
                      ·
                        rfl

theorem cell23_1801131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 4].length) (baseStart_1801131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801131 prefixEnd_1801131 := by exact prefixLift 1801131
  have htrace : WordTrace (prefixWord ++ tailWord_1801131) baseStart_1801131 baseEnd_1801131 := by
    simpa [prefixWord, tailWord_1801131, baseEnd_1801131] using wordTrace_append hprefix tailTrace_1801131
  have hstable : (prefixWord ++ tailWord_1801131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801131).length < 2 ^ (prefixWord ++ tailWord_1801131).sum := by decide
  have hdescent : baseEnd_1801131 < baseStart_1801131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801152 : List Nat := [2, 1, 1, 2, 3, 3, 2, 3, 2, 2, 2]
def baseStart_1801152 : Nat := 118140960795 + 1801152 * 2 ^ 59
def prefixEnd_1801152 : Nat := 4983230072969 + 3 ^ 40 * 1801152 * 2
def baseEnd_1801152 : Nat := 924856707807042218216659

theorem tailTrace_1801152 : CollatzResearch.WordTrace tailWord_1801152 prefixEnd_1801152 924856707807042218216659 := by
  unfold tailWord_1801152
  simp only [CollatzResearch.WordTrace]
  refine ⟨32846705185370695558222855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43795606913827594077630473 32846705185370695558222855)
  ·
    refine ⟨49270057778056043337334283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32846705185370695558222855 49270057778056043337334283)
    ·
      refine ⟨73905086667084065006001425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49270057778056043337334283 73905086667084065006001425)
      ·
        refine ⟨55428815000313048754501069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73905086667084065006001425 55428815000313048754501069)
        ·
          refine ⟨20785805625117393282937901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55428815000313048754501069 20785805625117393282937901)
          ·
            refine ⟨7794677109419022481101713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20785805625117393282937901 7794677109419022481101713)
            ·
              refine ⟨5846007832064266860826285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7794677109419022481101713 5846007832064266860826285)
              ·
                refine ⟨2192252937024100072809857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5846007832064266860826285 2192252937024100072809857)
                ·
                  refine ⟨1644189702768075054607393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2192252937024100072809857 1644189702768075054607393)
                  ·
                    refine ⟨1233142277076056290955545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1644189702768075054607393 1233142277076056290955545)
                    ·
                      refine ⟨924856707807042218216659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1233142277076056290955545 924856707807042218216659)
                      ·
                        rfl

theorem cell23_1801152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 2, 2, 2].length) (baseStart_1801152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801152 prefixEnd_1801152 := by exact prefixLift 1801152
  have htrace : WordTrace (prefixWord ++ tailWord_1801152) baseStart_1801152 baseEnd_1801152 := by
    simpa [prefixWord, tailWord_1801152, baseEnd_1801152] using wordTrace_append hprefix tailTrace_1801152
  have hstable : (prefixWord ++ tailWord_1801152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801152).length < 2 ^ (prefixWord ++ tailWord_1801152).sum := by decide
  have hdescent : baseEnd_1801152 < baseStart_1801152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801186 : List Nat := [3, 3, 3, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_1801186 : Nat := 118140960795 + 1801186 * 2 ^ 59
def prefixEnd_1801186 : Nat := 4983230072969 + 3 ^ 40 * 1801186 * 2
def baseEnd_1801186 : Nat := 924874166149295085191503

theorem tailTrace_1801186 : CollatzResearch.WordTrace tailWord_1801186 prefixEnd_1801186 924874166149295085191503 := by
  unfold tailWord_1801186
  simp only [CollatzResearch.WordTrace]
  refine ⟨16423662613154553730795853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43796433635078809948788941 16423662613154553730795853)
  ·
    refine ⟨6158873479932957649048445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16423662613154553730795853 6158873479932957649048445)
    ·
      refine ⟨2309577554974859118393167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6158873479932957649048445 2309577554974859118393167)
      ·
        refine ⟨3464366332462288677589751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2309577554974859118393167 3464366332462288677589751)
        ·
          refine ⟨5196549498693433016384627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3464366332462288677589751 5196549498693433016384627)
          ·
            refine ⟨7794824248040149524576941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5196549498693433016384627 7794824248040149524576941)
            ·
              refine ⟨2923059093015056071716353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7794824248040149524576941 2923059093015056071716353)
              ·
                refine ⟨2192294319761292053787265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2923059093015056071716353 2192294319761292053787265)
                ·
                  refine ⟨1644220739820969040340449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2192294319761292053787265 1644220739820969040340449)
                  ·
                    refine ⟨1233165554865726780255337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1644220739820969040340449 1233165554865726780255337)
                    ·
                      refine ⟨924874166149295085191503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1233165554865726780255337 924874166149295085191503)
                      ·
                        rfl

theorem cell23_1801186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_1801186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801186 prefixEnd_1801186 := by exact prefixLift 1801186
  have htrace : WordTrace (prefixWord ++ tailWord_1801186) baseStart_1801186 baseEnd_1801186 := by
    simpa [prefixWord, tailWord_1801186, baseEnd_1801186] using wordTrace_append hprefix tailTrace_1801186
  have hstable : (prefixWord ++ tailWord_1801186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801186).length < 2 ^ (prefixWord ++ tailWord_1801186).sum := by decide
  have hdescent : baseEnd_1801186 < baseStart_1801186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801252 : List Nat := [2, 3, 1, 4, 1, 1, 3, 1, 3, 4]
def baseStart_1801252 : Nat := 118140960795 + 1801252 * 2 ^ 59
def prefixEnd_1801252 : Nat := 4983230072969 + 3 ^ 40 * 1801252 * 2
def baseEnd_1801252 : Nat := 308302685290830608988733

theorem tailTrace_1801252 : CollatzResearch.WordTrace tailWord_1801252 prefixEnd_1801252 308302685290830608988733 := by
  unfold tailWord_1801252
  simp only [CollatzResearch.WordTrace]
  refine ⟨32848528835189554097543005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43798038446919405463390673 32848528835189554097543005)
  ·
    refine ⟨12318198313196082786578627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32848528835189554097543005 12318198313196082786578627)
    ·
      refine ⟨18477297469794124179867941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12318198313196082786578627 18477297469794124179867941)
      ·
        refine ⟨3464493275586398283725239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18477297469794124179867941 3464493275586398283725239)
        ·
          refine ⟨5196739913379597425587859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3464493275586398283725239 5196739913379597425587859)
          ·
            refine ⟨7795109870069396138381789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5196739913379597425587859 7795109870069396138381789)
            ·
              refine ⟨2923166201276023551893171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7795109870069396138381789 2923166201276023551893171)
              ·
                refine ⟨4384749301914035327839757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2923166201276023551893171 4384749301914035327839757)
                ·
                  refine ⟨1644280988217763247939909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4384749301914035327839757 1644280988217763247939909)
                  ·
                    refine ⟨308302685290830608988733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1644280988217763247939909 308302685290830608988733)
                    ·
                      rfl

theorem cell23_1801252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_1801252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801252 prefixEnd_1801252 := by exact prefixLift 1801252
  have htrace : WordTrace (prefixWord ++ tailWord_1801252) baseStart_1801252 baseEnd_1801252 := by
    simpa [prefixWord, tailWord_1801252, baseEnd_1801252] using wordTrace_append hprefix tailTrace_1801252
  have hstable : (prefixWord ++ tailWord_1801252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801252).length < 2 ^ (prefixWord ++ tailWord_1801252).sum := by decide
  have hdescent : baseEnd_1801252 < baseStart_1801252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801285 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 1, 5, 2]
def baseStart_1801285 : Nat := 118140960795 + 1801285 * 2 ^ 59
def prefixEnd_1801285 : Nat := 4983230072969 + 3 ^ 40 * 1801285 * 2
def baseEnd_1801285 : Nat := 924925000734090197853547

theorem tailTrace_1801285 : CollatzResearch.WordTrace tailWord_1801285 prefixEnd_1801285 924925000734090197853547 := by
  unfold tailWord_1801285
  simp only [CollatzResearch.WordTrace]
  refine ⟨65698261279259554831037309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43798840852839703220691539 65698261279259554831037309)
  ·
    refine ⟨24636847979722333061638991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65698261279259554831037309 24636847979722333061638991)
    ·
      refine ⟨36955271969583499592458487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24636847979722333061638991 36955271969583499592458487)
      ·
        refine ⟨55432907954375249388687731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36955271969583499592458487 55432907954375249388687731)
        ·
          refine ⟨83149361931562874083031597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55432907954375249388687731 83149361931562874083031597)
          ·
            refine ⟨31181010724336077781136849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83149361931562874083031597 31181010724336077781136849)
            ·
              refine ⟨23385758043252058335852637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31181010724336077781136849 23385758043252058335852637)
              ·
                refine ⟨8769659266219521875944739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23385758043252058335852637 8769659266219521875944739)
                ·
                  refine ⟨13154488899329282813917109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8769659266219521875944739 13154488899329282813917109)
                  ·
                    refine ⟨1233233334312120263804729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13154488899329282813917109 1233233334312120263804729)
                    ·
                      refine ⟨924925000734090197853547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1233233334312120263804729 924925000734090197853547)
                      ·
                        rfl

theorem cell23_1801285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 5, 2].length) (baseStart_1801285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801285 prefixEnd_1801285 := by exact prefixLift 1801285
  have htrace : WordTrace (prefixWord ++ tailWord_1801285) baseStart_1801285 baseEnd_1801285 := by
    simpa [prefixWord, tailWord_1801285, baseEnd_1801285] using wordTrace_append hprefix tailTrace_1801285
  have hstable : (prefixWord ++ tailWord_1801285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801285).length < 2 ^ (prefixWord ++ tailWord_1801285).sum := by decide
  have hdescent : baseEnd_1801285 < baseStart_1801285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801315 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 2, 6, 2]
def baseStart_1801315 : Nat := 118140960795 + 1801315 * 2 ^ 59
def prefixEnd_1801315 : Nat := 4983230072969 + 3 ^ 40 * 1801315 * 2
def baseEnd_1801315 : Nat := 924940405153725080478409

theorem tailTrace_1801315 : CollatzResearch.WordTrace tailWord_1801315 prefixEnd_1801315 924940405153725080478409 := by
  unfold tailWord_1801315
  simp only [CollatzResearch.WordTrace]
  refine ⟨65699355469150869954629399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43799570312767246636419599 65699355469150869954629399)
  ·
    refine ⟨98549033203726304931944099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65699355469150869954629399 98549033203726304931944099)
    ·
      refine ⟨147823549805589457397916149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98549033203726304931944099 147823549805589457397916149)
      ·
        refine ⟨13858457794274011631054639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147823549805589457397916149 13858457794274011631054639)
        ·
          refine ⟨20787686691411017446581959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13858457794274011631054639 20787686691411017446581959)
          ·
            refine ⟨31181530037116526169872939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20787686691411017446581959 31181530037116526169872939)
            ·
              refine ⟨46772295055674789254809409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31181530037116526169872939 46772295055674789254809409)
              ·
                refine ⟨35079221291756091941107057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46772295055674789254809409 35079221291756091941107057)
                ·
                  refine ⟨26309415968817068955830293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35079221291756091941107057 26309415968817068955830293)
                  ·
                    refine ⟨1233253873538300107304545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26309415968817068955830293 1233253873538300107304545)
                    ·
                      refine ⟨924940405153725080478409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1233253873538300107304545 924940405153725080478409)
                      ·
                        rfl

theorem cell23_1801315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_1801315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801315 prefixEnd_1801315 := by exact prefixLift 1801315
  have htrace : WordTrace (prefixWord ++ tailWord_1801315) baseStart_1801315 baseEnd_1801315 := by
    simpa [prefixWord, tailWord_1801315, baseEnd_1801315] using wordTrace_append hprefix tailTrace_1801315
  have hstable : (prefixWord ++ tailWord_1801315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801315).length < 2 ^ (prefixWord ++ tailWord_1801315).sum := by decide
  have hdescent : baseEnd_1801315 < baseStart_1801315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801325 : List Nat := [1, 5, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_1801325 : Nat := 118140960795 + 1801325 * 2 ^ 59
def prefixEnd_1801325 : Nat := 4983230072969 + 3 ^ 40 * 1801325 * 2
def baseEnd_1801325 : Nat := 308315179986756680451121

theorem tailTrace_1801325 : CollatzResearch.WordTrace tailWord_1801325 prefixEnd_1801325 308315179986756680451121 := by
  unfold tailWord_1801325
  simp only [CollatzResearch.WordTrace]
  refine ⟨65699720199114641662493429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43799813466076427774995619 65699720199114641662493429)
  ·
    refine ⟨6159348768666997655858759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65699720199114641662493429 6159348768666997655858759)
    ·
      refine ⟨9239023153000496483788139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6159348768666997655858759 9239023153000496483788139)
      ·
        refine ⟨13858534729500744725682209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9239023153000496483788139 13858534729500744725682209)
        ·
          refine ⟨10393901047125558544261657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13858534729500744725682209 10393901047125558544261657)
          ·
            refine ⟨7795425785344168908196243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10393901047125558544261657 7795425785344168908196243)
            ·
              refine ⟨11693138678016253362294365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7795425785344168908196243 11693138678016253362294365)
              ·
                refine ⟨4384927004256095010860387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11693138678016253362294365 4384927004256095010860387)
                ·
                  refine ⟨6577390506384142516290581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4384927004256095010860387 6577390506384142516290581)
                  ·
                    refine ⟨308315179986756680451121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6577390506384142516290581 308315179986756680451121)
                    ·
                      rfl

theorem cell23_1801325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_1801325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801325 prefixEnd_1801325 := by exact prefixLift 1801325
  have htrace : WordTrace (prefixWord ++ tailWord_1801325) baseStart_1801325 baseEnd_1801325 := by
    simpa [prefixWord, tailWord_1801325, baseEnd_1801325] using wordTrace_append hprefix tailTrace_1801325
  have hstable : (prefixWord ++ tailWord_1801325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801325).length < 2 ^ (prefixWord ++ tailWord_1801325).sum := by decide
  have hdescent : baseEnd_1801325 < baseStart_1801325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801335 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 3]
def baseStart_1801335 : Nat := 118140960795 + 1801335 * 2 ^ 59
def prefixEnd_1801335 : Nat := 4983230072969 + 3 ^ 40 * 1801335 * 2
def baseEnd_1801335 : Nat := 924950674766815002228317

theorem tailTrace_1801335 : CollatzResearch.WordTrace tailWord_1801335 prefixEnd_1801335 924950674766815002228317 := by
  unfold tailWord_1801335
  simp only [CollatzResearch.WordTrace]
  refine ⟨65700084929078413370357459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43800056619385608913571639 65700084929078413370357459)
  ·
    refine ⟨98550127393617620055536189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65700084929078413370357459 98550127393617620055536189)
    ·
      refine ⟨36956297772606607520826071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98550127393617620055536189 36956297772606607520826071)
      ·
        refine ⟨55434446658909911281239107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36956297772606607520826071 55434446658909911281239107)
        ·
          refine ⟨83151669988364866921858661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55434446658909911281239107 83151669988364866921858661)
          ·
            refine ⟨15590938122818412547848499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83151669988364866921858661 15590938122818412547848499)
            ·
              refine ⟨23386407184227618821772749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15590938122818412547848499 23386407184227618821772749)
              ·
                refine ⟨8769902694085357058164781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23386407184227618821772749 8769902694085357058164781)
                ·
                  refine ⟨3288713510282008896811793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8769902694085357058164781 3288713510282008896811793)
                  ·
                    refine ⟨2466535132711506672608845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3288713510282008896811793 2466535132711506672608845)
                    ·
                      refine ⟨924950674766815002228317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2466535132711506672608845 924950674766815002228317)
                      ·
                        rfl

theorem cell23_1801335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_1801335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801335 prefixEnd_1801335 := by exact prefixLift 1801335
  have htrace : WordTrace (prefixWord ++ tailWord_1801335) baseStart_1801335 baseEnd_1801335 := by
    simpa [prefixWord, tailWord_1801335, baseEnd_1801335] using wordTrace_append hprefix tailTrace_1801335
  have hstable : (prefixWord ++ tailWord_1801335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801335).length < 2 ^ (prefixWord ++ tailWord_1801335).sum := by decide
  have hdescent : baseEnd_1801335 < baseStart_1801335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801386 : List Nat := [3, 1, 5, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_1801386 : Nat := 118140960795 + 1801386 * 2 ^ 59
def prefixEnd_1801386 : Nat := 4983230072969 + 3 ^ 40 * 1801386 * 2
def baseEnd_1801386 : Nat := 924976862280194302690583

theorem tailTrace_1801386 : CollatzResearch.WordTrace tailWord_1801386 prefixEnd_1801386 924976862280194302690583 := by
  unfold tailWord_1801386
  simp only [CollatzResearch.WordTrace]
  refine ⟨16425486262973412270116003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43801296701262432720309341 16425486262973412270116003)
  ·
    refine ⟨24638229394460118405174005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16425486262973412270116003 24638229394460118405174005)
    ·
      refine ⟨2309834005730636100485063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24638229394460118405174005 2309834005730636100485063)
      ·
        refine ⟨3464751008595954150727595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2309834005730636100485063 3464751008595954150727595)
        ·
          refine ⟨5197126512893931226091393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3464751008595954150727595 5197126512893931226091393)
          ·
            refine ⟨3897844884670448419568545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5197126512893931226091393 3897844884670448419568545)
            ·
              refine ⟨2923383663502836314676409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3897844884670448419568545 2923383663502836314676409)
              ·
                refine ⟨2192537747627127236007307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2923383663502836314676409 2192537747627127236007307)
                ·
                  refine ⟨3288806621440690854010961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2192537747627127236007307 3288806621440690854010961)
                  ·
                    refine ⟨2466604966080518140508221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3288806621440690854010961 2466604966080518140508221)
                    ·
                      refine ⟨924976862280194302690583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2466604966080518140508221 924976862280194302690583)
                      ·
                        rfl

theorem cell23_1801386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_1801386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801386 prefixEnd_1801386 := by exact prefixLift 1801386
  have htrace : WordTrace (prefixWord ++ tailWord_1801386) baseStart_1801386 baseEnd_1801386 := by
    simpa [prefixWord, tailWord_1801386, baseEnd_1801386] using wordTrace_append hprefix tailTrace_1801386
  have hstable : (prefixWord ++ tailWord_1801386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801386).length < 2 ^ (prefixWord ++ tailWord_1801386).sum := by decide
  have hdescent : baseEnd_1801386 < baseStart_1801386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801388 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 8]
def baseStart_1801388 : Nat := 118140960795 + 1801388 * 2 ^ 59
def prefixEnd_1801388 : Nat := 4983230072969 + 3 ^ 40 * 1801388 * 2
def baseEnd_1801388 : Nat := 924977889241503294865573

theorem tailTrace_1801388 : CollatzResearch.WordTrace tailWord_1801388 prefixEnd_1801388 924977889241503294865573 := by
  unfold tailWord_1801388
  simp only [CollatzResearch.WordTrace]
  refine ⟨32851008998943201711018409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43801345331924268948024545 32851008998943201711018409)
  ·
    refine ⟨24638256749207401283263807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32851008998943201711018409 24638256749207401283263807)
    ·
      refine ⟨36957385123811101924895711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24638256749207401283263807 36957385123811101924895711)
      ·
        refine ⟨55436077685716652887343567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36957385123811101924895711 55436077685716652887343567)
        ·
          refine ⟨83154116528574979331015351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55436077685716652887343567 83154116528574979331015351)
          ·
            refine ⟨124731174792862468996523027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83154116528574979331015351 124731174792862468996523027)
            ·
              refine ⟨187096762189293703494784541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124731174792862468996523027 187096762189293703494784541)
              ·
                refine ⟨70161285820985138810544203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187096762189293703494784541 70161285820985138810544203)
                ·
                  refine ⟨105241928731477708215816305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70161285820985138810544203 105241928731477708215816305)
                  ·
                    refine ⟨78931446548608281161862229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105241928731477708215816305 78931446548608281161862229)
                    ·
                      refine ⟨924977889241503294865573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 78931446548608281161862229 924977889241503294865573)
                      ·
                        rfl

theorem cell23_1801388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_1801388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801388 prefixEnd_1801388 := by exact prefixLift 1801388
  have htrace : WordTrace (prefixWord ++ tailWord_1801388) baseStart_1801388 baseEnd_1801388 := by
    simpa [prefixWord, tailWord_1801388, baseEnd_1801388] using wordTrace_append hprefix tailTrace_1801388
  have hstable : (prefixWord ++ tailWord_1801388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801388).length < 2 ^ (prefixWord ++ tailWord_1801388).sum := by decide
  have hdescent : baseEnd_1801388 < baseStart_1801388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801389 : List Nat := [1, 5, 2, 1, 3, 2, 2, 7]
def baseStart_1801389 : Nat := 118140960795 + 1801389 * 2 ^ 59
def prefixEnd_1801389 : Nat := 4983230072969 + 3 ^ 40 * 1801389 * 2
def baseEnd_1801389 : Nat := 34258459360079918183447

theorem tailTrace_1801389 : CollatzResearch.WordTrace tailWord_1801389 prefixEnd_1801389 34258459360079918183447 := by
  unfold tailWord_1801389
  simp only [CollatzResearch.WordTrace]
  refine ⟨65702054470882780592823221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43801369647255187061882147 65702054470882780592823221)
  ·
    refine ⟨6159567606645260680577177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65702054470882780592823221 6159567606645260680577177)
    ·
      refine ⟨4619675704983945510432883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6159567606645260680577177 4619675704983945510432883)
      ·
        refine ⟨6929513557475918265649325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4619675704983945510432883 6929513557475918265649325)
        ·
          refine ⟨2598567584053469349618497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6929513557475918265649325 2598567584053469349618497)
          ·
            refine ⟨1948925688040102012213873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2598567584053469349618497 1948925688040102012213873)
            ·
              refine ⟨1461694266030076509160405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1948925688040102012213873 1461694266030076509160405)
              ·
                refine ⟨34258459360079918183447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1461694266030076509160405 34258459360079918183447)
                ·
                  rfl

theorem cell23_1801389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 7].length) (baseStart_1801389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801389 prefixEnd_1801389 := by exact prefixLift 1801389
  have htrace : WordTrace (prefixWord ++ tailWord_1801389) baseStart_1801389 baseEnd_1801389 := by
    simpa [prefixWord, tailWord_1801389, baseEnd_1801389] using wordTrace_append hprefix tailTrace_1801389
  have hstable : (prefixWord ++ tailWord_1801389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801389).length < 2 ^ (prefixWord ++ tailWord_1801389).sum := by decide
  have hdescent : baseEnd_1801389 < baseStart_1801389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801425 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 2, 4, 3]
def baseStart_1801425 : Nat := 118140960795 + 1801425 * 2 ^ 59
def prefixEnd_1801425 : Nat := 4983230072969 + 3 ^ 40 * 1801425 * 2
def baseEnd_1801425 : Nat := 924996888025719650102903

theorem tailTrace_1801425 : CollatzResearch.WordTrace tailWord_1801425 prefixEnd_1801425 924996888025719650102903 := by
  unfold tailWord_1801425
  simp only [CollatzResearch.WordTrace]
  refine ⟨65703367498752358741133729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43802244999168239160755819 65703367498752358741133729)
  ·
    refine ⟨49277525624064269055850297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65703367498752358741133729 49277525624064269055850297)
    ·
      refine ⟨36958144218048201791887723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49277525624064269055850297 36958144218048201791887723)
      ·
        refine ⟨55437216327072302687831585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36958144218048201791887723 55437216327072302687831585)
        ·
          refine ⟨41577912245304227015873689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55437216327072302687831585 41577912245304227015873689)
          ·
            refine ⟨31183434183978170261905267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41577912245304227015873689 31183434183978170261905267)
            ·
              refine ⟨46775151275967255392857901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31183434183978170261905267 46775151275967255392857901)
              ·
                refine ⟨17540681728487720772321713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46775151275967255392857901 17540681728487720772321713)
                ·
                  refine ⟨13155511296365790579241285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17540681728487720772321713 13155511296365790579241285)
                  ·
                    refine ⟨2466658368068585733607741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13155511296365790579241285 2466658368068585733607741)
                    ·
                      refine ⟨924996888025719650102903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2466658368068585733607741 924996888025719650102903)
                      ·
                        rfl

theorem cell23_1801425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_1801425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801425 prefixEnd_1801425 := by exact prefixLift 1801425
  have htrace : WordTrace (prefixWord ++ tailWord_1801425) baseStart_1801425 baseEnd_1801425 := by
    simpa [prefixWord, tailWord_1801425, baseEnd_1801425] using wordTrace_append hprefix tailTrace_1801425
  have hstable : (prefixWord ++ tailWord_1801425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801425).length < 2 ^ (prefixWord ++ tailWord_1801425).sum := by decide
  have hdescent : baseEnd_1801425 < baseStart_1801425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801509 : List Nat := [1, 3, 1, 2, 4, 3, 1, 1, 2, 5]
def baseStart_1801509 : Nat := 118140960795 + 1801509 * 2 ^ 59
def prefixEnd_1801509 : Nat := 4983230072969 + 3 ^ 40 * 1801509 * 2
def baseEnd_1801509 : Nat := 308346673466899107150839

theorem tailTrace_1801509 : CollatzResearch.WordTrace tailWord_1801509 prefixEnd_1801509 308346673466899107150839 := by
  unfold tailWord_1801509
  simp only [CollatzResearch.WordTrace]
  refine ⟨65706431230448041087191581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43804287486965360724794387 65706431230448041087191581)
  ·
    refine ⟨24639911711418015407696843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65706431230448041087191581 24639911711418015407696843)
    ·
      refine ⟨36959867567127023111545265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24639911711418015407696843 36959867567127023111545265)
      ·
        refine ⟨27719900675345267333658949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36959867567127023111545265 27719900675345267333658949)
        ·
          refine ⟨5197481376627237625061053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27719900675345267333658949 5197481376627237625061053)
          ·
            refine ⟨1949055516235214109397895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5197481376627237625061053 1949055516235214109397895)
            ·
              refine ⟨2923583274352821164096843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1949055516235214109397895 2923583274352821164096843)
              ·
                refine ⟨4385374911529231746145265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2923583274352821164096843 4385374911529231746145265)
                ·
                  refine ⟨3289031183646923809608949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4385374911529231746145265 3289031183646923809608949)
                  ·
                    refine ⟨308346673466899107150839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3289031183646923809608949 308346673466899107150839)
                    ·
                      rfl

theorem cell23_1801509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_1801509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801509 prefixEnd_1801509 := by exact prefixLift 1801509
  have htrace : WordTrace (prefixWord ++ tailWord_1801509) baseStart_1801509 baseEnd_1801509 := by
    simpa [prefixWord, tailWord_1801509, baseEnd_1801509] using wordTrace_append hprefix tailTrace_1801509
  have hstable : (prefixWord ++ tailWord_1801509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801509).length < 2 ^ (prefixWord ++ tailWord_1801509).sum := by decide
  have hdescent : baseEnd_1801509 < baseStart_1801509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801555 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 6]
def baseStart_1801555 : Nat := 118140960795 + 1801555 * 2 ^ 59
def prefixEnd_1801555 : Nat := 4983230072969 + 3 ^ 40 * 1801555 * 2
def baseEnd_1801555 : Nat := 925063640510804141477305

theorem tailTrace_1801555 : CollatzResearch.WordTrace tailWord_1801555 prefixEnd_1801555 925063640510804141477305 := by
  unfold tailWord_1801555
  simp only [CollatzResearch.WordTrace]
  refine ⟨65708108988281390943366119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43805405992187593962244079 65708108988281390943366119)
  ·
    refine ⟨98562163482422086415049179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65708108988281390943366119 98562163482422086415049179)
    ·
      refine ⟨147843245223633129622573769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98562163482422086415049179 147843245223633129622573769)
      ·
        refine ⟨110882433917724847216930327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147843245223633129622573769 110882433917724847216930327)
        ·
          refine ⟨166323650876587270825395491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110882433917724847216930327 166323650876587270825395491)
          ·
            refine ⟨249485476314880906238093237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166323650876587270825395491 249485476314880906238093237)
            ·
              refine ⟨23389263404520084959821241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 249485476314880906238093237 23389263404520084959821241)
              ·
                refine ⟨17541947553390063719865931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23389263404520084959821241 17541947553390063719865931)
                ·
                  refine ⟨26312921330085095579798897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17541947553390063719865931 26312921330085095579798897)
                  ·
                    refine ⟨19734690997563821684849173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26312921330085095579798897 19734690997563821684849173)
                    ·
                      refine ⟨925063640510804141477305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19734690997563821684849173 925063640510804141477305)
                      ·
                        rfl

theorem cell23_1801555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_1801555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801555 prefixEnd_1801555 := by exact prefixLift 1801555
  have htrace : WordTrace (prefixWord ++ tailWord_1801555) baseStart_1801555 baseEnd_1801555 := by
    simpa [prefixWord, tailWord_1801555, baseEnd_1801555] using wordTrace_append hprefix tailTrace_1801555
  have hstable : (prefixWord ++ tailWord_1801555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801555).length < 2 ^ (prefixWord ++ tailWord_1801555).sum := by decide
  have hdescent : baseEnd_1801555 < baseStart_1801555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801612 : List Nat := [2, 2, 1, 2, 1, 3, 2, 3, 1, 6]
def baseStart_1801612 : Nat := 118140960795 + 1801612 * 2 ^ 59
def prefixEnd_1801612 : Nat := 4983230072969 + 3 ^ 40 * 1801612 * 2
def baseEnd_1801612 : Nat := 308364302969370139488181

theorem tailTrace_1801612 : CollatzResearch.WordTrace tailWord_1801612 prefixEnd_1801612 308364302969370139488181 := by
  unfold tailWord_1801612
  simp only [CollatzResearch.WordTrace]
  refine ⟨32855093974537444839095545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43806791966049926452127393 32855093974537444839095545)
  ·
    refine ⟨24641320480903083629321659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32855093974537444839095545 24641320480903083629321659)
    ·
      refine ⟨36961980721354625443982489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24641320480903083629321659 36961980721354625443982489)
      ·
        refine ⟨27721485541015969082986867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36961980721354625443982489 27721485541015969082986867)
        ·
          refine ⟨41582228311523953624480301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27721485541015969082986867 41582228311523953624480301)
          ·
            refine ⟨15593335616821482609180113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41582228311523953624480301 15593335616821482609180113)
            ·
              refine ⟨11695001712616111956885085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15593335616821482609180113 11695001712616111956885085)
              ·
                refine ⟨4385625642231041983831907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11695001712616111956885085 4385625642231041983831907)
                ·
                  refine ⟨6578438463346562975747861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4385625642231041983831907 6578438463346562975747861)
                  ·
                    refine ⟨308364302969370139488181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6578438463346562975747861 308364302969370139488181)
                    ·
                      rfl

theorem cell23_1801612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_1801612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801612 prefixEnd_1801612 := by exact prefixLift 1801612
  have htrace : WordTrace (prefixWord ++ tailWord_1801612) baseStart_1801612 baseEnd_1801612 := by
    simpa [prefixWord, tailWord_1801612, baseEnd_1801612] using wordTrace_append hprefix tailTrace_1801612
  have hstable : (prefixWord ++ tailWord_1801612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801612).length < 2 ^ (prefixWord ++ tailWord_1801612).sum := by decide
  have hdescent : baseEnd_1801612 < baseStart_1801612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801629 : List Nat := [1, 4, 2, 1, 3, 2, 1, 2, 1, 6]
def baseStart_1801629 : Nat := 118140960795 + 1801629 * 2 ^ 59
def prefixEnd_1801629 : Nat := 4983230072969 + 3 ^ 40 * 1801629 * 2
def baseEnd_1801629 : Nat := 308367212693078950650655

theorem tailTrace_1801629 : CollatzResearch.WordTrace tailWord_1801629 prefixEnd_1801629 308367212693078950650655 := by
  unfold tailWord_1801629
  simp only [CollatzResearch.WordTrace]
  refine ⟨65710807990013301581559941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43807205326675534387706627 65710807990013301581559941)
  ·
    refine ⟨12320776498127494046542489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65710807990013301581559941 12320776498127494046542489)
    ·
      refine ⟨9240582373595620534906867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12320776498127494046542489 9240582373595620534906867)
      ·
        refine ⟨13860873560393430802360301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9240582373595620534906867 13860873560393430802360301)
        ·
          refine ⟨5197827585147536550885113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13860873560393430802360301 5197827585147536550885113)
          ·
            refine ⟨3898370688860652413163835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5197827585147536550885113 3898370688860652413163835)
            ·
              refine ⟨5847556033290978619745753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3898370688860652413163835 5847556033290978619745753)
              ·
                refine ⟨4385667024968233964809315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5847556033290978619745753 4385667024968233964809315)
                ·
                  refine ⟨6578500537452350947213973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4385667024968233964809315 6578500537452350947213973)
                  ·
                    refine ⟨308367212693078950650655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6578500537452350947213973 308367212693078950650655)
                    ·
                      rfl

theorem cell23_1801629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_1801629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801629 prefixEnd_1801629 := by exact prefixLift 1801629
  have htrace : WordTrace (prefixWord ++ tailWord_1801629) baseStart_1801629 baseEnd_1801629 := by
    simpa [prefixWord, tailWord_1801629, baseEnd_1801629] using wordTrace_append hprefix tailTrace_1801629
  have hstable : (prefixWord ++ tailWord_1801629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801629).length < 2 ^ (prefixWord ++ tailWord_1801629).sum := by decide
  have hdescent : baseEnd_1801629 < baseStart_1801629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801672 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 2, 7]
def baseStart_1801672 : Nat := 118140960795 + 1801672 * 2 ^ 59
def prefixEnd_1801672 : Nat := 4983230072969 + 3 ^ 40 * 1801672 * 2
def baseEnd_1801672 : Nat := 308374572582460061238089

theorem tailTrace_1801672 : CollatzResearch.WordTrace tailWord_1801672 prefixEnd_1801672 308374572582460061238089 := by
  unfold tailWord_1801672
  simp only [CollatzResearch.WordTrace]
  refine ⟨32856188164428759962687635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43808250885905013283583513 32856188164428759962687635)
  ·
    refine ⟨49284282246643139944031453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32856188164428759962687635 49284282246643139944031453)
    ·
      refine ⟨18481605842491177479011795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49284282246643139944031453 18481605842491177479011795)
      ·
        refine ⟨27722408763736766218517693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18481605842491177479011795 27722408763736766218517693)
        ·
          refine ⟨10395903286401287331944135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27722408763736766218517693 10395903286401287331944135)
          ·
            refine ⟨15593854929601930997916203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10395903286401287331944135 15593854929601930997916203)
            ·
              refine ⟨23390782394402896496874305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15593854929601930997916203 23390782394402896496874305)
              ·
                refine ⟨17543086795802172372655729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23390782394402896496874305 17543086795802172372655729)
                ·
                  refine ⟨13157315096851629279491797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17543086795802172372655729 13157315096851629279491797)
                  ·
                    refine ⟨308374572582460061238089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13157315096851629279491797 308374572582460061238089)
                    ·
                      rfl

theorem cell23_1801672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_1801672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801672 prefixEnd_1801672 := by exact prefixLift 1801672
  have htrace : WordTrace (prefixWord ++ tailWord_1801672) baseStart_1801672 baseEnd_1801672 := by
    simpa [prefixWord, tailWord_1801672, baseEnd_1801672] using wordTrace_append hprefix tailTrace_1801672
  have hstable : (prefixWord ++ tailWord_1801672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801672).length < 2 ^ (prefixWord ++ tailWord_1801672).sum := by decide
  have hdescent : baseEnd_1801672 < baseStart_1801672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801703 : List Nat := [1, 1, 5, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_1801703 : Nat := 118140960795 + 1801703 * 2 ^ 59
def prefixEnd_1801703 : Nat := 4983230072969 + 3 ^ 40 * 1801703 * 2
def baseEnd_1801703 : Nat := 925139635647669562426625

theorem tailTrace_1801703 : CollatzResearch.WordTrace tailWord_1801703 prefixEnd_1801703 925139635647669562426625 := by
  unfold tailWord_1801703
  simp only [CollatzResearch.WordTrace]
  refine ⟨65713506991745212219753763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43809004661163474813169175 65713506991745212219753763)
  ·
    refine ⟨98570260487617818329630645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65713506991745212219753763 98570260487617818329630645)
    ·
      refine ⟨9240961920714170468402873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98570260487617818329630645 9240961920714170468402873)
      ·
        refine ⟨6930721440535627851302155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9240961920714170468402873 6930721440535627851302155)
        ·
          refine ⟨10396082160803441776953233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6930721440535627851302155 10396082160803441776953233)
          ·
            refine ⟨7797061620602581332714925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10396082160803441776953233 7797061620602581332714925)
            ·
              refine ⟨2923898107725967999768097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7797061620602581332714925 2923898107725967999768097)
              ·
                refine ⟨2192923580794475999826073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2923898107725967999768097 2192923580794475999826073)
                ·
                  refine ⟨1644692685595856999869555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2192923580794475999826073 1644692685595856999869555)
                  ·
                    refine ⟨2467039028393785499804333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1644692685595856999869555 2467039028393785499804333)
                    ·
                      refine ⟨925139635647669562426625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2467039028393785499804333 925139635647669562426625)
                      ·
                        rfl

theorem cell23_1801703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_1801703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801703 prefixEnd_1801703 := by exact prefixLift 1801703
  have htrace : WordTrace (prefixWord ++ tailWord_1801703) baseStart_1801703 baseEnd_1801703 := by
    simpa [prefixWord, tailWord_1801703, baseEnd_1801703] using wordTrace_append hprefix tailTrace_1801703
  have hstable : (prefixWord ++ tailWord_1801703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801703).length < 2 ^ (prefixWord ++ tailWord_1801703).sum := by decide
  have hdescent : baseEnd_1801703 < baseStart_1801703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801730 : List Nat := [3, 4, 1, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_1801730 : Nat := 118140960795 + 1801730 * 2 ^ 59
def prefixEnd_1801730 : Nat := 4983230072969 + 3 ^ 40 * 1801730 * 2
def baseEnd_1801730 : Nat := 925153499625340956789001

theorem tailTrace_1801730 : CollatzResearch.WordTrace tailWord_1801730 prefixEnd_1801730 925153499625340956789001 := by
  unfold tailWord_1801730
  simp only [CollatzResearch.WordTrace]
  refine ⟨16428622940661848957746661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43809661175098263887324429 16428622940661848957746661)
  ·
    refine ⟨3080366801374096679577499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16428622940661848957746661 3080366801374096679577499)
    ·
      refine ⟨4620550202061145019366249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3080366801374096679577499 4620550202061145019366249)
      ·
        refine ⟨3465412651545858764524687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4620550202061145019366249 3465412651545858764524687)
        ·
          refine ⟨5198118977318788146787031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3465412651545858764524687 5198118977318788146787031)
          ·
            refine ⟨7797178465978182220180547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5198118977318788146787031 7797178465978182220180547)
            ·
              refine ⟨11695767698967273330270821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7797178465978182220180547 11695767698967273330270821)
              ·
                refine ⟨2192956443556363749425779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11695767698967273330270821 2192956443556363749425779)
                ·
                  refine ⟨3289434665334545624138669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2192956443556363749425779 3289434665334545624138669)
                  ·
                    refine ⟨1233537999500454609052001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3289434665334545624138669 1233537999500454609052001)
                    ·
                      refine ⟨925153499625340956789001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1233537999500454609052001 925153499625340956789001)
                      ·
                        rfl

theorem cell23_1801730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_1801730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801730 prefixEnd_1801730 := by exact prefixLift 1801730
  have htrace : WordTrace (prefixWord ++ tailWord_1801730) baseStart_1801730 baseEnd_1801730 := by
    simpa [prefixWord, tailWord_1801730, baseEnd_1801730] using wordTrace_append hprefix tailTrace_1801730
  have hstable : (prefixWord ++ tailWord_1801730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801730).length < 2 ^ (prefixWord ++ tailWord_1801730).sum := by decide
  have hdescent : baseEnd_1801730 < baseStart_1801730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801759 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 3]
def baseStart_1801759 : Nat := 118140960795 + 1801759 * 2 ^ 59
def prefixEnd_1801759 : Nat := 4983230072969 + 3 ^ 40 * 1801759 * 2
def baseEnd_1801759 : Nat := 925168390564321343326367

theorem tailTrace_1801759 : CollatzResearch.WordTrace tailWord_1801759 prefixEnd_1801759 925168390564321343326367 := by
  unfold tailWord_1801759
  simp only [CollatzResearch.WordTrace]
  refine ⟨65715549479542333783792331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43810366319694889189194887 65715549479542333783792331)
  ·
    refine ⟨98573324219313500675688497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65715549479542333783792331 98573324219313500675688497)
    ·
      refine ⟨73929993164485125506766373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98573324219313500675688497 73929993164485125506766373)
      ·
        refine ⟨13861873718340961032518695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73929993164485125506766373 13861873718340961032518695)
        ·
          refine ⟨20792810577511441548778043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13861873718340961032518695 20792810577511441548778043)
          ·
            refine ⟨31189215866267162323167065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20792810577511441548778043 31189215866267162323167065)
            ·
              refine ⟨23391911899700371742375299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31189215866267162323167065 23391911899700371742375299)
              ·
                refine ⟨35087867849550557613562949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23391911899700371742375299 35087867849550557613562949)
                ·
                  refine ⟨6578975221790729552543053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35087867849550557613562949 6578975221790729552543053)
                  ·
                    refine ⟨2467115708171523582203645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6578975221790729552543053 2467115708171523582203645)
                    ·
                      refine ⟨925168390564321343326367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2467115708171523582203645 925168390564321343326367)
                      ·
                        rfl

theorem cell23_1801759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_1801759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801759 prefixEnd_1801759 := by exact prefixLift 1801759
  have htrace : WordTrace (prefixWord ++ tailWord_1801759) baseStart_1801759 baseEnd_1801759 := by
    simpa [prefixWord, tailWord_1801759, baseEnd_1801759] using wordTrace_append hprefix tailTrace_1801759
  have hstable : (prefixWord ++ tailWord_1801759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801759).length < 2 ^ (prefixWord ++ tailWord_1801759).sum := by decide
  have hdescent : baseEnd_1801759 < baseStart_1801759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801816 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 2, 4, 2]
def baseStart_1801816 : Nat := 118140960795 + 1801816 * 2 ^ 59
def prefixEnd_1801816 : Nat := 4983230072969 + 3 ^ 40 * 1801816 * 2
def baseEnd_1801816 : Nat := 925197658961627620313605

theorem tailTrace_1801816 : CollatzResearch.WordTrace tailWord_1801816 prefixEnd_1801816 925197658961627620313605 := by
  unfold tailWord_1801816
  simp only [CollatzResearch.WordTrace]
  refine ⟨32858814220167916259308651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43811752293557221679078201 32858814220167916259308651)
  ·
    refine ⟨49288221330251874388962977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32858814220167916259308651 49288221330251874388962977)
    ·
      refine ⟨36966165997688905791722233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49288221330251874388962977 36966165997688905791722233)
      ·
        refine ⟨27724624498266679343791675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36966165997688905791722233 27724624498266679343791675)
        ·
          refine ⟨41586936747400019015687513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27724624498266679343791675 41586936747400019015687513)
          ·
            refine ⟨31190202560550014261765635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41586936747400019015687513 31190202560550014261765635)
            ·
              refine ⟨46785303840825021392648453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31190202560550014261765635 46785303840825021392648453)
              ·
                refine ⟨8772244470154691511121585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46785303840825021392648453 8772244470154691511121585)
                ·
                  refine ⟨6579183352616018633341189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8772244470154691511121585 6579183352616018633341189)
                  ·
                    refine ⟨1233596878615503493751473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6579183352616018633341189 1233596878615503493751473)
                    ·
                      refine ⟨925197658961627620313605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1233596878615503493751473 925197658961627620313605)
                      ·
                        rfl

theorem cell23_1801816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_1801816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801816 prefixEnd_1801816 := by exact prefixLift 1801816
  have htrace : WordTrace (prefixWord ++ tailWord_1801816) baseStart_1801816 baseEnd_1801816 := by
    simpa [prefixWord, tailWord_1801816, baseEnd_1801816] using wordTrace_append hprefix tailTrace_1801816
  have hstable : (prefixWord ++ tailWord_1801816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801816).length < 2 ^ (prefixWord ++ tailWord_1801816).sum := by decide
  have hdescent : baseEnd_1801816 < baseStart_1801816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801853 : List Nat := [1, 4, 1, 1, 4, 1, 3, 1, 2, 2, 3]
def baseStart_1801853 : Nat := 118140960795 + 1801853 * 2 ^ 59
def prefixEnd_1801853 : Nat := 4983230072969 + 3 ^ 40 * 1801853 * 2
def baseEnd_1801853 : Nat := 925216657745843975550935

theorem tailTrace_1801853 : CollatzResearch.WordTrace tailWord_1801853 prefixEnd_1801853 925216657745843975550935 := by
  unfold tailWord_1801853
  simp only [CollatzResearch.WordTrace]
  refine ⟨65718977941201787837714213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43812651960801191891809475 65718977941201787837714213)
  ·
    refine ⟨12322308363975335219571415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65718977941201787837714213 12322308363975335219571415)
    ·
      refine ⟨18483462545963002829357123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12322308363975335219571415 18483462545963002829357123)
      ·
        refine ⟨27725193818944504244035685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18483462545963002829357123 27725193818944504244035685)
        ·
          refine ⟨5198473841052094545756691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27725193818944504244035685 5198473841052094545756691)
          ·
            refine ⟨7797710761578141818635037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5198473841052094545756691 7797710761578141818635037)
            ·
              refine ⟨2924141535591803181988139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7797710761578141818635037 2924141535591803181988139)
              ·
                refine ⟨4386212303387704772982209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2924141535591803181988139 4386212303387704772982209)
                ·
                  refine ⟨3289659227540778579736657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4386212303387704772982209 3289659227540778579736657)
                  ·
                    refine ⟨2467244420655583934802493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3289659227540778579736657 2467244420655583934802493)
                    ·
                      refine ⟨925216657745843975550935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2467244420655583934802493 925216657745843975550935)
                      ·
                        rfl

theorem cell23_1801853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_1801853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801853 prefixEnd_1801853 := by exact prefixLift 1801853
  have htrace : WordTrace (prefixWord ++ tailWord_1801853) baseStart_1801853 baseEnd_1801853 := by
    simpa [prefixWord, tailWord_1801853, baseEnd_1801853] using wordTrace_append hprefix tailTrace_1801853
  have hstable : (prefixWord ++ tailWord_1801853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801853).length < 2 ^ (prefixWord ++ tailWord_1801853).sum := by decide
  have hdescent : baseEnd_1801853 < baseStart_1801853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801906 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_1801906 : Nat := 118140960795 + 1801906 * 2 ^ 59
def prefixEnd_1801906 : Nat := 4983230072969 + 3 ^ 40 * 1801906 * 2
def baseEnd_1801906 : Nat := 925243872220532268188191

theorem tailTrace_1801906 : CollatzResearch.WordTrace tailWord_1801906 prefixEnd_1801906 925243872220532268188191 := by
  unfold tailWord_1801906
  simp only [CollatzResearch.WordTrace]
  refine ⟨16430227752502444472348393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43813940673339851926262381 16430227752502444472348393)
  ·
    refine ⟨12322670814376833354261295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16430227752502444472348393 12322670814376833354261295)
    ·
      refine ⟨18484006221565250031391943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12322670814376833354261295 18484006221565250031391943)
      ·
        refine ⟨27726009332347875047087915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18484006221565250031391943 27726009332347875047087915)
        ·
          refine ⟨41589013998521812570631873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27726009332347875047087915 41589013998521812570631873)
          ·
            refine ⟨31191760498891359427973905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41589013998521812570631873 31191760498891359427973905)
            ·
              refine ⟨23393820374168519570980429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31191760498891359427973905 23393820374168519570980429)
              ·
                refine ⟨8772682640313194839117661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23393820374168519570980429 8772682640313194839117661)
                ·
                  refine ⟨3289755990117448064669123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8772682640313194839117661 3289755990117448064669123)
                  ·
                    refine ⟨4934633985176172097003685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3289755990117448064669123 4934633985176172097003685)
                    ·
                      refine ⟨925243872220532268188191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4934633985176172097003685 925243872220532268188191)
                      ·
                        rfl

theorem cell23_1801906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_1801906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801906 prefixEnd_1801906 := by exact prefixLift 1801906
  have htrace : WordTrace (prefixWord ++ tailWord_1801906) baseStart_1801906 baseEnd_1801906 := by
    simpa [prefixWord, tailWord_1801906, baseEnd_1801906] using wordTrace_append hprefix tailTrace_1801906
  have hstable : (prefixWord ++ tailWord_1801906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801906).length < 2 ^ (prefixWord ++ tailWord_1801906).sum := by decide
  have hdescent : baseEnd_1801906 < baseStart_1801906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801946 : List Nat := [3, 1, 1, 2, 2, 4, 2, 8]
def baseStart_1801946 : Nat := 118140960795 + 1801946 * 2 ^ 59
def prefixEnd_1801946 : Nat := 4983230072969 + 3 ^ 40 * 1801946 * 2
def baseEnd_1801946 : Nat := 34269052275804152284741

theorem tailTrace_1801946 : CollatzResearch.WordTrace tailWord_1801946 prefixEnd_1801946 34269052275804152284741 := by
  unfold tailWord_1801946
  simp only [CollatzResearch.WordTrace]
  refine ⟨16430592482466216180212423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43814913286576576480566461 16430592482466216180212423)
  ·
    refine ⟨24645888723699324270318635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16430592482466216180212423 24645888723699324270318635)
    ·
      refine ⟨36968833085548986405477953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24645888723699324270318635 36968833085548986405477953)
      ·
        refine ⟨27726624814161739804108465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36968833085548986405477953 27726624814161739804108465)
        ·
          refine ⟨20794968610621304853081349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27726624814161739804108465 20794968610621304853081349)
          ·
            refine ⟨3899056614491494659952753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20794968610621304853081349 3899056614491494659952753)
            ·
              refine ⟨2924292460868620994964565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3899056614491494659952753 2924292460868620994964565)
              ·
                refine ⟨34269052275804152284741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2924292460868620994964565 34269052275804152284741)
                ·
                  rfl

theorem cell23_1801946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 8].length) (baseStart_1801946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801946 prefixEnd_1801946 := by exact prefixLift 1801946
  have htrace : WordTrace (prefixWord ++ tailWord_1801946) baseStart_1801946 baseEnd_1801946 := by
    simpa [prefixWord, tailWord_1801946, baseEnd_1801946] using wordTrace_append hprefix tailTrace_1801946
  have hstable : (prefixWord ++ tailWord_1801946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801946).length < 2 ^ (prefixWord ++ tailWord_1801946).sum := by decide
  have hdescent : baseEnd_1801946 < baseStart_1801946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801960 : List Nat := [2, 1, 4, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_1801960 : Nat := 118140960795 + 1801960 * 2 ^ 59
def prefixEnd_1801960 : Nat := 4983230072969 + 3 ^ 40 * 1801960 * 2
def baseEnd_1801960 : Nat := 925271600175875056912943

theorem tailTrace_1801960 : CollatzResearch.WordTrace tailWord_1801960 prefixEnd_1801960 925271600175875056912943 := by
  unfold tailWord_1801960
  simp only [CollatzResearch.WordTrace]
  refine ⟨32861440275907072555929667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43815253701209430074572889 32861440275907072555929667)
  ·
    refine ⟨49292160413860608833894501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32861440275907072555929667 49292160413860608833894501)
    ·
      refine ⟨9242280077598864156355219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49292160413860608833894501 9242280077598864156355219)
      ·
        refine ⟨13863420116398296234532829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9242280077598864156355219 13863420116398296234532829)
        ·
          refine ⟨5198782543649361087949811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13863420116398296234532829 5198782543649361087949811)
          ·
            refine ⟨7798173815474041631924717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5198782543649361087949811 7798173815474041631924717)
            ·
              refine ⟨2924315180802765611971769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7798173815474041631924717 2924315180802765611971769)
              ·
                refine ⟨2193236385602074208978827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2924315180802765611971769 2193236385602074208978827)
                ·
                  refine ⟨3289854578403111313468241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193236385602074208978827 3289854578403111313468241)
                  ·
                    refine ⟨2467390933802333485101181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3289854578403111313468241 2467390933802333485101181)
                    ·
                      refine ⟨925271600175875056912943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2467390933802333485101181 925271600175875056912943)
                      ·
                        rfl

theorem cell23_1801960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_1801960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801960 prefixEnd_1801960 := by exact prefixLift 1801960
  have htrace : WordTrace (prefixWord ++ tailWord_1801960) baseStart_1801960 baseEnd_1801960 := by
    simpa [prefixWord, tailWord_1801960, baseEnd_1801960] using wordTrace_append hprefix tailTrace_1801960
  have hstable : (prefixWord ++ tailWord_1801960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801960).length < 2 ^ (prefixWord ++ tailWord_1801960).sum := by decide
  have hdescent : baseEnd_1801960 < baseStart_1801960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801996 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 2, 3, 4]
def baseStart_1801996 : Nat := 118140960795 + 1801996 * 2 ^ 59
def prefixEnd_1801996 : Nat := 4983230072969 + 3 ^ 40 * 1801996 * 2
def baseEnd_1801996 : Nat := 925290085479436916062777

theorem tailTrace_1801996 : CollatzResearch.WordTrace tailWord_1801996 prefixEnd_1801996 925290085479436916062777 := by
  unfold tailWord_1801996
  simp only [CollatzResearch.WordTrace]
  refine ⟨32862096789841861630084921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43816129053122482173446561 32862096789841861630084921)
  ·
    refine ⟨24646572592381396222563691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32862096789841861630084921 24646572592381396222563691)
    ·
      refine ⟨36969858888572094333845537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24646572592381396222563691 36969858888572094333845537)
      ·
        refine ⟨27727394166429070750384153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36969858888572094333845537 27727394166429070750384153)
        ·
          refine ⟨20795545624821803062788115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27727394166429070750384153 20795545624821803062788115)
          ·
            refine ⟨31193318437232704594182173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20795545624821803062788115 31193318437232704594182173)
            ·
              refine ⟨11697494413962264222818315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31193318437232704594182173 11697494413962264222818315)
              ·
                refine ⟨17546241620943396334227473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11697494413962264222818315 17546241620943396334227473)
                ·
                  refine ⟨13159681215707547250670605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17546241620943396334227473 13159681215707547250670605)
                  ·
                    refine ⟨4934880455890330219001477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13159681215707547250670605 4934880455890330219001477)
                    ·
                      refine ⟨925290085479436916062777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4934880455890330219001477 925290085479436916062777)
                      ·
                        rfl

theorem cell23_1801996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_1801996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1801996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1801996 prefixEnd_1801996 := by exact prefixLift 1801996
  have htrace : WordTrace (prefixWord ++ tailWord_1801996) baseStart_1801996 baseEnd_1801996 := by
    simpa [prefixWord, tailWord_1801996, baseEnd_1801996] using wordTrace_append hprefix tailTrace_1801996
  have hstable : (prefixWord ++ tailWord_1801996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801996).length < 2 ^ (prefixWord ++ tailWord_1801996).sum := by decide
  have hdescent : baseEnd_1801996 < baseStart_1801996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802004 : List Nat := [2, 4, 4, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1802004 : Nat := 118140960795 + 1802004 * 2 ^ 59
def prefixEnd_1802004 : Nat := 4983230072969 + 3 ^ 40 * 1802004 * 2
def baseEnd_1802004 : Nat := 925294193324672884762741

theorem tailTrace_1802004 : CollatzResearch.WordTrace tailWord_1802004 prefixEnd_1802004 925294193324672884762741 := by
  unfold tailWord_1802004
  simp only [CollatzResearch.WordTrace]
  refine ⟨32862242681827370313230533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43816323575769827084307377 32862242681827370313230533)
  ·
    refine ⟨6161670502842631933730725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32862242681827370313230533 6161670502842631933730725)
    ·
      refine ⟨1155313219282993487574511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6161670502842631933730725 1155313219282993487574511)
      ·
        refine ⟨1732969828924490231361767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1155313219282993487574511 1732969828924490231361767)
        ·
          refine ⟨2599454743386735347042651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1732969828924490231361767 2599454743386735347042651)
          ·
            refine ⟨3899182115080103020563977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2599454743386735347042651 3899182115080103020563977)
            ·
              refine ⟨2924386586310077265422983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3899182115080103020563977 2924386586310077265422983)
              ·
                refine ⟨4386579879465115898134475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2924386586310077265422983 4386579879465115898134475)
                ·
                  refine ⟨6579869819197673847201713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4386579879465115898134475 6579869819197673847201713)
                  ·
                    refine ⟨4934902364398255385401285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6579869819197673847201713 4934902364398255385401285)
                    ·
                      refine ⟨925294193324672884762741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4934902364398255385401285 925294193324672884762741)
                      ·
                        rfl

theorem cell23_1802004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1802004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802004 prefixEnd_1802004 := by exact prefixLift 1802004
  have htrace : WordTrace (prefixWord ++ tailWord_1802004) baseStart_1802004 baseEnd_1802004 := by
    simpa [prefixWord, tailWord_1802004, baseEnd_1802004] using wordTrace_append hprefix tailTrace_1802004
  have hstable : (prefixWord ++ tailWord_1802004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802004).length < 2 ^ (prefixWord ++ tailWord_1802004).sum := by decide
  have hdescent : baseEnd_1802004 < baseStart_1802004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802034 : List Nat := [3, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2]
def baseStart_1802034 : Nat := 118140960795 + 1802034 * 2 ^ 59
def prefixEnd_1802034 : Nat := 4983230072969 + 3 ^ 40 * 1802034 * 2
def baseEnd_1802034 : Nat := 925309597744307767387603

theorem tailTrace_1802034 : CollatzResearch.WordTrace tailWord_1802034 prefixEnd_1802034 925309597744307767387603 := by
  unfold tailWord_1802034
  simp only [CollatzResearch.WordTrace]
  refine ⟨16431394888386513937513289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43817053035697370500035437 16431394888386513937513289)
  ·
    refine ⟨12323546166289885453134967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16431394888386513937513289 12323546166289885453134967)
    ·
      refine ⟨18485319249434828179702451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12323546166289885453134967 18485319249434828179702451)
      ·
        refine ⟨27727978874152242269553677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18485319249434828179702451 27727978874152242269553677)
        ·
          refine ⟨10397992077807090851082629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27727978874152242269553677 10397992077807090851082629)
          ·
            refine ⟨1949623514588829534577993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10397992077807090851082629 1949623514588829534577993)
            ·
              refine ⟨1462217635941622150933495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1949623514588829534577993 1462217635941622150933495)
              ·
                refine ⟨2193326453912433226400243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1462217635941622150933495 2193326453912433226400243)
                ·
                  refine ⟨3289989680868649839600365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193326453912433226400243 3289989680868649839600365)
                  ·
                    refine ⟨1233746130325743689850137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3289989680868649839600365 1233746130325743689850137)
                    ·
                      refine ⟨925309597744307767387603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1233746130325743689850137 925309597744307767387603)
                      ·
                        rfl

theorem cell23_1802034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_1802034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802034 prefixEnd_1802034 := by exact prefixLift 1802034
  have htrace : WordTrace (prefixWord ++ tailWord_1802034) baseStart_1802034 baseEnd_1802034 := by
    simpa [prefixWord, tailWord_1802034, baseEnd_1802034] using wordTrace_append hprefix tailTrace_1802034
  have hstable : (prefixWord ++ tailWord_1802034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802034).length < 2 ^ (prefixWord ++ tailWord_1802034).sum := by decide
  have hdescent : baseEnd_1802034 < baseStart_1802034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802041 : List Nat := [1, 2, 1, 7, 2, 1, 1, 2, 2, 1, 3]
def baseStart_1802041 : Nat := 118140960795 + 1802041 * 2 ^ 59
def prefixEnd_1802041 : Nat := 4983230072969 + 3 ^ 40 * 1802041 * 2
def baseEnd_1802041 : Nat := 925313192108889240000071

theorem tailTrace_1802041 : CollatzResearch.WordTrace tailWord_1802041 prefixEnd_1802041 925313192108889240000071 := by
  unfold tailWord_1802041
  simp only [CollatzResearch.WordTrace]
  refine ⟨65725834864520695945557977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43817223243013797297038651 65725834864520695945557977)
  ·
    refine ⟨49294376148390521959168483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65725834864520695945557977 49294376148390521959168483)
    ·
      refine ⟨73941564222585782938752725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49294376148390521959168483 73941564222585782938752725)
      ·
        refine ⟨1733005411466854287627017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 73941564222585782938752725 1733005411466854287627017)
        ·
          refine ⟨1299754058600140715720263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1733005411466854287627017 1299754058600140715720263)
          ·
            refine ⟨1949631087900211073580395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1299754058600140715720263 1949631087900211073580395)
            ·
              refine ⟨2924446631850316610370593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1949631087900211073580395 2924446631850316610370593)
              ·
                refine ⟨2193334973887737457777945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2924446631850316610370593 2193334973887737457777945)
                ·
                  refine ⟨1645001230415803093333459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2193334973887737457777945 1645001230415803093333459)
                  ·
                    refine ⟨2467501845623704640000189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1645001230415803093333459 2467501845623704640000189)
                    ·
                      refine ⟨925313192108889240000071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2467501845623704640000189 925313192108889240000071)
                      ·
                        rfl

theorem cell23_1802041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_1802041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802041 prefixEnd_1802041 := by exact prefixLift 1802041
  have htrace : WordTrace (prefixWord ++ tailWord_1802041) baseStart_1802041 baseEnd_1802041 := by
    simpa [prefixWord, tailWord_1802041, baseEnd_1802041] using wordTrace_append hprefix tailTrace_1802041
  have hstable : (prefixWord ++ tailWord_1802041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802041).length < 2 ^ (prefixWord ++ tailWord_1802041).sum := by decide
  have hdescent : baseEnd_1802041 < baseStart_1802041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802047 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 4, 2, 2]
def baseStart_1802047 : Nat := 118140960795 + 1802047 * 2 ^ 59
def prefixEnd_1802047 : Nat := 4983230072969 + 3 ^ 40 * 1802047 * 2
def baseEnd_1802047 : Nat := 925316272992816216525043

theorem tailTrace_1802047 : CollatzResearch.WordTrace tailWord_1802047 prefixEnd_1802047 925316272992816216525043 := by
  unfold tailWord_1802047
  simp only [CollatzResearch.WordTrace]
  refine ⟨65726053702498958970276395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43817369134999305980184263 65726053702498958970276395)
  ·
    refine ⟨98589080553748438455414593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65726053702498958970276395 98589080553748438455414593)
    ·
      refine ⟨73941810415311328841560945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98589080553748438455414593 73941810415311328841560945)
      ·
        refine ⟨55456357811483496631170709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73941810415311328841560945 55456357811483496631170709)
        ·
          refine ⟨2599516772413288904586127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55456357811483496631170709 2599516772413288904586127)
          ·
            refine ⟨3899275158619933356879191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2599516772413288904586127 3899275158619933356879191)
            ·
              refine ⟨5848912737929900035318787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3899275158619933356879191 5848912737929900035318787)
              ·
                refine ⟨8773369106894850052978181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5848912737929900035318787 8773369106894850052978181)
                ·
                  refine ⟨1645006707542784384933409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8773369106894850052978181 1645006707542784384933409)
                  ·
                    refine ⟨1233755030657088288700057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1645006707542784384933409 1233755030657088288700057)
                    ·
                      refine ⟨925316272992816216525043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1233755030657088288700057 925316272992816216525043)
                      ·
                        rfl

theorem cell23_1802047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 2, 2].length) (baseStart_1802047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802047 prefixEnd_1802047 := by exact prefixLift 1802047
  have htrace : WordTrace (prefixWord ++ tailWord_1802047) baseStart_1802047 baseEnd_1802047 := by
    simpa [prefixWord, tailWord_1802047, baseEnd_1802047] using wordTrace_append hprefix tailTrace_1802047
  have hstable : (prefixWord ++ tailWord_1802047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802047).length < 2 ^ (prefixWord ++ tailWord_1802047).sum := by decide
  have hdescent : baseEnd_1802047 < baseStart_1802047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802053 : List Nat := [1, 3, 1, 1, 1, 2, 3, 6, 5]
def baseStart_1802053 : Nat := 118140960795 + 1802053 * 2 ^ 59
def prefixEnd_1802053 : Nat := 4983230072969 + 3 ^ 40 * 1802053 * 2
def baseEnd_1802053 : Nat := 102813261541860354783335

theorem tailTrace_1802053 : CollatzResearch.WordTrace tailWord_1802053 prefixEnd_1802053 102813261541860354783335 := by
  unfold tailWord_1802053
  simp only [CollatzResearch.WordTrace]
  refine ⟨65726272540477221994994813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43817515026984814663329875 65726272540477221994994813)
  ·
    refine ⟨24647352202678958248123055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65726272540477221994994813 24647352202678958248123055)
    ·
      refine ⟨36971028304018437372184583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24647352202678958248123055 36971028304018437372184583)
      ·
        refine ⟨55456542456027656058276875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36971028304018437372184583 55456542456027656058276875)
        ·
          refine ⟨83184813684041484087415313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55456542456027656058276875 83184813684041484087415313)
          ·
            refine ⟨62388610263031113065561485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83184813684041484087415313 62388610263031113065561485)
            ·
              refine ⟨23395728848636667399585557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62388610263031113065561485 23395728848636667399585557)
              ·
                refine ⟨1096674789779843784355573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23395728848636667399585557 1096674789779843784355573)
                ·
                  refine ⟨102813261541860354783335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1096674789779843784355573 102813261541860354783335)
                  ·
                    rfl

theorem cell23_1802053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 5].length) (baseStart_1802053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802053 prefixEnd_1802053 := by exact prefixLift 1802053
  have htrace : WordTrace (prefixWord ++ tailWord_1802053) baseStart_1802053 baseEnd_1802053 := by
    simpa [prefixWord, tailWord_1802053, baseEnd_1802053] using wordTrace_append hprefix tailTrace_1802053
  have hstable : (prefixWord ++ tailWord_1802053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802053).length < 2 ^ (prefixWord ++ tailWord_1802053).sum := by decide
  have hdescent : baseEnd_1802053 < baseStart_1802053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802110 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1802110 : Nat := 118140960795 + 1802110 * 2 ^ 59
def prefixEnd_1802110 : Nat := 4983230072969 + 3 ^ 40 * 1802110 * 2
def baseEnd_1802110 : Nat := 925348622274049470037253

theorem tailTrace_1802110 : CollatzResearch.WordTrace tailWord_1802110 prefixEnd_1802110 925348622274049470037253 := by
  unfold tailWord_1802110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8216043937658840091227473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43818901000847147153213189 8216043937658840091227473)
  ·
    refine ⟨6162032953244130068420605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8216043937658840091227473 6162032953244130068420605)
    ·
      refine ⟨2310762357466548775657727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6162032953244130068420605 2310762357466548775657727)
      ·
        refine ⟨3466143536199823163486591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2310762357466548775657727 3466143536199823163486591)
        ·
          refine ⟨5199215304299734745229887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3466143536199823163486591 5199215304299734745229887)
          ·
            refine ⟨7798822956449602117844831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5199215304299734745229887 7798822956449602117844831)
            ·
              refine ⟨11698234434674403176767247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7798822956449602117844831 11698234434674403176767247)
              ·
                refine ⟨17547351652011604765150871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11698234434674403176767247 17547351652011604765150871)
                ·
                  refine ⟨26321027478017407147726307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17547351652011604765150871 26321027478017407147726307)
                  ·
                    refine ⟨39481541217026110721589461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26321027478017407147726307 39481541217026110721589461)
                    ·
                      refine ⟨925348622274049470037253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39481541217026110721589461 925348622274049470037253)
                      ·
                        rfl

theorem cell23_1802110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1802110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802110 prefixEnd_1802110 := by exact prefixLift 1802110
  have htrace : WordTrace (prefixWord ++ tailWord_1802110) baseStart_1802110 baseEnd_1802110 := by
    simpa [prefixWord, tailWord_1802110, baseEnd_1802110] using wordTrace_append hprefix tailTrace_1802110
  have hstable : (prefixWord ++ tailWord_1802110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802110).length < 2 ^ (prefixWord ++ tailWord_1802110).sum := by decide
  have hdescent : baseEnd_1802110 < baseStart_1802110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802123 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 3]
def baseStart_1802123 : Nat := 118140960795 + 1802123 * 2 ^ 59
def prefixEnd_1802123 : Nat := 4983230072969 + 3 ^ 40 * 1802123 * 2
def baseEnd_1802123 : Nat := 925355297522557919174693

theorem tailTrace_1802123 : CollatzResearch.WordTrace tailWord_1802123 prefixEnd_1802123 925355297522557919174693 := by
  unfold tailWord_1802123
  simp only [CollatzResearch.WordTrace]
  refine ⟨65728825650223623950043023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43819217100149082633362015 65728825650223623950043023)
  ·
    refine ⟨98593238475335435925064535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65728825650223623950043023 98593238475335435925064535)
    ·
      refine ⟨147889857713003153887596803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98593238475335435925064535 147889857713003153887596803)
      ·
        refine ⟨221834786569504730831395205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147889857713003153887596803 221834786569504730831395205)
        ·
          refine ⟨41594022481782137030886601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221834786569504730831395205 41594022481782137030886601)
          ·
            refine ⟨31195516861336602773164951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41594022481782137030886601 31195516861336602773164951)
            ·
              refine ⟨46793275292004904159747427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31195516861336602773164951 46793275292004904159747427)
              ·
                refine ⟨70189912938007356239621141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46793275292004904159747427 70189912938007356239621141)
                ·
                  refine ⟨3290152168969094823732241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70189912938007356239621141 3290152168969094823732241)
                  ·
                    refine ⟨2467614126726821117799181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3290152168969094823732241 2467614126726821117799181)
                    ·
                      refine ⟨925355297522557919174693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2467614126726821117799181 925355297522557919174693)
                      ·
                        rfl

theorem cell23_1802123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 3].length) (baseStart_1802123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802123 prefixEnd_1802123 := by exact prefixLift 1802123
  have htrace : WordTrace (prefixWord ++ tailWord_1802123) baseStart_1802123 baseEnd_1802123 := by
    simpa [prefixWord, tailWord_1802123, baseEnd_1802123] using wordTrace_append hprefix tailTrace_1802123
  have hstable : (prefixWord ++ tailWord_1802123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802123).length < 2 ^ (prefixWord ++ tailWord_1802123).sum := by decide
  have hdescent : baseEnd_1802123 < baseStart_1802123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802190 : List Nat := [4, 1, 1, 1, 2, 2, 2, 4, 1, 5]
def baseStart_1802190 : Nat := 118140960795 + 1802190 * 2 ^ 59
def prefixEnd_1802190 : Nat := 4983230072969 + 3 ^ 40 * 1802190 * 2
def baseEnd_1802190 : Nat := 308463233575469719012295

theorem tailTrace_1802190 : CollatzResearch.WordTrace tailWord_1802190 prefixEnd_1802190 308463233575469719012295 := by
  unfold tailWord_1802190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8216408667622611799091503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43820846227320596261821349 8216408667622611799091503)
  ·
    refine ⟨12324613001433917698637255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8216408667622611799091503 12324613001433917698637255)
    ·
      refine ⟨18486919502150876547955883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12324613001433917698637255 18486919502150876547955883)
      ·
        refine ⟨27730379253226314821933825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18486919502150876547955883 27730379253226314821933825)
        ·
          refine ⟨20797784439919736116450369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27730379253226314821933825 20797784439919736116450369)
          ·
            refine ⟨15598338329939802087337777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20797784439919736116450369 15598338329939802087337777)
            ·
              refine ⟨11698753747454851565503333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15598338329939802087337777 11698753747454851565503333)
              ·
                refine ⟨2193516327647784668531875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11698753747454851565503333 2193516327647784668531875)
                ·
                  refine ⟨3290274491471677002797813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193516327647784668531875 3290274491471677002797813)
                  ·
                    refine ⟨308463233575469719012295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3290274491471677002797813 308463233575469719012295)
                    ·
                      rfl

theorem cell23_1802190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_1802190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802190 prefixEnd_1802190 := by exact prefixLift 1802190
  have htrace : WordTrace (prefixWord ++ tailWord_1802190) baseStart_1802190 baseEnd_1802190 := by
    simpa [prefixWord, tailWord_1802190, baseEnd_1802190] using wordTrace_append hprefix tailTrace_1802190
  have hstable : (prefixWord ++ tailWord_1802190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802190).length < 2 ^ (prefixWord ++ tailWord_1802190).sum := by decide
  have hdescent : baseEnd_1802190 < baseStart_1802190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802197 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 1, 5, 2]
def baseStart_1802197 : Nat := 118140960795 + 1802197 * 2 ^ 59
def prefixEnd_1802197 : Nat := 4983230072969 + 3 ^ 40 * 1802197 * 2
def baseEnd_1802197 : Nat := 925393295090990629649353

theorem tailTrace_1802197 : CollatzResearch.WordTrace tailWord_1802197 prefixEnd_1802197 925393295090990629649353 := by
  unfold tailWord_1802197
  simp only [CollatzResearch.WordTrace]
  refine ⟨65731524651955534588236845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43821016434637023058824563 65731524651955534588236845)
  ·
    refine ⟨24649321744483325470588817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65731524651955534588236845 24649321744483325470588817)
    ·
      refine ⟨18486991308362494102941613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24649321744483325470588817 18486991308362494102941613)
      ·
        refine ⟨6932621740635935288603105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18486991308362494102941613 6932621740635935288603105)
        ·
          refine ⟨5199466305476951466452329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6932621740635935288603105 5199466305476951466452329)
          ·
            refine ⟨3899599729107713599839247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5199466305476951466452329 3899599729107713599839247)
            ·
              refine ⟨5849399593661570399758871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3899599729107713599839247 5849399593661570399758871)
              ·
                refine ⟨8774099390492355599638307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5849399593661570399758871 8774099390492355599638307)
                ·
                  refine ⟨13161149085738533399457461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8774099390492355599638307 13161149085738533399457461)
                  ·
                    refine ⟨1233857726787987506199137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13161149085738533399457461 1233857726787987506199137)
                    ·
                      refine ⟨925393295090990629649353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1233857726787987506199137 925393295090990629649353)
                      ·
                        rfl

theorem cell23_1802197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_1802197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802197 prefixEnd_1802197 := by exact prefixLift 1802197
  have htrace : WordTrace (prefixWord ++ tailWord_1802197) baseStart_1802197 baseEnd_1802197 := by
    simpa [prefixWord, tailWord_1802197, baseEnd_1802197] using wordTrace_append hprefix tailTrace_1802197
  have hstable : (prefixWord ++ tailWord_1802197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802197).length < 2 ^ (prefixWord ++ tailWord_1802197).sum := by decide
  have hdescent : baseEnd_1802197 < baseStart_1802197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802207 : List Nat := [1, 1, 2, 3, 4, 1, 4, 1, 1, 5]
def baseStart_1802207 : Nat := 118140960795 + 1802207 * 2 ^ 59
def prefixEnd_1802207 : Nat := 4983230072969 + 3 ^ 40 * 1802207 * 2
def baseEnd_1802207 : Nat := 308466143299178530174769

theorem tailTrace_1802207 : CollatzResearch.WordTrace tailWord_1802207 prefixEnd_1802207 308466143299178530174769 := by
  unfold tailWord_1802207
  simp only [CollatzResearch.WordTrace]
  refine ⟨65731889381919306296100875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43821259587946204197400583 65731889381919306296100875)
  ·
    refine ⟨98597834072878959444151313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65731889381919306296100875 98597834072878959444151313)
    ·
      refine ⟨73948375554659219583113485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98597834072878959444151313 73948375554659219583113485)
      ·
        refine ⟨27730640832997207343667557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73948375554659219583113485 27730640832997207343667557)
        ·
          refine ⟨5199495156186976376937667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27730640832997207343667557 5199495156186976376937667)
          ·
            refine ⟨7799242734280464565406501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5199495156186976376937667 7799242734280464565406501)
            ·
              refine ⟨1462358012677587106013719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7799242734280464565406501 1462358012677587106013719)
              ·
                refine ⟨2193537019016380659020579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1462358012677587106013719 2193537019016380659020579)
                ·
                  refine ⟨3290305528524570988530869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193537019016380659020579 3290305528524570988530869)
                  ·
                    refine ⟨308466143299178530174769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3290305528524570988530869 308466143299178530174769)
                    ·
                      rfl

theorem cell23_1802207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 1, 5].length) (baseStart_1802207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802207 prefixEnd_1802207 := by exact prefixLift 1802207
  have htrace : WordTrace (prefixWord ++ tailWord_1802207) baseStart_1802207 baseEnd_1802207 := by
    simpa [prefixWord, tailWord_1802207, baseEnd_1802207] using wordTrace_append hprefix tailTrace_1802207
  have hstable : (prefixWord ++ tailWord_1802207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802207).length < 2 ^ (prefixWord ++ tailWord_1802207).sum := by decide
  have hdescent : baseEnd_1802207 < baseStart_1802207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802221 : List Nat := [1, 5, 1, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_1802221 : Nat := 118140960795 + 1802221 * 2 ^ 59
def prefixEnd_1802221 : Nat := 4983230072969 + 3 ^ 40 * 1802221 * 2
def baseEnd_1802221 : Nat := 925405618626698535749243

theorem tailTrace_1802221 : CollatzResearch.WordTrace tailWord_1802221 prefixEnd_1802221 925405618626698535749243 := by
  unfold tailWord_1802221
  simp only [CollatzResearch.WordTrace]
  refine ⟨65732400003868586687110517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43821600002579057791407011 65732400003868586687110517)
  ·
    refine ⟨6162412500362680001916611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65732400003868586687110517 6162412500362680001916611)
    ·
      refine ⟨9243618750544020002874917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6162412500362680001916611 9243618750544020002874917)
      ·
        refine ⟨1733178515727003750539047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9243618750544020002874917 1733178515727003750539047)
        ·
          refine ⟨2599767773590505625808571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1733178515727003750539047 2599767773590505625808571)
          ·
            refine ⟨3899651660385758438712857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2599767773590505625808571 3899651660385758438712857)
            ·
              refine ⟨2924738745289318829034643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3899651660385758438712857 2924738745289318829034643)
              ·
                refine ⟨4387108117933978243551965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2924738745289318829034643 4387108117933978243551965)
                ·
                  refine ⟨1645165544225241841331987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4387108117933978243551965 1645165544225241841331987)
                  ·
                    refine ⟨2467748316337862761997981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1645165544225241841331987 2467748316337862761997981)
                    ·
                      refine ⟨925405618626698535749243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2467748316337862761997981 925405618626698535749243)
                      ·
                        rfl

theorem cell23_1802221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_1802221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802221 prefixEnd_1802221 := by exact prefixLift 1802221
  have htrace : WordTrace (prefixWord ++ tailWord_1802221) baseStart_1802221 baseEnd_1802221 := by
    simpa [prefixWord, tailWord_1802221, baseEnd_1802221] using wordTrace_append hprefix tailTrace_1802221
  have hstable : (prefixWord ++ tailWord_1802221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802221).length < 2 ^ (prefixWord ++ tailWord_1802221).sum := by decide
  have hdescent : baseEnd_1802221 < baseStart_1802221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802223 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 6]
def baseStart_1802223 : Nat := 118140960795 + 1802223 * 2 ^ 59
def prefixEnd_1802223 : Nat := 4983230072969 + 3 ^ 40 * 1802223 * 2
def baseEnd_1802223 : Nat := 925406645588007527924233

theorem tailTrace_1802223 : CollatzResearch.WordTrace tailWord_1802223 prefixEnd_1802223 925406645588007527924233 := by
  unfold tailWord_1802223
  simp only [CollatzResearch.WordTrace]
  refine ⟨65732472949861341028683323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43821648633240894019122215 65732472949861341028683323)
  ·
    refine ⟨98598709424792011543024985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65732472949861341028683323 98598709424792011543024985)
    ·
      refine ⟨73949032068594008657268739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98598709424792011543024985 73949032068594008657268739)
      ·
        refine ⟨110923548102891012985903109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73949032068594008657268739 110923548102891012985903109)
        ·
          refine ⟨20798165269292064934856833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110923548102891012985903109 20798165269292064934856833)
          ·
            refine ⟨15598623951969048701142625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20798165269292064934856833 15598623951969048701142625)
            ·
              refine ⟨11698967963976786525856969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15598623951969048701142625 11698967963976786525856969)
              ·
                refine ⟨8774225972982589894392727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11698967963976786525856969 8774225972982589894392727)
                ·
                  refine ⟨13161338959473884841589091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8774225972982589894392727 13161338959473884841589091)
                  ·
                    refine ⟨19742008439210827262383637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13161338959473884841589091 19742008439210827262383637)
                    ·
                      refine ⟨925406645588007527924233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19742008439210827262383637 925406645588007527924233)
                      ·
                        rfl

theorem cell23_1802223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_1802223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802223 prefixEnd_1802223 := by exact prefixLift 1802223
  have htrace : WordTrace (prefixWord ++ tailWord_1802223) baseStart_1802223 baseEnd_1802223 := by
    simpa [prefixWord, tailWord_1802223, baseEnd_1802223] using wordTrace_append hprefix tailTrace_1802223
  have hstable : (prefixWord ++ tailWord_1802223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802223).length < 2 ^ (prefixWord ++ tailWord_1802223).sum := by decide
  have hdescent : baseEnd_1802223 < baseStart_1802223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802247 : List Nat := [1, 1, 4, 3, 1, 2, 1, 4, 1, 2, 3]
def baseStart_1802247 : Nat := 118140960795 + 1802247 * 2 ^ 59
def prefixEnd_1802247 : Nat := 4983230072969 + 3 ^ 40 * 1802247 * 2
def baseEnd_1802247 : Nat := 925418969123715434024123

theorem tailTrace_1802247 : CollatzResearch.WordTrace tailWord_1802247 prefixEnd_1802247 925418969123715434024123 := by
  unfold tailWord_1802247
  simp only [CollatzResearch.WordTrace]
  refine ⟨65733348301774393127556995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43822232201182928751704663 65733348301774393127556995)
  ·
    refine ⟨98600022452661589691335493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65733348301774393127556995 98600022452661589691335493)
    ·
      refine ⟨18487504209874048067125405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98600022452661589691335493 18487504209874048067125405)
      ·
        refine ⟨6932814078702768025172027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18487504209874048067125405 6932814078702768025172027)
        ·
          refine ⟨10399221118054152037758041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6932814078702768025172027 10399221118054152037758041)
          ·
            refine ⟨7799415838540614028318531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10399221118054152037758041 7799415838540614028318531)
            ·
              refine ⟨11699123757810921042477797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7799415838540614028318531 11699123757810921042477797)
              ·
                refine ⟨2193585704589547695464587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11699123757810921042477797 2193585704589547695464587)
                ·
                  refine ⟨3290378556884321543196881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193585704589547695464587 3290378556884321543196881)
                  ·
                    refine ⟨2467783917663241157397661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3290378556884321543196881 2467783917663241157397661)
                    ·
                      refine ⟨925418969123715434024123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2467783917663241157397661 925418969123715434024123)
                      ·
                        rfl

theorem cell23_1802247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_1802247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802247 prefixEnd_1802247 := by exact prefixLift 1802247
  have htrace : WordTrace (prefixWord ++ tailWord_1802247) baseStart_1802247 baseEnd_1802247 := by
    simpa [prefixWord, tailWord_1802247, baseEnd_1802247] using wordTrace_append hprefix tailTrace_1802247
  have hstable : (prefixWord ++ tailWord_1802247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802247).length < 2 ^ (prefixWord ++ tailWord_1802247).sum := by decide
  have hdescent : baseEnd_1802247 < baseStart_1802247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802250 : List Nat := [3, 1, 2, 2, 4, 1, 1, 9]
def baseStart_1802250 : Nat := 118140960795 + 1802250 * 2 ^ 59
def prefixEnd_1802250 : Nat := 4983230072969 + 3 ^ 40 * 1802250 * 2
def baseEnd_1802250 : Nat := 34274833687617737862467

theorem tailTrace_1802250 : CollatzResearch.WordTrace tailWord_1802250 prefixEnd_1802250 34274833687617737862467 := by
  unfold tailWord_1802250
  simp only [CollatzResearch.WordTrace]
  refine ⟨16433364430190881159979051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43822305147175683093277469 16433364430190881159979051)
  ·
    refine ⟨24650046645286321739968577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16433364430190881159979051 24650046645286321739968577)
    ·
      refine ⟨18487534983964741304976433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24650046645286321739968577 18487534983964741304976433)
      ·
        refine ⟨13865651237973555978732325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18487534983964741304976433 13865651237973555978732325)
        ·
          refine ⟨2599809607120041746012311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13865651237973555978732325 2599809607120041746012311)
          ·
            refine ⟨3899714410680062619018467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2599809607120041746012311 3899714410680062619018467)
            ·
              refine ⟨5849571616020093928527701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3899714410680062619018467 5849571616020093928527701)
              ·
                refine ⟨34274833687617737862467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5849571616020093928527701 34274833687617737862467)
                ·
                  rfl

theorem cell23_1802250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 9].length) (baseStart_1802250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802250 prefixEnd_1802250 := by exact prefixLift 1802250
  have htrace : WordTrace (prefixWord ++ tailWord_1802250) baseStart_1802250 baseEnd_1802250 := by
    simpa [prefixWord, tailWord_1802250, baseEnd_1802250] using wordTrace_append hprefix tailTrace_1802250
  have hstable : (prefixWord ++ tailWord_1802250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802250).length < 2 ^ (prefixWord ++ tailWord_1802250).sum := by decide
  have hdescent : baseEnd_1802250 < baseStart_1802250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802277 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 4, 1, 3]
def baseStart_1802277 : Nat := 118140960795 + 1802277 * 2 ^ 59
def prefixEnd_1802277 : Nat := 4983230072969 + 3 ^ 40 * 1802277 * 2
def baseEnd_1802277 : Nat := 925434373543350316648985

theorem tailTrace_1802277 : CollatzResearch.WordTrace tailWord_1802277 prefixEnd_1802277 925434373543350316648985 := by
  unfold tailWord_1802277
  simp only [CollatzResearch.WordTrace]
  refine ⟨65734442491665708251149085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43822961661110472167432723 65734442491665708251149085)
  ·
    refine ⟨24650415934374640594180907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65734442491665708251149085 24650415934374640594180907)
    ·
      refine ⟨36975623901561960891271361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24650415934374640594180907 36975623901561960891271361)
      ·
        refine ⟨27731717926171470668453521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36975623901561960891271361 27731717926171470668453521)
        ·
          refine ⟨20798788444628603001340141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27731717926171470668453521 20798788444628603001340141)
          ·
            refine ⟨7799545666735726125502553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20798788444628603001340141 7799545666735726125502553)
            ·
              refine ⟨5849659250051794594126915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7799545666735726125502553 5849659250051794594126915)
              ·
                refine ⟨8774488875077691891190373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5849659250051794594126915 8774488875077691891190373)
                ·
                  refine ⟨1645216664077067229598195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8774488875077691891190373 1645216664077067229598195)
                  ·
                    refine ⟨2467824996115600844397293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1645216664077067229598195 2467824996115600844397293)
                    ·
                      refine ⟨925434373543350316648985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2467824996115600844397293 925434373543350316648985)
                      ·
                        rfl

theorem cell23_1802277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_1802277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802277 prefixEnd_1802277 := by exact prefixLift 1802277
  have htrace : WordTrace (prefixWord ++ tailWord_1802277) baseStart_1802277 baseEnd_1802277 := by
    simpa [prefixWord, tailWord_1802277, baseEnd_1802277] using wordTrace_append hprefix tailTrace_1802277
  have hstable : (prefixWord ++ tailWord_1802277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802277).length < 2 ^ (prefixWord ++ tailWord_1802277).sum := by decide
  have hdescent : baseEnd_1802277 < baseStart_1802277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802304 : List Nat := [2, 1, 1, 2, 2, 4, 3, 2, 1, 3, 2]
def baseStart_1802304 : Nat := 118140960795 + 1802304 * 2 ^ 59
def prefixEnd_1802304 : Nat := 4983230072969 + 3 ^ 40 * 1802304 * 2
def baseEnd_1802304 : Nat := 925448237521021711011361

theorem tailTrace_1802304 : CollatzResearch.WordTrace tailWord_1802304 prefixEnd_1802304 925448237521021711011361 := by
  unfold tailWord_1802304
  simp only [CollatzResearch.WordTrace]
  refine ⟨32867713631283945931190983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43823618175045261241587977 32867713631283945931190983)
  ·
    refine ⟨49301570446925918896786475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32867713631283945931190983 49301570446925918896786475)
    ·
      refine ⟨73952355670388878345179713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49301570446925918896786475 73952355670388878345179713)
      ·
        refine ⟨55464266752791658758884785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73952355670388878345179713 55464266752791658758884785)
        ·
          refine ⟨41598200064593744069163589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55464266752791658758884785 41598200064593744069163589)
          ·
            refine ⟨7799662512111327012968173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41598200064593744069163589 7799662512111327012968173)
            ·
              refine ⟨2924873442041747629863065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7799662512111327012968173 2924873442041747629863065)
              ·
                refine ⟨2193655081531310722397299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2924873442041747629863065 2193655081531310722397299)
                ·
                  refine ⟨3290482622296966083595949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193655081531310722397299 3290482622296966083595949)
                  ·
                    refine ⟨1233930983361362281348481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3290482622296966083595949 1233930983361362281348481)
                    ·
                      refine ⟨925448237521021711011361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1233930983361362281348481 925448237521021711011361)
                      ·
                        rfl

theorem cell23_1802304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 1, 3, 2].length) (baseStart_1802304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802304 prefixEnd_1802304 := by exact prefixLift 1802304
  have htrace : WordTrace (prefixWord ++ tailWord_1802304) baseStart_1802304 baseEnd_1802304 := by
    simpa [prefixWord, tailWord_1802304, baseEnd_1802304] using wordTrace_append hprefix tailTrace_1802304
  have hstable : (prefixWord ++ tailWord_1802304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802304).length < 2 ^ (prefixWord ++ tailWord_1802304).sum := by decide
  have hdescent : baseEnd_1802304 < baseStart_1802304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802330 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4]
def baseStart_1802330 : Nat := 118140960795 + 1802330 * 2 ^ 59
def prefixEnd_1802330 : Nat := 4983230072969 + 3 ^ 40 * 1802330 * 2
def baseEnd_1802330 : Nat := 925461588018038609286241

theorem tailTrace_1802330 : CollatzResearch.WordTrace tailWord_1802330 prefixEnd_1802330 925461588018038609286241 := by
  unfold tailWord_1802330
  simp only [CollatzResearch.WordTrace]
  refine ⟨16434093890118424575707111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43824250373649132201885629 16434093890118424575707111)
  ·
    refine ⟨24651140835177636863560667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16434093890118424575707111 24651140835177636863560667)
    ·
      refine ⟨36976711252766455295341001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24651140835177636863560667 36976711252766455295341001)
      ·
        refine ⟨27732533439574841471505751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36976711252766455295341001 27732533439574841471505751)
        ·
          refine ⟨41598800159362262207258627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27732533439574841471505751 41598800159362262207258627)
          ·
            refine ⟨62398200239043393310887941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41598800159362262207258627 62398200239043393310887941)
            ·
              refine ⟨11699662544820636245791489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62398200239043393310887941 11699662544820636245791489)
              ·
                refine ⟨8774746908615477184343617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11699662544820636245791489 8774746908615477184343617)
                ·
                  refine ⟨6581060181461607888257713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8774746908615477184343617 6581060181461607888257713)
                  ·
                    refine ⟨4935795136096205916193285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6581060181461607888257713 4935795136096205916193285)
                    ·
                      refine ⟨925461588018038609286241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4935795136096205916193285 925461588018038609286241)
                      ·
                        rfl

theorem cell23_1802330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_1802330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802330 prefixEnd_1802330 := by exact prefixLift 1802330
  have htrace : WordTrace (prefixWord ++ tailWord_1802330) baseStart_1802330 baseEnd_1802330 := by
    simpa [prefixWord, tailWord_1802330, baseEnd_1802330] using wordTrace_append hprefix tailTrace_1802330
  have hstable : (prefixWord ++ tailWord_1802330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802330).length < 2 ^ (prefixWord ++ tailWord_1802330).sum := by decide
  have hdescent : baseEnd_1802330 < baseStart_1802330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802427 : List Nat := [1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 3]
def baseStart_1802427 : Nat := 118140960795 + 1802427 * 2 ^ 59
def prefixEnd_1802427 : Nat := 4983230072969 + 3 ^ 40 * 1802427 * 2
def baseEnd_1802427 : Nat := 925511395641524729773295

theorem tailTrace_1802427 : CollatzResearch.WordTrace tailWord_1802427 prefixEnd_1802427 925511395641524729773295 := by
  unfold tailWord_1802427
  simp only [CollatzResearch.WordTrace]
  refine ⟨65739913441122283869109535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43826608960748189246073023 65739913441122283869109535)
  ·
    refine ⟨98609870161683425803664303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65739913441122283869109535 98609870161683425803664303)
    ·
      refine ⟨147914805242525138705496455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98609870161683425803664303 147914805242525138705496455)
      ·
        refine ⟨221872207863787708058244683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147914805242525138705496455 221872207863787708058244683)
        ·
          refine ⟨332808311795681562087367025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221872207863787708058244683 332808311795681562087367025)
          ·
            refine ⟨249606233846761171565525269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332808311795681562087367025 249606233846761171565525269)
            ·
              refine ⟨11700292211566929917133997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 249606233846761171565525269 11700292211566929917133997)
              ·
                refine ⟨4387609579337598718925249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11700292211566929917133997 4387609579337598718925249)
                ·
                  refine ⟨3290707184503199039193937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4387609579337598718925249 3290707184503199039193937)
                  ·
                    refine ⟨2468030388377399279395453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3290707184503199039193937 2468030388377399279395453)
                    ·
                      refine ⟨925511395641524729773295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2468030388377399279395453 925511395641524729773295)
                      ·
                        rfl

theorem cell23_1802427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 3].length) (baseStart_1802427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802427 prefixEnd_1802427 := by exact prefixLift 1802427
  have htrace : WordTrace (prefixWord ++ tailWord_1802427) baseStart_1802427 baseEnd_1802427 := by
    simpa [prefixWord, tailWord_1802427, baseEnd_1802427] using wordTrace_append hprefix tailTrace_1802427
  have hstable : (prefixWord ++ tailWord_1802427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802427).length < 2 ^ (prefixWord ++ tailWord_1802427).sum := by decide
  have hdescent : baseEnd_1802427 < baseStart_1802427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802474 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_1802474 : Nat := 118140960795 + 1802474 * 2 ^ 59
def prefixEnd_1802474 : Nat := 4983230072969 + 3 ^ 40 * 1802474 * 2
def baseEnd_1802474 : Nat := 925535529232286045885579

theorem tailTrace_1802474 : CollatzResearch.WordTrace tailWord_1802474 prefixEnd_1802474 925535529232286045885579 := by
  unfold tailWord_1802474
  simp only [CollatzResearch.WordTrace]
  refine ⟨16435406917988002724017619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43827751781301340597380317 16435406917988002724017619)
  ·
    refine ⟨24653110376982004086026429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16435406917988002724017619 24653110376982004086026429)
    ·
      refine ⟨9244916391368251532259911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24653110376982004086026429 9244916391368251532259911)
      ·
        refine ⟨13867374587052377298389867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9244916391368251532259911 13867374587052377298389867)
        ·
          refine ⟨20801061880578565947584801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13867374587052377298389867 20801061880578565947584801)
          ·
            refine ⟨15600796410433924460688601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20801061880578565947584801 15600796410433924460688601)
            ·
              refine ⟨11700597307825443345516451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15600796410433924460688601 11700597307825443345516451)
              ·
                refine ⟨17550895961738165018274677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11700597307825443345516451 17550895961738165018274677)
                ·
                  refine ⟨1645396496412952970463251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17550895961738165018274677 1645396496412952970463251)
                  ·
                    refine ⟨2468094744619429455694877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1645396496412952970463251 2468094744619429455694877)
                    ·
                      refine ⟨925535529232286045885579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2468094744619429455694877 925535529232286045885579)
                      ·
                        rfl

theorem cell23_1802474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_1802474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802474 prefixEnd_1802474 := by exact prefixLift 1802474
  have htrace : WordTrace (prefixWord ++ tailWord_1802474) baseStart_1802474 baseEnd_1802474 := by
    simpa [prefixWord, tailWord_1802474, baseEnd_1802474] using wordTrace_append hprefix tailTrace_1802474
  have hstable : (prefixWord ++ tailWord_1802474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802474).length < 2 ^ (prefixWord ++ tailWord_1802474).sum := by decide
  have hdescent : baseEnd_1802474 < baseStart_1802474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802517 : List Nat := [1, 3, 2, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_1802517 : Nat := 118140960795 + 1802517 * 2 ^ 59
def prefixEnd_1802517 : Nat := 4983230072969 + 3 ^ 40 * 1802517 * 2
def baseEnd_1802517 : Nat := 925557608900429377647881

theorem tailTrace_1802517 : CollatzResearch.WordTrace tailWord_1802517 prefixEnd_1802517 925557608900429377647881 := by
  unfold tailWord_1802517
  simp only [CollatzResearch.WordTrace]
  refine ⟨65743196010796229239885805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43828797340530819493257203 65743196010796229239885805)
  ·
    refine ⟨24653698504048585964957177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65743196010796229239885805 24653698504048585964957177)
    ·
      refine ⟨18490273878036439473717883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24653698504048585964957177 18490273878036439473717883)
      ·
        refine ⟨27735410817054659210576825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18490273878036439473717883 27735410817054659210576825)
        ·
          refine ⟨20801558112790994407932619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27735410817054659210576825 20801558112790994407932619)
          ·
            refine ⟨31202337169186491611898929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20801558112790994407932619 31202337169186491611898929)
            ·
              refine ⟨23401752876889868708924197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31202337169186491611898929 23401752876889868708924197)
              ·
                refine ⟨4387828664416850382923287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23401752876889868708924197 4387828664416850382923287)
                ·
                  refine ⟨6581742996625275574384931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4387828664416850382923287 6581742996625275574384931)
                  ·
                    refine ⟨9872614494937913361577397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6581742996625275574384931 9872614494937913361577397)
                    ·
                      refine ⟨925557608900429377647881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9872614494937913361577397 925557608900429377647881)
                      ·
                        rfl

theorem cell23_1802517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_1802517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802517 prefixEnd_1802517 := by exact prefixLift 1802517
  have htrace : WordTrace (prefixWord ++ tailWord_1802517) baseStart_1802517 baseEnd_1802517 := by
    simpa [prefixWord, tailWord_1802517, baseEnd_1802517] using wordTrace_append hprefix tailTrace_1802517
  have hstable : (prefixWord ++ tailWord_1802517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802517).length < 2 ^ (prefixWord ++ tailWord_1802517).sum := by decide
  have hdescent : baseEnd_1802517 < baseStart_1802517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802531 : List Nat := [1, 1, 1, 4, 2, 2, 3, 2, 3, 2, 2]
def baseStart_1802531 : Nat := 118140960795 + 1802531 * 2 ^ 59
def prefixEnd_1802531 : Nat := 4983230072969 + 3 ^ 40 * 1802531 * 2
def baseEnd_1802531 : Nat := 925564797629592322872817

theorem tailTrace_1802531 : CollatzResearch.WordTrace tailWord_1802531 prefixEnd_1802531 925564797629592322872817 := by
  unfold tailWord_1802531
  simp only [CollatzResearch.WordTrace]
  refine ⟨65743706632745509630895447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43829137755163673087263631 65743706632745509630895447)
  ·
    refine ⟨98615559949118264446343171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65743706632745509630895447 98615559949118264446343171)
    ·
      refine ⟨147923339923677396669514757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98615559949118264446343171 147923339923677396669514757)
      ·
        refine ⟨27735626235689511875534017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147923339923677396669514757 27735626235689511875534017)
        ·
          refine ⟨20801719676767133906650513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27735626235689511875534017 20801719676767133906650513)
          ·
            refine ⟨15601289757575350429987885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20801719676767133906650513 15601289757575350429987885)
            ·
              refine ⟨5850483659090756411245457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15601289757575350429987885 5850483659090756411245457)
              ·
                refine ⟨4387862744318067308434093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5850483659090756411245457 4387862744318067308434093)
                ·
                  refine ⟨1645448529119275240662785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4387862744318067308434093 1645448529119275240662785)
                  ·
                    refine ⟨1234086396839456430497089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1645448529119275240662785 1234086396839456430497089)
                    ·
                      refine ⟨925564797629592322872817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1234086396839456430497089 925564797629592322872817)
                      ·
                        rfl

theorem cell23_1802531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_1802531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802531 prefixEnd_1802531 := by exact prefixLift 1802531
  have htrace : WordTrace (prefixWord ++ tailWord_1802531) baseStart_1802531 baseEnd_1802531 := by
    simpa [prefixWord, tailWord_1802531, baseEnd_1802531] using wordTrace_append hprefix tailTrace_1802531
  have hstable : (prefixWord ++ tailWord_1802531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802531).length < 2 ^ (prefixWord ++ tailWord_1802531).sum := by decide
  have hdescent : baseEnd_1802531 < baseStart_1802531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802535 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_1802535 : Nat := 118140960795 + 1802535 * 2 ^ 59
def prefixEnd_1802535 : Nat := 4983230072969 + 3 ^ 40 * 1802535 * 2
def baseEnd_1802535 : Nat := 925566851552210307222799

theorem tailTrace_1802535 : CollatzResearch.WordTrace tailWord_1802535 prefixEnd_1802535 925566851552210307222799 := by
  unfold tailWord_1802535
  simp only [CollatzResearch.WordTrace]
  refine ⟨65743852524731018314041059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43829235016487345542694039 65743852524731018314041059)
  ·
    refine ⟨98615778787096527471061589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65743852524731018314041059 98615778787096527471061589)
    ·
      refine ⟨1155653657661287431301503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 98615778787096527471061589 1155653657661287431301503)
      ·
        refine ⟨1733480486491931146952255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1155653657661287431301503 1733480486491931146952255)
        ·
          refine ⟨2600220729737896720428383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1733480486491931146952255 2600220729737896720428383)
          ·
            refine ⟨3900331094606845080642575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600220729737896720428383 3900331094606845080642575)
            ·
              refine ⟨5850496641910267620963863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3900331094606845080642575 5850496641910267620963863)
              ·
                refine ⟨8775744962865401431445795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5850496641910267620963863 8775744962865401431445795)
                ·
                  refine ⟨13163617444298102147168693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8775744962865401431445795 13163617444298102147168693)
                  ·
                    refine ⟨1234089135402947076297065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13163617444298102147168693 1234089135402947076297065)
                    ·
                      refine ⟨925566851552210307222799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1234089135402947076297065 925566851552210307222799)
                      ·
                        rfl

theorem cell23_1802535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_1802535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802535 prefixEnd_1802535 := by exact prefixLift 1802535
  have htrace : WordTrace (prefixWord ++ tailWord_1802535) baseStart_1802535 baseEnd_1802535 := by
    simpa [prefixWord, tailWord_1802535, baseEnd_1802535] using wordTrace_append hprefix tailTrace_1802535
  have hstable : (prefixWord ++ tailWord_1802535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802535).length < 2 ^ (prefixWord ++ tailWord_1802535).sum := by decide
  have hdescent : baseEnd_1802535 < baseStart_1802535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802542 : List Nat := [4, 1, 3, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_1802542 : Nat := 118140960795 + 1802542 * 2 ^ 59
def prefixEnd_1802542 : Nat := 4983230072969 + 3 ^ 40 * 1802542 * 2
def baseEnd_1802542 : Nat := 925570445916791779835267

theorem tailTrace_1802542 : CollatzResearch.WordTrace tailWord_1802542 prefixEnd_1802542 925570445916791779835267 := by
  unfold tailWord_1802542
  simp only [CollatzResearch.WordTrace]
  refine ⟨8218013479463207313693235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43829405223803772339697253 8218013479463207313693235)
  ·
    refine ⟨12327020219194810970539853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8218013479463207313693235 12327020219194810970539853)
    ·
      refine ⟨4622632582198054113952445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12327020219194810970539853 4622632582198054113952445)
      ·
        refine ⟨1733487218324270292732167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4622632582198054113952445 1733487218324270292732167)
        ·
          refine ⟨2600230827486405439098251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1733487218324270292732167 2600230827486405439098251)
          ·
            refine ⟨3900346241229608158647377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600230827486405439098251 3900346241229608158647377)
            ·
              refine ⟨2925259680922206118985533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3900346241229608158647377 2925259680922206118985533)
              ·
                refine ⟨1096972380345827294619575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2925259680922206118985533 1096972380345827294619575)
                ·
                  refine ⟨1645458570518740941929363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1096972380345827294619575 1645458570518740941929363)
                  ·
                    refine ⟨2468187855778111412894045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1645458570518740941929363 2468187855778111412894045)
                    ·
                      refine ⟨925570445916791779835267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2468187855778111412894045 925570445916791779835267)
                      ·
                        rfl

theorem cell23_1802542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_1802542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802542 prefixEnd_1802542 := by exact prefixLift 1802542
  have htrace : WordTrace (prefixWord ++ tailWord_1802542) baseStart_1802542 baseEnd_1802542 := by
    simpa [prefixWord, tailWord_1802542, baseEnd_1802542] using wordTrace_append hprefix tailTrace_1802542
  have hstable : (prefixWord ++ tailWord_1802542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802542).length < 2 ^ (prefixWord ++ tailWord_1802542).sum := by decide
  have hdescent : baseEnd_1802542 < baseStart_1802542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802548 : List Nat := [2, 5, 1, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_1802548 : Nat := 118140960795 + 1802548 * 2 ^ 59
def prefixEnd_1802548 : Nat := 4983230072969 + 3 ^ 40 * 1802548 * 2
def baseEnd_1802548 : Nat := 925573526800718756360239

theorem tailTrace_1802548 : CollatzResearch.WordTrace tailWord_1802548 prefixEnd_1802548 925573526800718756360239 := by
  unfold tailWord_1802548
  simp only [CollatzResearch.WordTrace]
  refine ⟨32872163336841960767132149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43829551115789281022842865 32872163336841960767132149)
  ·
    refine ⟨3081765312828933821918639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32872163336841960767132149 3081765312828933821918639)
    ·
      refine ⟨4622647969243400732877959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3081765312828933821918639 4622647969243400732877959)
      ·
        refine ⟨6933971953865101099316939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4622647969243400732877959 6933971953865101099316939)
        ·
          refine ⟨10400957930797651648975409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6933971953865101099316939 10400957930797651648975409)
          ·
            refine ⟨7800718448098238736731557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10400957930797651648975409 7800718448098238736731557)
            ·
              refine ⟨1462634709018419763137167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7800718448098238736731557 1462634709018419763137167)
              ·
                refine ⟨2193952063527629644705751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1462634709018419763137167 2193952063527629644705751)
                ·
                  refine ⟨3290928095291444467058627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193952063527629644705751 3290928095291444467058627)
                  ·
                    refine ⟨4936392142937166700587941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3290928095291444467058627 4936392142937166700587941)
                    ·
                      refine ⟨925573526800718756360239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4936392142937166700587941 925573526800718756360239)
                      ·
                        rfl

theorem cell23_1802548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_1802548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802548 prefixEnd_1802548 := by exact prefixLift 1802548
  have htrace : WordTrace (prefixWord ++ tailWord_1802548) baseStart_1802548 baseEnd_1802548 := by
    simpa [prefixWord, tailWord_1802548, baseEnd_1802548] using wordTrace_append hprefix tailTrace_1802548
  have hstable : (prefixWord ++ tailWord_1802548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802548).length < 2 ^ (prefixWord ++ tailWord_1802548).sum := by decide
  have hdescent : baseEnd_1802548 < baseStart_1802548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802558 : List Nat := [4, 2, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_1802558 : Nat := 118140960795 + 1802558 * 2 ^ 59
def prefixEnd_1802558 : Nat := 4983230072969 + 3 ^ 40 * 1802558 * 2
def baseEnd_1802558 : Nat := 308526220535754572411731

theorem tailTrace_1802558 : CollatzResearch.WordTrace tailWord_1802558 prefixEnd_1802558 308526220535754572411731 := by
  unfold tailWord_1802558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8218086425455961655266041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43829794269098462161418885 8218086425455961655266041)
  ·
    refine ⟨6163564819091971241449531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8218086425455961655266041 6163564819091971241449531)
    ·
      refine ⟨9245347228637956862174297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6163564819091971241449531 9245347228637956862174297)
      ·
        refine ⟨6934010421478467646630723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9245347228637956862174297 6934010421478467646630723)
        ·
          refine ⟨10401015632217701469946085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6934010421478467646630723 10401015632217701469946085)
          ·
            refine ⟨1950190431040819025614891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10401015632217701469946085 1950190431040819025614891)
            ·
              refine ⟨2925285646561228538422337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1950190431040819025614891 2925285646561228538422337)
              ·
                refine ⟨2193964234920921403816753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2925285646561228538422337 2193964234920921403816753)
                ·
                  refine ⟨1645473176190691052862565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2193964234920921403816753 1645473176190691052862565)
                  ·
                    refine ⟨308526220535754572411731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1645473176190691052862565 308526220535754572411731)
                    ·
                      rfl

theorem cell23_1802558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_1802558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802558 prefixEnd_1802558 := by exact prefixLift 1802558
  have htrace : WordTrace (prefixWord ++ tailWord_1802558) baseStart_1802558 baseEnd_1802558 := by
    simpa [prefixWord, tailWord_1802558, baseEnd_1802558] using wordTrace_append hprefix tailTrace_1802558
  have hstable : (prefixWord ++ tailWord_1802558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802558).length < 2 ^ (prefixWord ++ tailWord_1802558).sum := by decide
  have hdescent : baseEnd_1802558 < baseStart_1802558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802574 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2]
def baseStart_1802574 : Nat := 118140960795 + 1802574 * 2 ^ 59
def prefixEnd_1802574 : Nat := 4983230072969 + 3 ^ 40 * 1802574 * 2
def baseEnd_1802574 : Nat := 925586877297735654635119

theorem tailTrace_1802574 : CollatzResearch.WordTrace tailWord_1802574 prefixEnd_1802574 925586877297735654635119 := by
  unfold tailWord_1802574
  simp only [CollatzResearch.WordTrace]
  refine ⟨8218159371448715996838847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43830183314393151983140517 8218159371448715996838847)
  ·
    refine ⟨12327239057173073995258271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8218159371448715996838847 12327239057173073995258271)
    ·
      refine ⟨18490858585759610992887407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12327239057173073995258271 18490858585759610992887407)
      ·
        refine ⟨27736287878639416489331111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18490858585759610992887407 27736287878639416489331111)
        ·
          refine ⟨41604431817959124733996667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27736287878639416489331111 41604431817959124733996667)
          ·
            refine ⟨62406647726938687100995001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41604431817959124733996667 62406647726938687100995001)
            ·
              refine ⟨46804985795204015325746251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62406647726938687100995001 46804985795204015325746251)
              ·
                refine ⟨70207478692806022988619377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46804985795204015325746251 70207478692806022988619377)
                ·
                  refine ⟨52655609019604517241464533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70207478692806022988619377 52655609019604517241464533)
                  ·
                    refine ⟨1234115836396980872846825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52655609019604517241464533 1234115836396980872846825)
                    ·
                      refine ⟨925586877297735654635119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1234115836396980872846825 925586877297735654635119)
                      ·
                        rfl

theorem cell23_1802574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_1802574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802574 prefixEnd_1802574 := by exact prefixLift 1802574
  have htrace : WordTrace (prefixWord ++ tailWord_1802574) baseStart_1802574 baseEnd_1802574 := by
    simpa [prefixWord, tailWord_1802574, baseEnd_1802574] using wordTrace_append hprefix tailTrace_1802574
  have hstable : (prefixWord ++ tailWord_1802574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802574).length < 2 ^ (prefixWord ++ tailWord_1802574).sum := by decide
  have hdescent : baseEnd_1802574 < baseStart_1802574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802588 : List Nat := [2, 2, 4, 3, 1, 2, 2, 7]
def baseStart_1802588 : Nat := 118140960795 + 1802588 * 2 ^ 59
def prefixEnd_1802588 : Nat := 4983230072969 + 3 ^ 40 * 1802588 * 2
def baseEnd_1802588 : Nat := 34281261704699948142965

theorem tailTrace_1802588 : CollatzResearch.WordTrace tailWord_1802588 prefixEnd_1802588 34281261704699948142965 := by
  unfold tailWord_1802588
  simp only [CollatzResearch.WordTrace]
  refine ⟨32872892796769504182860209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43830523729026005577146945 32872892796769504182860209)
  ·
    refine ⟨24654669597577128137145157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32872892796769504182860209 24654669597577128137145157)
    ·
      refine ⟨4622750549545711525714717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24654669597577128137145157 4622750549545711525714717)
      ·
        refine ⟨1733531456079641822143019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4622750549545711525714717 1733531456079641822143019)
        ·
          refine ⟨2600297184119462733214529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1733531456079641822143019 2600297184119462733214529)
          ·
            refine ⟨1950222888089597049910897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2600297184119462733214529 1950222888089597049910897)
            ·
              refine ⟨1462667166067197787433173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1950222888089597049910897 1462667166067197787433173)
              ·
                refine ⟨34281261704699948142965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1462667166067197787433173 34281261704699948142965)
                ·
                  rfl

theorem cell23_1802588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 7].length) (baseStart_1802588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802588 prefixEnd_1802588 := by exact prefixLift 1802588
  have htrace : WordTrace (prefixWord ++ tailWord_1802588) baseStart_1802588 baseEnd_1802588 := by
    simpa [prefixWord, tailWord_1802588, baseEnd_1802588] using wordTrace_append hprefix tailTrace_1802588
  have hstable : (prefixWord ++ tailWord_1802588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802588).length < 2 ^ (prefixWord ++ tailWord_1802588).sum := by decide
  have hdescent : baseEnd_1802588 < baseStart_1802588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802591 : List Nat := [1, 1, 2, 3, 1, 2, 3, 4, 1, 3, 2]
def baseStart_1802591 : Nat := 118140960795 + 1802591 * 2 ^ 59
def prefixEnd_1802591 : Nat := 4983230072969 + 3 ^ 40 * 1802591 * 2
def baseEnd_1802591 : Nat := 925595606468862088122541

theorem tailTrace_1802591 : CollatzResearch.WordTrace tailWord_1802591 prefixEnd_1802591 925595606468862088122541 := by
  unfold tailWord_1802591
  simp only [CollatzResearch.WordTrace]
  refine ⟨65745895012528139878079627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43830596675018759918719751 65745895012528139878079627)
  ·
    refine ⟨98618842518792209817119441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65745895012528139878079627 98618842518792209817119441)
    ·
      refine ⟨73964131889094157362839581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98618842518792209817119441 73964131889094157362839581)
      ·
        refine ⟨27736549458410309011064843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73964131889094157362839581 27736549458410309011064843)
        ·
          refine ⟨41604824187615463516597265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27736549458410309011064843 41604824187615463516597265)
          ·
            refine ⟨31203618140711597637447949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41604824187615463516597265 31203618140711597637447949)
            ·
              refine ⟨11701356802766849114042981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31203618140711597637447949 11701356802766849114042981)
              ·
                refine ⟨2194004400518784208883059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11701356802766849114042981 2194004400518784208883059)
                ·
                  refine ⟨3291006600778176313324589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2194004400518784208883059 3291006600778176313324589)
                  ·
                    refine ⟨1234127475291816117496721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3291006600778176313324589 1234127475291816117496721)
                    ·
                      refine ⟨925595606468862088122541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1234127475291816117496721 925595606468862088122541)
                      ·
                        rfl

theorem cell23_1802591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_1802591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802591 prefixEnd_1802591 := by exact prefixLift 1802591
  have htrace : WordTrace (prefixWord ++ tailWord_1802591) baseStart_1802591 baseEnd_1802591 := by
    simpa [prefixWord, tailWord_1802591, baseEnd_1802591] using wordTrace_append hprefix tailTrace_1802591
  have hstable : (prefixWord ++ tailWord_1802591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802591).length < 2 ^ (prefixWord ++ tailWord_1802591).sum := by decide
  have hdescent : baseEnd_1802591 < baseStart_1802591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802594 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1802594 : Nat := 118140960795 + 1802594 * 2 ^ 59
def prefixEnd_1802594 : Nat := 4983230072969 + 3 ^ 40 * 1802594 * 2
def baseEnd_1802594 : Nat := 925597146910825576385027

theorem tailTrace_1802594 : CollatzResearch.WordTrace tailWord_1802594 prefixEnd_1802594 925597146910825576385027 := by
  unfold tailWord_1802594
  simp only [CollatzResearch.WordTrace]
  refine ⟨16436501107879317847609709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43830669621011514260292557 16436501107879317847609709)
  ·
    refine ⟨6163687915454744192853641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16436501107879317847609709 6163687915454744192853641)
    ·
      refine ⟨4622765936591058144640231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6163687915454744192853641 4622765936591058144640231)
      ·
        refine ⟨6934148904886587216960347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4622765936591058144640231 6934148904886587216960347)
        ·
          refine ⟨10401223357329880825440521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6934148904886587216960347 10401223357329880825440521)
          ·
            refine ⟨7800917517997410619080391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10401223357329880825440521 7800917517997410619080391)
            ·
              refine ⟨11701376276996115928620587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7800917517997410619080391 11701376276996115928620587)
              ·
                refine ⟨17552064415494173892930881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11701376276996115928620587 17552064415494173892930881)
                ·
                  refine ⟨13164048311620630419698161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17552064415494173892930881 13164048311620630419698161)
                  ·
                    refine ⟨9873036233715472814773621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13164048311620630419698161 9873036233715472814773621)
                    ·
                      refine ⟨925597146910825576385027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9873036233715472814773621 925597146910825576385027)
                      ·
                        rfl

theorem cell23_1802594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1802594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802594 prefixEnd_1802594 := by exact prefixLift 1802594
  have htrace : WordTrace (prefixWord ++ tailWord_1802594) baseStart_1802594 baseEnd_1802594 := by
    simpa [prefixWord, tailWord_1802594, baseEnd_1802594] using wordTrace_append hprefix tailTrace_1802594
  have hstable : (prefixWord ++ tailWord_1802594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802594).length < 2 ^ (prefixWord ++ tailWord_1802594).sum := by decide
  have hdescent : baseEnd_1802594 < baseStart_1802594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802674 : List Nat := [3, 2, 1, 1, 1, 1, 3, 4, 2, 5]
def baseStart_1802674 : Nat := 118140960795 + 1802674 * 2 ^ 59
def prefixEnd_1802674 : Nat := 4983230072969 + 3 ^ 40 * 1802674 * 2
def baseEnd_1802674 : Nat := 308546075121061754461553

theorem tailTrace_1802674 : CollatzResearch.WordTrace tailWord_1802674 prefixEnd_1802674 308546075121061754461553 := by
  unfold tailWord_1802674
  simp only [CollatzResearch.WordTrace]
  refine ⟨16437230567806861263337769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43832614847484963368900717 16437230567806861263337769)
  ·
    refine ⟨12327922925855145947503327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16437230567806861263337769 12327922925855145947503327)
    ·
      refine ⟨18491884388782718921254991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12327922925855145947503327 18491884388782718921254991)
      ·
        refine ⟨27737826583174078381882487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18491884388782718921254991 27737826583174078381882487)
        ·
          refine ⟨41606739874761117572823731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27737826583174078381882487 41606739874761117572823731)
          ·
            refine ⟨62410109812141676359235597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41606739874761117572823731 62410109812141676359235597)
            ·
              refine ⟨23403791179553128634713349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62410109812141676359235597 23403791179553128634713349)
              ·
                refine ⟨4388210846166211619008753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23403791179553128634713349 4388210846166211619008753)
                ·
                  refine ⟨3291158134624658714256565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4388210846166211619008753 3291158134624658714256565)
                  ·
                    refine ⟨308546075121061754461553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3291158134624658714256565 308546075121061754461553)
                    ·
                      rfl

theorem cell23_1802674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_1802674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802674 prefixEnd_1802674 := by exact prefixLift 1802674
  have htrace : WordTrace (prefixWord ++ tailWord_1802674) baseStart_1802674 baseEnd_1802674 := by
    simpa [prefixWord, tailWord_1802674, baseEnd_1802674] using wordTrace_append hprefix tailTrace_1802674
  have hstable : (prefixWord ++ tailWord_1802674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802674).length < 2 ^ (prefixWord ++ tailWord_1802674).sum := by decide
  have hdescent : baseEnd_1802674 < baseStart_1802674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802681 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 2, 5, 2]
def baseStart_1802681 : Nat := 118140960795 + 1802681 * 2 ^ 59
def prefixEnd_1802681 : Nat := 4983230072969 + 3 ^ 40 * 1802681 * 2
def baseEnd_1802681 : Nat := 925641819727766735997127

theorem tailTrace_1802681 : CollatzResearch.WordTrace tailWord_1802681 prefixEnd_1802681 925641819727766735997127 := by
  unfold tailWord_1802681
  simp only [CollatzResearch.WordTrace]
  refine ⟨65749177582202085248855897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43832785054801390165903931 65749177582202085248855897)
  ·
    refine ⟨49311883186651563936641923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65749177582202085248855897 49311883186651563936641923)
    ·
      refine ⟨73967824779977345904962885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49311883186651563936641923 73967824779977345904962885)
      ·
        refine ⟨13868967146245752357180541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73967824779977345904962885 13868967146245752357180541)
        ·
          refine ⟨5200862679842157133942703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13868967146245752357180541 5200862679842157133942703)
          ·
            refine ⟨7801294019763235700914055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5200862679842157133942703 7801294019763235700914055)
            ·
              refine ⟨11701941029644853551371083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7801294019763235700914055 11701941029644853551371083)
              ·
                refine ⟨17552911544467280327056625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11701941029644853551371083 17552911544467280327056625)
                ·
                  refine ⟨13164683658350460245292469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17552911544467280327056625 13164683658350460245292469)
                  ·
                    refine ⟨1234189092970355647996169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13164683658350460245292469 1234189092970355647996169)
                    ·
                      refine ⟨925641819727766735997127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1234189092970355647996169 925641819727766735997127)
                      ·
                        rfl

theorem cell23_1802681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_1802681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802681 prefixEnd_1802681 := by exact prefixLift 1802681
  have htrace : WordTrace (prefixWord ++ tailWord_1802681) baseStart_1802681 baseEnd_1802681 := by
    simpa [prefixWord, tailWord_1802681, baseEnd_1802681] using wordTrace_append hprefix tailTrace_1802681
  have hstable : (prefixWord ++ tailWord_1802681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802681).length < 2 ^ (prefixWord ++ tailWord_1802681).sum := by decide
  have hdescent : baseEnd_1802681 < baseStart_1802681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802687 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 4, 8]
def baseStart_1802687 : Nat := 118140960795 + 1802687 * 2 ^ 59
def prefixEnd_1802687 : Nat := 4983230072969 + 3 ^ 40 * 1802687 * 2
def baseEnd_1802687 : Nat := 308548300203897904174033

theorem tailTrace_1802687 : CollatzResearch.WordTrace tailWord_1802687 prefixEnd_1802687 308548300203897904174033 := by
  unfold tailWord_1802687
  simp only [CollatzResearch.WordTrace]
  refine ⟨65749396420180348273574315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43832930946786898849049543 65749396420180348273574315)
  ·
    refine ⟨98624094630270522410361473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65749396420180348273574315 98624094630270522410361473)
    ·
      refine ⟨73968070972702891807771105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98624094630270522410361473 73968070972702891807771105)
      ·
        refine ⟨55476053229527168855828329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73968070972702891807771105 55476053229527168855828329)
        ·
          refine ⟨41607039922145376641871247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55476053229527168855828329 41607039922145376641871247)
          ·
            refine ⟨62410559883218064962806871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41607039922145376641871247 62410559883218064962806871)
            ·
              refine ⟨93615839824827097444210307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62410559883218064962806871 93615839824827097444210307)
              ·
                refine ⟨140423759737240646166315461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93615839824827097444210307 140423759737240646166315461)
                ·
                  refine ⟨26329454950732621156184149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140423759737240646166315461 26329454950732621156184149)
                  ·
                    refine ⟨308548300203897904174033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26329454950732621156184149 308548300203897904174033)
                    ·
                      rfl

theorem cell23_1802687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 8].length) (baseStart_1802687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802687 prefixEnd_1802687 := by exact prefixLift 1802687
  have htrace : WordTrace (prefixWord ++ tailWord_1802687) baseStart_1802687 baseEnd_1802687 := by
    simpa [prefixWord, tailWord_1802687, baseEnd_1802687] using wordTrace_append hprefix tailTrace_1802687
  have hstable : (prefixWord ++ tailWord_1802687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802687).length < 2 ^ (prefixWord ++ tailWord_1802687).sum := by decide
  have hdescent : baseEnd_1802687 < baseStart_1802687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802708 : List Nat := [2, 4, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_1802708 : Nat := 118140960795 + 1802708 * 2 ^ 59
def prefixEnd_1802708 : Nat := 4983230072969 + 3 ^ 40 * 1802708 * 2
def baseEnd_1802708 : Nat := 308551894568479376786501

theorem tailTrace_1802708 : CollatzResearch.WordTrace tailWord_1802708 prefixEnd_1802708 308551894568479376786501 := by
  unfold tailWord_1802708
  simp only [CollatzResearch.WordTrace]
  refine ⟨32875081176552134430044389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43833441568736179240059185 32875081176552134430044389)
  ·
    refine ⟨6164077720603525205633323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32875081176552134430044389 6164077720603525205633323)
    ·
      refine ⟨9246116580905287808449985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6164077720603525205633323 9246116580905287808449985)
      ·
        refine ⟨6934587435678965856337489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9246116580905287808449985 6934587435678965856337489)
        ·
          refine ⟨5200940576759224392253117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6934587435678965856337489 5200940576759224392253117)
          ·
            refine ⟨1950352716284709147094919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5200940576759224392253117 1950352716284709147094919)
            ·
              refine ⟨2925529074427063720642379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1950352716284709147094919 2925529074427063720642379)
              ·
                refine ⟨4388293611640595580963569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2925529074427063720642379 4388293611640595580963569)
                ·
                  refine ⟨3291220208730446685722677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4388293611640595580963569 3291220208730446685722677)
                  ·
                    refine ⟨308551894568479376786501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3291220208730446685722677 308551894568479376786501)
                    ·
                      rfl

theorem cell23_1802708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_1802708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802708 prefixEnd_1802708 := by exact prefixLift 1802708
  have htrace : WordTrace (prefixWord ++ tailWord_1802708) baseStart_1802708 baseEnd_1802708 := by
    simpa [prefixWord, tailWord_1802708, baseEnd_1802708] using wordTrace_append hprefix tailTrace_1802708
  have hstable : (prefixWord ++ tailWord_1802708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802708).length < 2 ^ (prefixWord ++ tailWord_1802708).sum := by decide
  have hdescent : baseEnd_1802708 < baseStart_1802708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802751 : List Nat := [1, 1, 2, 2, 1, 2, 7, 1, 6]
def baseStart_1802751 : Nat := 118140960795 + 1802751 * 2 ^ 59
def prefixEnd_1802751 : Nat := 4983230072969 + 3 ^ 40 * 1802751 * 2
def baseEnd_1802751 : Nat := 102853084819286829124645

theorem tailTrace_1802751 : CollatzResearch.WordTrace tailWord_1802751 prefixEnd_1802751 102853084819286829124645 := by
  unfold tailWord_1802751
  simp only [CollatzResearch.WordTrace]
  refine ⟨65751730691948487203904107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43834487127965658135936071 65751730691948487203904107)
  ·
    refine ⟨98627596037922730805856161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65751730691948487203904107 98627596037922730805856161)
    ·
      refine ⟨73970697028442048104392121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98627596037922730805856161 73970697028442048104392121)
      ·
        refine ⟨55478022771331536078294091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73970697028442048104392121 55478022771331536078294091)
        ·
          refine ⟨83217034156997304117441137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55478022771331536078294091 83217034156997304117441137)
          ·
            refine ⟨62412775617747978088080853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83217034156997304117441137 62412775617747978088080853)
            ·
              refine ⟨1462799428540968236439395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 62412775617747978088080853 1462799428540968236439395)
              ·
                refine ⟨2194199142811452354659093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1462799428540968236439395 2194199142811452354659093)
                ·
                  refine ⟨102853084819286829124645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2194199142811452354659093 102853084819286829124645)
                  ·
                    rfl

theorem cell23_1802751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 6].length) (baseStart_1802751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802751 prefixEnd_1802751 := by exact prefixLift 1802751
  have htrace : WordTrace (prefixWord ++ tailWord_1802751) baseStart_1802751 baseEnd_1802751 := by
    simpa [prefixWord, tailWord_1802751, baseEnd_1802751] using wordTrace_append hprefix tailTrace_1802751
  have hstable : (prefixWord ++ tailWord_1802751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802751).length < 2 ^ (prefixWord ++ tailWord_1802751).sum := by decide
  have hdescent : baseEnd_1802751 < baseStart_1802751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802761 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 5, 1, 3]
def baseStart_1802761 : Nat := 118140960795 + 1802761 * 2 ^ 59
def prefixEnd_1802761 : Nat := 4983230072969 + 3 ^ 40 * 1802761 * 2
def baseEnd_1802761 : Nat := 925682898180126422996759

theorem tailTrace_1802761 : CollatzResearch.WordTrace tailWord_1802761 prefixEnd_1802761 925682898180126422996759 := by
  unfold tailWord_1802761
  simp only [CollatzResearch.WordTrace]
  refine ⟨65752095421912258911768137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43834730281274839274512091 65752095421912258911768137)
  ·
    refine ⟨49314071566434194183826103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65752095421912258911768137 49314071566434194183826103)
    ·
      refine ⟨73971107349651291275739155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49314071566434194183826103 73971107349651291275739155)
      ·
        refine ⟨110956661024476936913608733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73971107349651291275739155 110956661024476936913608733)
        ·
          refine ⟨41608747884178851342603275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110956661024476936913608733 41608747884178851342603275)
          ·
            refine ⟨62413121826268277013904913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41608747884178851342603275 62413121826268277013904913)
            ·
              refine ⟨46809841369701207760428685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62413121826268277013904913 46809841369701207760428685)
              ·
                refine ⟨17553690513637952910160757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46809841369701207760428685 17553690513637952910160757)
                ·
                  refine ⟨1645658485653558085327571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17553690513637952910160757 1645658485653558085327571)
                  ·
                    refine ⟨2468487728480337127991357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1645658485653558085327571 2468487728480337127991357)
                    ·
                      refine ⟨925682898180126422996759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2468487728480337127991357 925682898180126422996759)
                      ·
                        rfl

theorem cell23_1802761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 1, 3].length) (baseStart_1802761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802761 prefixEnd_1802761 := by exact prefixLift 1802761
  have htrace : WordTrace (prefixWord ++ tailWord_1802761) baseStart_1802761 baseEnd_1802761 := by
    simpa [prefixWord, tailWord_1802761, baseEnd_1802761] using wordTrace_append hprefix tailTrace_1802761
  have hstable : (prefixWord ++ tailWord_1802761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802761).length < 2 ^ (prefixWord ++ tailWord_1802761).sum := by decide
  have hdescent : baseEnd_1802761 < baseStart_1802761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802765 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_1802765 : Nat := 118140960795 + 1802765 * 2 ^ 59
def prefixEnd_1802765 : Nat := 4983230072969 + 3 ^ 40 * 1802765 * 2
def baseEnd_1802765 : Nat := 925684952102744407346741

theorem tailTrace_1802765 : CollatzResearch.WordTrace tailWord_1802765 prefixEnd_1802765 925684952102744407346741 := by
  unfold tailWord_1802765
  simp only [CollatzResearch.WordTrace]
  refine ⟨65752241313897767594913749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43834827542598511729942499 65752241313897767594913749)
  ·
    refine ⟨1541068155794478928005791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 65752241313897767594913749 1541068155794478928005791)
    ·
      refine ⟨2311602233691718392008687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1541068155794478928005791 2311602233691718392008687)
      ·
        refine ⟨3467403350537577588013031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2311602233691718392008687 3467403350537577588013031)
        ·
          refine ⟨5201105025806366382019547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3467403350537577588013031 5201105025806366382019547)
          ·
            refine ⟨7801657538709549573029321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5201105025806366382019547 7801657538709549573029321)
            ·
              refine ⟨5851243154032162179771991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7801657538709549573029321 5851243154032162179771991)
              ·
                refine ⟨8776864731048243269657987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5851243154032162179771991 8776864731048243269657987)
                ·
                  refine ⟨13165297096572364904486981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8776864731048243269657987 13165297096572364904486981)
                  ·
                    refine ⟨2468493205607318419591309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13165297096572364904486981 2468493205607318419591309)
                    ·
                      refine ⟨925684952102744407346741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2468493205607318419591309 925684952102744407346741)
                      ·
                        rfl

theorem cell23_1802765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_1802765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802765 prefixEnd_1802765 := by exact prefixLift 1802765
  have htrace : WordTrace (prefixWord ++ tailWord_1802765) baseStart_1802765 baseEnd_1802765 := by
    simpa [prefixWord, tailWord_1802765, baseEnd_1802765] using wordTrace_append hprefix tailTrace_1802765
  have hstable : (prefixWord ++ tailWord_1802765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802765).length < 2 ^ (prefixWord ++ tailWord_1802765).sum := by decide
  have hdescent : baseEnd_1802765 < baseStart_1802765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802771 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 1, 5, 2]
def baseStart_1802771 : Nat := 118140960795 + 1802771 * 2 ^ 59
def prefixEnd_1802771 : Nat := 4983230072969 + 3 ^ 40 * 1802771 * 2
def baseEnd_1802771 : Nat := 925688032986671383871713

theorem tailTrace_1802771 : CollatzResearch.WordTrace tailWord_1802771 prefixEnd_1802771 925688032986671383871713 := by
  unfold tailWord_1802771
  simp only [CollatzResearch.WordTrace]
  refine ⟨65752460151876030619632167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43834973434584020413088111 65752460151876030619632167)
  ·
    refine ⟨98628690227814045929448251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65752460151876030619632167 98628690227814045929448251)
    ·
      refine ⟨147943035341721068894172377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98628690227814045929448251 147943035341721068894172377)
      ·
        refine ⟨110957276506290801670629283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147943035341721068894172377 110957276506290801670629283)
        ·
          refine ⟨166435914759436202505943925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110957276506290801670629283 166435914759436202505943925)
          ·
            refine ⟨15603367008697143984932243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166435914759436202505943925 15603367008697143984932243)
            ·
              refine ⟨23405050513045715977398365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15603367008697143984932243 23405050513045715977398365)
              ·
                refine ⟨8776893942392143491524387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23405050513045715977398365 8776893942392143491524387)
                ·
                  refine ⟨13165340913588215237286581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8776893942392143491524387 13165340913588215237286581)
                  ·
                    refine ⟨1234250710648895178495617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13165340913588215237286581 1234250710648895178495617)
                    ·
                      refine ⟨925688032986671383871713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1234250710648895178495617 925688032986671383871713)
                      ·
                        rfl

theorem cell23_1802771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 5, 2].length) (baseStart_1802771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802771 prefixEnd_1802771 := by exact prefixLift 1802771
  have htrace : WordTrace (prefixWord ++ tailWord_1802771) baseStart_1802771 baseEnd_1802771 := by
    simpa [prefixWord, tailWord_1802771, baseEnd_1802771] using wordTrace_append hprefix tailTrace_1802771
  have hstable : (prefixWord ++ tailWord_1802771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802771).length < 2 ^ (prefixWord ++ tailWord_1802771).sum := by decide
  have hdescent : baseEnd_1802771 < baseStart_1802771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802772 : List Nat := [2, 4, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_1802772 : Nat := 118140960795 + 1802772 * 2 ^ 59
def prefixEnd_1802772 : Nat := 4983230072969 + 3 ^ 40 * 1802772 * 2
def baseEnd_1802772 : Nat := 308562848822441959986403

theorem tailTrace_1802772 : CollatzResearch.WordTrace tailWord_1802772 prefixEnd_1802772 308562848822441959986403 := by
  unfold tailWord_1802772
  simp only [CollatzResearch.WordTrace]
  refine ⟨32876248312436203895209285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43834997749914938526945713 32876248312436203895209285)
  ·
    refine ⟨6164296558581788230351741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32876248312436203895209285 6164296558581788230351741)
    ·
      refine ⟨2311611209468170586381903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6164296558581788230351741 2311611209468170586381903)
      ·
        refine ⟨3467416814202255879572855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2311611209468170586381903 3467416814202255879572855)
        ·
          refine ⟨5201125221303383819359283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3467416814202255879572855 5201125221303383819359283)
          ·
            refine ⟨7801687831955075729038925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5201125221303383819359283 7801687831955075729038925)
            ·
              refine ⟨2925632936983153398389597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7801687831955075729038925 2925632936983153398389597)
              ·
                refine ⟨1097112351368682524396099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2925632936983153398389597 1097112351368682524396099)
                ·
                  refine ⟨1645668527053023786594149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097112351368682524396099 1645668527053023786594149)
                  ·
                    refine ⟨308562848822441959986403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1645668527053023786594149 308562848822441959986403)
                    ·
                      rfl

theorem cell23_1802772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_1802772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802772 prefixEnd_1802772 := by exact prefixLift 1802772
  have htrace : WordTrace (prefixWord ++ tailWord_1802772) baseStart_1802772 baseEnd_1802772 := by
    simpa [prefixWord, tailWord_1802772, baseEnd_1802772] using wordTrace_append hprefix tailTrace_1802772
  have hstable : (prefixWord ++ tailWord_1802772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802772).length < 2 ^ (prefixWord ++ tailWord_1802772).sum := by decide
  have hdescent : baseEnd_1802772 < baseStart_1802772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802822 : List Nat := [6, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_1802822 : Nat := 118140960795 + 1802822 * 2 ^ 59
def prefixEnd_1802822 : Nat := 4983230072969 + 3 ^ 40 * 1802822 * 2
def baseEnd_1802822 : Nat := 925714220500050684333979

theorem tailTrace_1802822 : CollatzResearch.WordTrace tailWord_1802822 prefixEnd_1802822 925714220500050684333979 := by
  unfold tailWord_1802822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2054822508584102072804335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43836213516460844219825813 2054822508584102072804335)
  ·
    refine ⟨3082233762876153109206503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2054822508584102072804335 3082233762876153109206503)
    ·
      refine ⟨4623350644314229663809755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3082233762876153109206503 4623350644314229663809755)
      ·
        refine ⟨6935025966471344495714633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4623350644314229663809755 6935025966471344495714633)
        ·
          refine ⟨5201269474853508371785975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6935025966471344495714633 5201269474853508371785975)
          ·
            refine ⟨7801904212280262557678963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5201269474853508371785975 7801904212280262557678963)
            ·
              refine ⟨11702856318420393836518445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7801904212280262557678963 11702856318420393836518445)
              ·
                refine ⟨4388571119407647688694417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11702856318420393836518445 4388571119407647688694417)
                ·
                  refine ⟨3291428339555735766520813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4388571119407647688694417 3291428339555735766520813)
                  ·
                    refine ⟨1234285627333400912445305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3291428339555735766520813 1234285627333400912445305)
                    ·
                      refine ⟨925714220500050684333979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1234285627333400912445305 925714220500050684333979)
                      ·
                        rfl

theorem cell23_1802822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_1802822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802822 prefixEnd_1802822 := by exact prefixLift 1802822
  have htrace : WordTrace (prefixWord ++ tailWord_1802822) baseStart_1802822 baseEnd_1802822 := by
    simpa [prefixWord, tailWord_1802822, baseEnd_1802822] using wordTrace_append hprefix tailTrace_1802822
  have hstable : (prefixWord ++ tailWord_1802822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802822).length < 2 ^ (prefixWord ++ tailWord_1802822).sum := by decide
  have hdescent : baseEnd_1802822 < baseStart_1802822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802851 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 3]
def baseStart_1802851 : Nat := 118140960795 + 1802851 * 2 ^ 59
def prefixEnd_1802851 : Nat := 4983230072969 + 3 ^ 40 * 1802851 * 2
def baseEnd_1802851 : Nat := 925729111439031070871345

theorem tailTrace_1802851 : CollatzResearch.WordTrace tailWord_1802851 prefixEnd_1802851 925729111439031070871345 := by
  unfold tailWord_1802851
  simp only [CollatzResearch.WordTrace]
  refine ⟨65755377991586204282544407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43836918661057469521696271 65755377991586204282544407)
  ·
    refine ⟨98633066987379306423816611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65755377991586204282544407 98633066987379306423816611)
    ·
      refine ⟨147949600481068959635724917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98633066987379306423816611 147949600481068959635724917)
      ·
        refine ⟨13870275045100214965849211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147949600481068959635724917 13870275045100214965849211)
        ·
          refine ⟨20805412567650322448773817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13870275045100214965849211 20805412567650322448773817)
          ·
            refine ⟨15604059425737741836580363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20805412567650322448773817 15604059425737741836580363)
            ·
              refine ⟨23406089138606612754870545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15604059425737741836580363 23406089138606612754870545)
              ·
                refine ⟨17554566853954959566152909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23406089138606612754870545 17554566853954959566152909)
                ·
                  refine ⟨6582962570233109837307341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17554566853954959566152909 6582962570233109837307341)
                  ·
                    refine ⟨2468610963837416188990253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6582962570233109837307341 2468610963837416188990253)
                    ·
                      refine ⟨925729111439031070871345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2468610963837416188990253 925729111439031070871345)
                      ·
                        rfl

theorem cell23_1802851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_1802851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802851 prefixEnd_1802851 := by exact prefixLift 1802851
  have htrace : WordTrace (prefixWord ++ tailWord_1802851) baseStart_1802851 baseEnd_1802851 := by
    simpa [prefixWord, tailWord_1802851, baseEnd_1802851] using wordTrace_append hprefix tailTrace_1802851
  have hstable : (prefixWord ++ tailWord_1802851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802851).length < 2 ^ (prefixWord ++ tailWord_1802851).sum := by decide
  have hdescent : baseEnd_1802851 < baseStart_1802851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802852 : List Nat := [2, 3, 1, 1, 2, 2, 3, 4, 1, 2, 2]
def baseStart_1802852 : Nat := 118140960795 + 1802852 * 2 ^ 59
def prefixEnd_1802852 : Nat := 4983230072969 + 3 ^ 40 * 1802852 * 2
def baseEnd_1802852 : Nat := 925729624919685566958841

theorem tailTrace_1802852 : CollatzResearch.WordTrace tailWord_1802852 prefixEnd_1802852 925729624919685566958841 := by
  unfold tailWord_1802852
  simp only [CollatzResearch.WordTrace]
  refine ⟨32877707232291290726665405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43836942976388387635553873 32877707232291290726665405)
  ·
    refine ⟨12329140212109234022499527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32877707232291290726665405 12329140212109234022499527)
    ·
      refine ⟨18493710318163851033749291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12329140212109234022499527 18493710318163851033749291)
      ·
        refine ⟨27740565477245776550623937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18493710318163851033749291 27740565477245776550623937)
        ·
          refine ⟨20805424107934332412967953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27740565477245776550623937 20805424107934332412967953)
          ·
            refine ⟨15604068080950749309725965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20805424107934332412967953 15604068080950749309725965)
            ·
              refine ⟨5851525530356530991147237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15604068080950749309725965 5851525530356530991147237)
              ·
                refine ⟨1097161036941849560840107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5851525530356530991147237 1097161036941849560840107)
                ·
                  refine ⟨1645741555412774341260161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097161036941849560840107 1645741555412774341260161)
                  ·
                    refine ⟨1234306166559580755945121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1645741555412774341260161 1234306166559580755945121)
                    ·
                      refine ⟨925729624919685566958841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1234306166559580755945121 925729624919685566958841)
                      ·
                        rfl

theorem cell23_1802852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 1, 2, 2].length) (baseStart_1802852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802852 prefixEnd_1802852 := by exact prefixLift 1802852
  have htrace : WordTrace (prefixWord ++ tailWord_1802852) baseStart_1802852 baseEnd_1802852 := by
    simpa [prefixWord, tailWord_1802852, baseEnd_1802852] using wordTrace_append hprefix tailTrace_1802852
  have hstable : (prefixWord ++ tailWord_1802852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802852).length < 2 ^ (prefixWord ++ tailWord_1802852).sum := by decide
  have hdescent : baseEnd_1802852 < baseStart_1802852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802881 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_1802881 : Nat := 118140960795 + 1802881 * 2 ^ 59
def prefixEnd_1802881 : Nat := 4983230072969 + 3 ^ 40 * 1802881 * 2
def baseEnd_1802881 : Nat := 925744515858665953496207

theorem tailTrace_1802881 : CollatzResearch.WordTrace tailWord_1802881 prefixEnd_1802881 925744515858665953496207 := by
  unfold tailWord_1802881
  simp only [CollatzResearch.WordTrace]
  refine ⟨65756472181477519406136497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43837648120985012937424331 65756472181477519406136497)
  ·
    refine ⟨49317354136108139554602373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65756472181477519406136497 49317354136108139554602373)
    ·
      refine ⟨9247003900520276166487945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49317354136108139554602373 9247003900520276166487945)
      ·
        refine ⟨6935252925390207124865959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9247003900520276166487945 6935252925390207124865959)
        ·
          refine ⟨10402879388085310687298939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6935252925390207124865959 10402879388085310687298939)
          ·
            refine ⟨15604319082127966030948409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10402879388085310687298939 15604319082127966030948409)
            ·
              refine ⟨11703239311595974523211307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15604319082127966030948409 11703239311595974523211307)
              ·
                refine ⟨17554858967393961784816961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11703239311595974523211307 17554858967393961784816961)
                ·
                  refine ⟨13166144225545471338612721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17554858967393961784816961 13166144225545471338612721)
                  ·
                    refine ⟨9874608169159103503959541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13166144225545471338612721 9874608169159103503959541)
                    ·
                      refine ⟨925744515858665953496207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9874608169159103503959541 925744515858665953496207)
                      ·
                        rfl

theorem cell23_1802881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_1802881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802881 prefixEnd_1802881 := by exact prefixLift 1802881
  have htrace : WordTrace (prefixWord ++ tailWord_1802881) baseStart_1802881 baseEnd_1802881 := by
    simpa [prefixWord, tailWord_1802881, baseEnd_1802881] using wordTrace_append hprefix tailTrace_1802881
  have hstable : (prefixWord ++ tailWord_1802881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802881).length < 2 ^ (prefixWord ++ tailWord_1802881).sum := by decide
  have hdescent : baseEnd_1802881 < baseStart_1802881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802919 : List Nat := [1, 1, 6, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_1802919 : Nat := 118140960795 + 1802919 * 2 ^ 59
def prefixEnd_1802919 : Nat := 4983230072969 + 3 ^ 40 * 1802919 * 2
def baseEnd_1802919 : Nat := 925764028123536804821033

theorem tailTrace_1802919 : CollatzResearch.WordTrace tailWord_1802919 prefixEnd_1802919 925764028123536804821033 := by
  unfold tailWord_1802919
  simp only [CollatzResearch.WordTrace]
  refine ⟨65757858155339851896019811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43838572103559901264013207 65757858155339851896019811)
  ·
    refine ⟨98636787233009777844029717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65757858155339851896019811 98636787233009777844029717)
    ·
      refine ⟨4623599401547333336438893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98636787233009777844029717 4623599401547333336438893)
      ·
        refine ⟨1733849775580250001164585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4623599401547333336438893 1733849775580250001164585)
        ·
          refine ⟨1300387331685187500873439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1733849775580250001164585 1300387331685187500873439)
          ·
            refine ⟨1950580997527781251310159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300387331685187500873439 1950580997527781251310159)
            ·
              refine ⟨2925871496291671876965239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1950580997527781251310159 2925871496291671876965239)
              ·
                refine ⟨4388807244437507815447859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2925871496291671876965239 4388807244437507815447859)
                ·
                  refine ⟨6583210866656261723171789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4388807244437507815447859 6583210866656261723171789)
                  ·
                    refine ⟨2468704074996098146189421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6583210866656261723171789 2468704074996098146189421)
                    ·
                      refine ⟨925764028123536804821033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2468704074996098146189421 925764028123536804821033)
                      ·
                        rfl

theorem cell23_1802919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_1802919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802919 prefixEnd_1802919 := by exact prefixLift 1802919
  have htrace : WordTrace (prefixWord ++ tailWord_1802919) baseStart_1802919 baseEnd_1802919 := by
    simpa [prefixWord, tailWord_1802919, baseEnd_1802919] using wordTrace_append hprefix tailTrace_1802919
  have hstable : (prefixWord ++ tailWord_1802919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802919).length < 2 ^ (prefixWord ++ tailWord_1802919).sum := by decide
  have hdescent : baseEnd_1802919 < baseStart_1802919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802929 : List Nat := [1, 2, 2, 6, 1, 1, 2, 2, 1, 3, 2]
def baseStart_1802929 : Nat := 118140960795 + 1802929 * 2 ^ 59
def prefixEnd_1802929 : Nat := 4983230072969 + 3 ^ 40 * 1802929 * 2
def baseEnd_1802929 : Nat := 925769162930081765695987

theorem tailTrace_1802929 : CollatzResearch.WordTrace tailWord_1802929 prefixEnd_1802929 925769162930081765695987 := by
  unfold tailWord_1802929
  simp only [CollatzResearch.WordTrace]
  refine ⟨65758222885303623603883841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43838815256869082402589227 65758222885303623603883841)
  ·
    refine ⟨49318667163977717702912881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65758222885303623603883841 49318667163977717702912881)
    ·
      refine ⟨36989000372983288277184661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49318667163977717702912881 36989000372983288277184661)
      ·
        refine ⟨1733859392483591637993031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36989000372983288277184661 1733859392483591637993031)
        ·
          refine ⟨2600789088725387456989547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1733859392483591637993031 2600789088725387456989547)
          ·
            refine ⟨3901183633088081185484321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600789088725387456989547 3901183633088081185484321)
            ·
              refine ⟨2925887724816060889113241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3901183633088081185484321 2925887724816060889113241)
              ·
                refine ⟨2194415793612045666834931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2925887724816060889113241 2194415793612045666834931)
                ·
                  refine ⟨3291623690418068500252397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2194415793612045666834931 3291623690418068500252397)
                  ·
                    refine ⟨1234358883906775687594649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3291623690418068500252397 1234358883906775687594649)
                    ·
                      refine ⟨925769162930081765695987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1234358883906775687594649 925769162930081765695987)
                      ·
                        rfl

theorem cell23_1802929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_1802929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802929 prefixEnd_1802929 := by exact prefixLift 1802929
  have htrace : WordTrace (prefixWord ++ tailWord_1802929) baseStart_1802929 baseEnd_1802929 := by
    simpa [prefixWord, tailWord_1802929, baseEnd_1802929] using wordTrace_append hprefix tailTrace_1802929
  have hstable : (prefixWord ++ tailWord_1802929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802929).length < 2 ^ (prefixWord ++ tailWord_1802929).sum := by decide
  have hdescent : baseEnd_1802929 < baseStart_1802929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802931 : List Nat := [1, 1, 1, 2, 3, 4, 2, 2, 7]
def baseStart_1802931 : Nat := 118140960795 + 1802931 * 2 ^ 59
def prefixEnd_1802931 : Nat := 4983230072969 + 3 ^ 40 * 1802931 * 2
def baseEnd_1802931 : Nat := 102863354432376750874553

theorem tailTrace_1802931 : CollatzResearch.WordTrace tailWord_1802931 prefixEnd_1802931 102863354432376750874553 := by
  unfold tailWord_1802931
  simp only [CollatzResearch.WordTrace]
  refine ⟨65758295831296377945456647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43838863887530918630304431 65758295831296377945456647)
  ·
    refine ⟨98637443746944566918184971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65758295831296377945456647 98637443746944566918184971)
    ·
      refine ⟨147956165620416850377277457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98637443746944566918184971 147956165620416850377277457)
      ·
        refine ⟨110967124215312637782958093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147956165620416850377277457 110967124215312637782958093)
        ·
          refine ⟨41612671580742239168609285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110967124215312637782958093 41612671580742239168609285)
          ·
            refine ⟨7802375921389169844114241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41612671580742239168609285 7802375921389169844114241)
            ·
              refine ⟨5851781941041877383085681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7802375921389169844114241 5851781941041877383085681)
              ·
                refine ⟨4388836455781408037314261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5851781941041877383085681 4388836455781408037314261)
                ·
                  refine ⟨102863354432376750874553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4388836455781408037314261 102863354432376750874553)
                  ·
                    rfl

theorem cell23_1802931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 7].length) (baseStart_1802931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1802931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1802931 prefixEnd_1802931 := by exact prefixLift 1802931
  have htrace : WordTrace (prefixWord ++ tailWord_1802931) baseStart_1802931 baseEnd_1802931 := by
    simpa [prefixWord, tailWord_1802931, baseEnd_1802931] using wordTrace_append hprefix tailTrace_1802931
  have hstable : (prefixWord ++ tailWord_1802931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802931).length < 2 ^ (prefixWord ++ tailWord_1802931).sum := by decide
  have hdescent : baseEnd_1802931 < baseStart_1802931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803011 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 6]
def baseStart_1803011 : Nat := 118140960795 + 1803011 * 2 ^ 59
def prefixEnd_1803011 : Nat := 4983230072969 + 3 ^ 40 * 1803011 * 2
def baseEnd_1803011 : Nat := 925811268343750444870609

theorem tailTrace_1803011 : CollatzResearch.WordTrace tailWord_1803011 prefixEnd_1803011 925811268343750444870609 := by
  unfold tailWord_1803011
  simp only [CollatzResearch.WordTrace]
  refine ⟨65761213671006551608368887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43840809114004367738912591 65761213671006551608368887)
  ·
    refine ⟨98641820506509827412553331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65761213671006551608368887 98641820506509827412553331)
    ·
      refine ⟨147962730759764741118829997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98641820506509827412553331 147962730759764741118829997)
      ·
        refine ⟨55486024034911777919561249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147962730759764741118829997 55486024034911777919561249)
        ·
          refine ⟨41614518026183833439670937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55486024034911777919561249 41614518026183833439670937)
          ·
            refine ⟨31210888519637875079753203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41614518026183833439670937 31210888519637875079753203)
            ·
              refine ⟨46816332779456812619629805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31210888519637875079753203 46816332779456812619629805)
              ·
                refine ⟨17556124792296304732361177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46816332779456812619629805 17556124792296304732361177)
                ·
                  refine ⟨13167093594222228549270883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17556124792296304732361177 13167093594222228549270883)
                  ·
                    refine ⟨19750640391333342823906325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13167093594222228549270883 19750640391333342823906325)
                    ·
                      refine ⟨925811268343750444870609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19750640391333342823906325 925811268343750444870609)
                      ·
                        rfl

theorem cell23_1803011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_1803011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803011 prefixEnd_1803011 := by exact prefixLift 1803011
  have htrace : WordTrace (prefixWord ++ tailWord_1803011) baseStart_1803011 baseEnd_1803011 := by
    simpa [prefixWord, tailWord_1803011, baseEnd_1803011] using wordTrace_append hprefix tailTrace_1803011
  have hstable : (prefixWord ++ tailWord_1803011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803011).length < 2 ^ (prefixWord ++ tailWord_1803011).sum := by decide
  have hdescent : baseEnd_1803011 < baseStart_1803011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803015 : List Nat := [1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1803015 : Nat := 118140960795 + 1803015 * 2 ^ 59
def prefixEnd_1803015 : Nat := 4983230072969 + 3 ^ 40 * 1803015 * 2
def baseEnd_1803015 : Nat := 925813322266368429220591

theorem tailTrace_1803015 : CollatzResearch.WordTrace tailWord_1803015 prefixEnd_1803015 925813322266368429220591 := by
  unfold tailWord_1803015
  simp only [CollatzResearch.WordTrace]
  refine ⟨65761359562992060291514499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43840906375328040194342999 65761359562992060291514499)
  ·
    refine ⟨98642039344488090437271749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65761359562992060291514499 98642039344488090437271749)
    ·
      refine ⟨18495382377091516956988453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98642039344488090437271749 18495382377091516956988453)
      ·
        refine ⟨3467884195704659429435335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18495382377091516956988453 3467884195704659429435335)
        ·
          refine ⟨5201826293556989144153003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3467884195704659429435335 5201826293556989144153003)
          ·
            refine ⟨7802739440335483716229505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5201826293556989144153003 7802739440335483716229505)
            ·
              refine ⟨5852054580251612787172129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7802739440335483716229505 5852054580251612787172129)
              ·
                refine ⟨4389040935188709590379097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5852054580251612787172129 4389040935188709590379097)
                ·
                  refine ⟨3291780701391532192784323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4389040935188709590379097 3291780701391532192784323)
                  ·
                    refine ⟨4937671052087298289176485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3291780701391532192784323 4937671052087298289176485)
                    ·
                      refine ⟨925813322266368429220591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4937671052087298289176485 925813322266368429220591)
                      ·
                        rfl

theorem cell23_1803015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1803015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803015 prefixEnd_1803015 := by exact prefixLift 1803015
  have htrace : WordTrace (prefixWord ++ tailWord_1803015) baseStart_1803015 baseEnd_1803015 := by
    simpa [prefixWord, tailWord_1803015, baseEnd_1803015] using wordTrace_append hprefix tailTrace_1803015
  have hstable : (prefixWord ++ tailWord_1803015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803015).length < 2 ^ (prefixWord ++ tailWord_1803015).sum := by decide
  have hdescent : baseEnd_1803015 < baseStart_1803015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803075 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 4, 3, 2]
def baseStart_1803075 : Nat := 118140960795 + 1803075 * 2 ^ 59
def prefixEnd_1803075 : Nat := 4983230072969 + 3 ^ 40 * 1803075 * 2
def baseEnd_1803075 : Nat := 925844131105638194470315

theorem tailTrace_1803075 : CollatzResearch.WordTrace tailWord_1803075 prefixEnd_1803075 925844131105638194470315 := by
  unfold tailWord_1803075
  simp only [CollatzResearch.WordTrace]
  refine ⟨65763547942774690538698679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43842365295183127025799119 65763547942774690538698679)
  ·
    refine ⟨98645321914162035808048019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65763547942774690538698679 98645321914162035808048019)
    ·
      refine ⟨147967982871243053712072029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98645321914162035808048019 147967982871243053712072029)
      ·
        refine ⟨55487993576716145142027011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147967982871243053712072029 55487993576716145142027011)
        ·
          refine ⟨83231990365074217713040517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55487993576716145142027011 83231990365074217713040517)
          ·
            refine ⟨15605998193451415821195097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83231990365074217713040517 15605998193451415821195097)
            ·
              refine ⟨11704498645088561865896323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15605998193451415821195097 11704498645088561865896323)
              ·
                refine ⟨17556747967632842798844485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11704498645088561865896323 17556747967632842798844485)
                ·
                  refine ⟨3291890243931158024783341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17556747967632842798844485 3291890243931158024783341)
                  ·
                    refine ⟨1234458841474184259293753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3291890243931158024783341 1234458841474184259293753)
                    ·
                      refine ⟨925844131105638194470315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1234458841474184259293753 925844131105638194470315)
                      ·
                        rfl

theorem cell23_1803075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 3, 2].length) (baseStart_1803075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803075 prefixEnd_1803075 := by exact prefixLift 1803075
  have htrace : WordTrace (prefixWord ++ tailWord_1803075) baseStart_1803075 baseEnd_1803075 := by
    simpa [prefixWord, tailWord_1803075, baseEnd_1803075] using wordTrace_append hprefix tailTrace_1803075
  have hstable : (prefixWord ++ tailWord_1803075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803075).length < 2 ^ (prefixWord ++ tailWord_1803075).sum := by decide
  have hdescent : baseEnd_1803075 < baseStart_1803075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803088 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 4]
def baseStart_1803088 : Nat := 118140960795 + 1803088 * 2 ^ 59
def prefixEnd_1803088 : Nat := 4983230072969 + 3 ^ 40 * 1803088 * 2
def baseEnd_1803088 : Nat := 925850806354146643607755

theorem tailTrace_1803088 : CollatzResearch.WordTrace tailWord_1803088 prefixEnd_1803088 925850806354146643607755 := by
  unfold tailWord_1803088
  simp only [CollatzResearch.WordTrace]
  refine ⟨32882011045863796879460959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43842681394485062505947945 32882011045863796879460959)
  ·
    refine ⟨49323016568795695319191439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32882011045863796879460959 49323016568795695319191439)
    ·
      refine ⟨73984524853193542978787159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49323016568795695319191439 73984524853193542978787159)
      ·
        refine ⟨110976787279790314468180739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73984524853193542978787159 110976787279790314468180739)
        ·
          refine ⟨166465180919685471702271109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110976787279790314468180739 166465180919685471702271109)
          ·
            refine ⟨31212221422441025944175833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166465180919685471702271109 31212221422441025944175833)
            ·
              refine ⟨23409166066830769458131875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31212221422441025944175833 23409166066830769458131875)
              ·
                refine ⟨35113749100246154187197813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23409166066830769458131875 35113749100246154187197813)
                ·
                  refine ⟨3291913978148076955049795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35113749100246154187197813 3291913978148076955049795)
                  ·
                    refine ⟨4937870967222115432574693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3291913978148076955049795 4937870967222115432574693)
                    ·
                      refine ⟨925850806354146643607755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4937870967222115432574693 925850806354146643607755)
                      ·
                        rfl

theorem cell23_1803088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 4].length) (baseStart_1803088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803088 prefixEnd_1803088 := by exact prefixLift 1803088
  have htrace : WordTrace (prefixWord ++ tailWord_1803088) baseStart_1803088 baseEnd_1803088 := by
    simpa [prefixWord, tailWord_1803088, baseEnd_1803088] using wordTrace_append hprefix tailTrace_1803088
  have hstable : (prefixWord ++ tailWord_1803088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803088).length < 2 ^ (prefixWord ++ tailWord_1803088).sum := by decide
  have hdescent : baseEnd_1803088 < baseStart_1803088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803122 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 5, 2, 2]
def baseStart_1803122 : Nat := 118140960795 + 1803122 * 2 ^ 59
def prefixEnd_1803122 : Nat := 4983230072969 + 3 ^ 40 * 1803122 * 2
def baseEnd_1803122 : Nat := 925868264696399510582599

theorem tailTrace_1803122 : CollatzResearch.WordTrace tailWord_1803122 prefixEnd_1803122 925868264696399510582599 := by
  unfold tailWord_1803122
  simp only [CollatzResearch.WordTrace]
  refine ⟨16441315543401104391414905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43843508115736278377106413 16441315543401104391414905)
  ·
    refine ⟨12330986657550828293561179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16441315543401104391414905 12330986657550828293561179)
    ·
      refine ⟨18496479986326242440341769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12330986657550828293561179 18496479986326242440341769)
      ·
        refine ⟨13872359989744681830256327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18496479986326242440341769 13872359989744681830256327)
        ·
          refine ⟨20808539984617022745384491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13872359989744681830256327 20808539984617022745384491)
          ·
            refine ⟨31212809976925534118076737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20808539984617022745384491 31212809976925534118076737)
            ·
              refine ⟨23409607482694150588557553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31212809976925534118076737 23409607482694150588557553)
              ·
                refine ⟨17557205612020612941418165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23409607482694150588557553 17557205612020612941418165)
                ·
                  refine ⟨1645988026126932463257953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17557205612020612941418165 1645988026126932463257953)
                  ·
                    refine ⟨1234491019595199347443465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1645988026126932463257953 1234491019595199347443465)
                    ·
                      refine ⟨925868264696399510582599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1234491019595199347443465 925868264696399510582599)
                      ·
                        rfl

theorem cell23_1803122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_1803122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803122 prefixEnd_1803122 := by exact prefixLift 1803122
  have htrace : WordTrace (prefixWord ++ tailWord_1803122) baseStart_1803122 baseEnd_1803122 := by
    simpa [prefixWord, tailWord_1803122, baseEnd_1803122] using wordTrace_append hprefix tailTrace_1803122
  have hstable : (prefixWord ++ tailWord_1803122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803122).length < 2 ^ (prefixWord ++ tailWord_1803122).sum := by decide
  have hdescent : baseEnd_1803122 < baseStart_1803122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803125 : List Nat := [1, 3, 4, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1803125 : Nat := 118140960795 + 1803125 * 2 ^ 59
def prefixEnd_1803125 : Nat := 4983230072969 + 3 ^ 40 * 1803125 * 2
def baseEnd_1803125 : Nat := 925869805138362998845085

theorem tailTrace_1803125 : CollatzResearch.WordTrace tailWord_1803125 prefixEnd_1803125 925869805138362998845085 := by
  unfold tailWord_1803125
  simp only [CollatzResearch.WordTrace]
  refine ⟨65765371592593549078018829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43843581061729032718679219 65765371592593549078018829)
  ·
    refine ⟨24662014347222580904257061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65765371592593549078018829 24662014347222580904257061)
    ·
      refine ⟨4624127690104233919548199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24662014347222580904257061 4624127690104233919548199)
      ·
        refine ⟨6936191535156350879322299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4624127690104233919548199 6936191535156350879322299)
        ·
          refine ⟨10404287302734526318983449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6936191535156350879322299 10404287302734526318983449)
          ·
            refine ⟨7803215477050894739237587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10404287302734526318983449 7803215477050894739237587)
            ·
              refine ⟨11704823215576342108856381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7803215477050894739237587 11704823215576342108856381)
              ·
                refine ⟨4389308705841128290821143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11704823215576342108856381 4389308705841128290821143)
                ·
                  refine ⟨6583963058761692436231715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4389308705841128290821143 6583963058761692436231715)
                  ·
                    refine ⟨9875944588142538654347573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6583963058761692436231715 9875944588142538654347573)
                    ·
                      refine ⟨925869805138362998845085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9875944588142538654347573 925869805138362998845085)
                      ·
                        rfl

theorem cell23_1803125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1803125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803125 prefixEnd_1803125 := by exact prefixLift 1803125
  have htrace : WordTrace (prefixWord ++ tailWord_1803125) baseStart_1803125 baseEnd_1803125 := by
    simpa [prefixWord, tailWord_1803125, baseEnd_1803125] using wordTrace_append hprefix tailTrace_1803125
  have hstable : (prefixWord ++ tailWord_1803125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803125).length < 2 ^ (prefixWord ++ tailWord_1803125).sum := by decide
  have hdescent : baseEnd_1803125 < baseStart_1803125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803155 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 6, 1, 3]
def baseStart_1803155 : Nat := 118140960795 + 1803155 * 2 ^ 59
def prefixEnd_1803155 : Nat := 4983230072969 + 3 ^ 40 * 1803155 * 2
def baseEnd_1803155 : Nat := 925885209557997881469947

theorem tailTrace_1803155 : CollatzResearch.WordTrace tailWord_1803155 prefixEnd_1803155 925885209557997881469947 := by
  unfold tailWord_1803155
  simp only [CollatzResearch.WordTrace]
  refine ⟨65766465782484864201610919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43844310521656576134407279 65766465782484864201610919)
  ·
    refine ⟨98649698673727296302416379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65766465782484864201610919 98649698673727296302416379)
    ·
      refine ⟨147974548010590944453624569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98649698673727296302416379 147974548010590944453624569)
      ·
        refine ⟨110980911007943208340218427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147974548010590944453624569 110980911007943208340218427)
        ·
          refine ⟨166471366511914812510327641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110980911007943208340218427 166471366511914812510327641)
          ·
            refine ⟨124853524883936109382745731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166471366511914812510327641 124853524883936109382745731)
            ·
              refine ⟨187280287325904164074118597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124853524883936109382745731 187280287325904164074118597)
              ·
                refine ⟨35115053873607030763897237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187280287325904164074118597 35115053873607030763897237)
                ·
                  refine ⟨1646018150325329567057683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35115053873607030763897237 1646018150325329567057683)
                  ·
                    refine ⟨2469027225487994350586525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1646018150325329567057683 2469027225487994350586525)
                    ·
                      refine ⟨925885209557997881469947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2469027225487994350586525 925885209557997881469947)
                      ·
                        rfl

theorem cell23_1803155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 1, 3].length) (baseStart_1803155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803155 prefixEnd_1803155 := by exact prefixLift 1803155
  have htrace : WordTrace (prefixWord ++ tailWord_1803155) baseStart_1803155 baseEnd_1803155 := by
    simpa [prefixWord, tailWord_1803155, baseEnd_1803155] using wordTrace_append hprefix tailTrace_1803155
  have hstable : (prefixWord ++ tailWord_1803155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803155).length < 2 ^ (prefixWord ++ tailWord_1803155).sum := by decide
  have hdescent : baseEnd_1803155 < baseStart_1803155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803168 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 5]
def baseStart_1803168 : Nat := 118140960795 + 1803168 * 2 ^ 59
def prefixEnd_1803168 : Nat := 4983230072969 + 3 ^ 40 * 1803168 * 2
def baseEnd_1803168 : Nat := 925891884806506330607387

theorem tailTrace_1803168 : CollatzResearch.WordTrace tailWord_1803168 prefixEnd_1803168 925891884806506330607387 := by
  unfold tailWord_1803168
  simp only [CollatzResearch.WordTrace]
  refine ⟨32883469965718883710917079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43844626620958511614556105 32883469965718883710917079)
  ·
    refine ⟨49325204948578325566375619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32883469965718883710917079 49325204948578325566375619)
    ·
      refine ⟨73987807422867488349563429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49325204948578325566375619 73987807422867488349563429)
      ·
        refine ⟨13872713891787654065543143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73987807422867488349563429 13872713891787654065543143)
        ·
          refine ⟨20809070837681481098314715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13872713891787654065543143 20809070837681481098314715)
          ·
            refine ⟨31213606256522221647472073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20809070837681481098314715 31213606256522221647472073)
            ·
              refine ⟨23410204692391666235604055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31213606256522221647472073 23410204692391666235604055)
              ·
                refine ⟨35115307038587499353406083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23410204692391666235604055 35115307038587499353406083)
                ·
                  refine ⟨52672960557881249030109125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35115307038587499353406083 52672960557881249030109125)
                  ·
                    refine ⟨9876180104602734193145461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52672960557881249030109125 9876180104602734193145461)
                    ·
                      refine ⟨925891884806506330607387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9876180104602734193145461 925891884806506330607387)
                      ·
                        rfl

theorem cell23_1803168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_1803168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803168 prefixEnd_1803168 := by exact prefixLift 1803168
  have htrace : WordTrace (prefixWord ++ tailWord_1803168) baseStart_1803168 baseEnd_1803168 := by
    simpa [prefixWord, tailWord_1803168, baseEnd_1803168] using wordTrace_append hprefix tailTrace_1803168
  have hstable : (prefixWord ++ tailWord_1803168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803168).length < 2 ^ (prefixWord ++ tailWord_1803168).sum := by decide
  have hdescent : baseEnd_1803168 < baseStart_1803168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803189 : List Nat := [1, 3, 3, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_1803189 : Nat := 118140960795 + 1803189 * 2 ^ 59
def prefixEnd_1803189 : Nat := 4983230072969 + 3 ^ 40 * 1803189 * 2
def baseEnd_1803189 : Nat := 925902667900250748444791

theorem tailTrace_1803189 : CollatzResearch.WordTrace tailWord_1803189 prefixEnd_1803189 925902667900250748444791 := by
  unfold tailWord_1803189
  simp only [CollatzResearch.WordTrace]
  refine ⟨65767705864361688008348621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43845137242907792005565747 65767705864361688008348621)
  ·
    refine ⟨24662889699135633003130733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65767705864361688008348621 24662889699135633003130733)
    ·
      refine ⟨9248583637175862376174025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24662889699135633003130733 9248583637175862376174025)
      ·
        refine ⟨6936437727881896782130519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9248583637175862376174025 6936437727881896782130519)
        ·
          refine ⟨10404656591822845173195779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6936437727881896782130519 10404656591822845173195779)
          ·
            refine ⟨15606984887734267759793669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10404656591822845173195779 15606984887734267759793669)
            ·
              refine ⟨2926309666450175204961313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15606984887734267759793669 2926309666450175204961313)
              ·
                refine ⟨2194732249837631403720985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2926309666450175204961313 2194732249837631403720985)
                ·
                  refine ⟨1646049187378223552790739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2194732249837631403720985 1646049187378223552790739)
                  ·
                    refine ⟨2469073781067335329186109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1646049187378223552790739 2469073781067335329186109)
                    ·
                      refine ⟨925902667900250748444791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2469073781067335329186109 925902667900250748444791)
                      ·
                        rfl

theorem cell23_1803189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_1803189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803189 prefixEnd_1803189 := by exact prefixLift 1803189
  have htrace : WordTrace (prefixWord ++ tailWord_1803189) baseStart_1803189 baseEnd_1803189 := by
    simpa [prefixWord, tailWord_1803189, baseEnd_1803189] using wordTrace_append hprefix tailTrace_1803189
  have hstable : (prefixWord ++ tailWord_1803189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803189).length < 2 ^ (prefixWord ++ tailWord_1803189).sum := by decide
  have hdescent : baseEnd_1803189 < baseStart_1803189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803229 : List Nat := [1, 4, 3, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_1803229 : Nat := 118140960795 + 1803229 * 2 ^ 59
def prefixEnd_1803229 : Nat := 4983230072969 + 3 ^ 40 * 1803229 * 2
def baseEnd_1803229 : Nat := 925923207126430591944607

theorem tailTrace_1803229 : CollatzResearch.WordTrace tailWord_1803229 prefixEnd_1803229 925923207126430591944607 := by
  unfold tailWord_1803229
  simp only [CollatzResearch.WordTrace]
  refine ⟨65769164784216774839804741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43846109856144516559869827 65769164784216774839804741)
  ·
    refine ⟨12331718397040645282463389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65769164784216774839804741 12331718397040645282463389)
    ·
      refine ⟨4624394398890241980923771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12331718397040645282463389 4624394398890241980923771)
      ·
        refine ⟨6936591598335362971385657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4624394398890241980923771 6936591598335362971385657)
        ·
          refine ⟨5202443698751522228539243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6936591598335362971385657 5202443698751522228539243)
          ·
            refine ⟨7803665548127283342808865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5202443698751522228539243 7803665548127283342808865)
            ·
              refine ⟨5852749161095462507106649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7803665548127283342808865 5852749161095462507106649)
              ·
                refine ⟨4389561870821596880329987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5852749161095462507106649 4389561870821596880329987)
                ·
                  refine ⟨6584342806232395320494981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4389561870821596880329987 6584342806232395320494981)
                  ·
                    refine ⟨1234564276168574122592809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6584342806232395320494981 1234564276168574122592809)
                    ·
                      refine ⟨925923207126430591944607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1234564276168574122592809 925923207126430591944607)
                      ·
                        rfl

theorem cell23_1803229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_1803229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803229 prefixEnd_1803229 := by exact prefixLift 1803229
  have htrace : WordTrace (prefixWord ++ tailWord_1803229) baseStart_1803229 baseEnd_1803229 := by
    simpa [prefixWord, tailWord_1803229, baseEnd_1803229] using wordTrace_append hprefix tailTrace_1803229
  have hstable : (prefixWord ++ tailWord_1803229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803229).length < 2 ^ (prefixWord ++ tailWord_1803229).sum := by decide
  have hdescent : baseEnd_1803229 < baseStart_1803229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803246 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 4, 2, 2]
def baseStart_1803246 : Nat := 118140960795 + 1803246 * 2 ^ 59
def prefixEnd_1803246 : Nat := 4983230072969 + 3 ^ 40 * 1803246 * 2
def baseEnd_1803246 : Nat := 925931936297557025432029

theorem tailTrace_1803246 : CollatzResearch.WordTrace tailWord_1803246 prefixEnd_1803246 925931936297557025432029 := by
  unfold tailWord_1803246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8221223103144398342896699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43846523216770124495449061 8221223103144398342896699)
  ·
    refine ⟨12331834654716597514345049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8221223103144398342896699 12331834654716597514345049)
    ·
      refine ⟨9248875991037448135758787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12331834654716597514345049 9248875991037448135758787)
      ·
        refine ⟨13873313986556172203638181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9248875991037448135758787 13873313986556172203638181)
        ·
          refine ⟨2601246372479282288182159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13873313986556172203638181 2601246372479282288182159)
          ·
            refine ⟨3901869558718923432273239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2601246372479282288182159 3901869558718923432273239)
            ·
              refine ⟨5852804338078385148409859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3901869558718923432273239 5852804338078385148409859)
              ·
                refine ⟨8779206507117577722614789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5852804338078385148409859 8779206507117577722614789)
                ·
                  refine ⟨1646101220084545822990273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8779206507117577722614789 1646101220084545822990273)
                  ·
                    refine ⟨1234575915063409367242705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1646101220084545822990273 1234575915063409367242705)
                    ·
                      refine ⟨925931936297557025432029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1234575915063409367242705 925931936297557025432029)
                      ·
                        rfl

theorem cell23_1803246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_1803246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803246 prefixEnd_1803246 := by exact prefixLift 1803246
  have htrace : WordTrace (prefixWord ++ tailWord_1803246) baseStart_1803246 baseEnd_1803246 := by
    simpa [prefixWord, tailWord_1803246, baseEnd_1803246] using wordTrace_append hprefix tailTrace_1803246
  have hstable : (prefixWord ++ tailWord_1803246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803246).length < 2 ^ (prefixWord ++ tailWord_1803246).sum := by decide
  have hdescent : baseEnd_1803246 < baseStart_1803246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803265 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 1, 7]
def baseStart_1803265 : Nat := 118140960795 + 1803265 * 2 ^ 59
def prefixEnd_1803265 : Nat := 4983230072969 + 3 ^ 40 * 1803265 * 2
def baseEnd_1803265 : Nat := 308647230809997483698147

theorem tailTrace_1803265 : CollatzResearch.WordTrace tailWord_1803265 prefixEnd_1803265 308647230809997483698147 := by
  unfold tailWord_1803265
  simp only [CollatzResearch.WordTrace]
  refine ⟨65770477812086352988115249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43846985208057568658743499 65770477812086352988115249)
  ·
    refine ⟨49327858359064764741086437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65770477812086352988115249 49327858359064764741086437)
    ·
      refine ⟨9248973442324643388953707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49327858359064764741086437 9248973442324643388953707)
      ·
        refine ⟨13873460163486965083430561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9248973442324643388953707 13873460163486965083430561)
        ·
          refine ⟨10405095122615223812572921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13873460163486965083430561 10405095122615223812572921)
          ·
            refine ⟨7803821341961417859429691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10405095122615223812572921 7803821341961417859429691)
            ·
              refine ⟨11705732012942126789144537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7803821341961417859429691 11705732012942126789144537)
              ·
                refine ⟨8779299009706595091858403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11705732012942126789144537 8779299009706595091858403)
                ·
                  refine ⟨13168948514559892637787605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8779299009706595091858403 13168948514559892637787605)
                  ·
                    refine ⟨308647230809997483698147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13168948514559892637787605 308647230809997483698147)
                    ·
                      rfl

theorem cell23_1803265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_1803265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803265 prefixEnd_1803265 := by exact prefixLift 1803265
  have htrace : WordTrace (prefixWord ++ tailWord_1803265) baseStart_1803265 baseEnd_1803265 := by
    simpa [prefixWord, tailWord_1803265, baseEnd_1803265] using wordTrace_append hprefix tailTrace_1803265
  have hstable : (prefixWord ++ tailWord_1803265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803265).length < 2 ^ (prefixWord ++ tailWord_1803265).sum := by decide
  have hdescent : baseEnd_1803265 < baseStart_1803265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803382 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_1803382 : Nat := 118140960795 + 1803382 * 2 ^ 59
def prefixEnd_1803382 : Nat := 4983230072969 + 3 ^ 40 * 1803382 * 2
def baseEnd_1803382 : Nat := 926001769666568493331403

theorem tailTrace_1803382 : CollatzResearch.WordTrace tailWord_1803382 prefixEnd_1803382 926001769666568493331403 := by
  unfold tailWord_1803382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4110921572041405123132775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43849830101774987980082933 4110921572041405123132775)
  ·
    refine ⟨6166382358062107684699163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4110921572041405123132775 6166382358062107684699163)
    ·
      refine ⟨9249573537093161527048745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6166382358062107684699163 9249573537093161527048745)
      ·
        refine ⟨6937180152819871145286559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9249573537093161527048745 6937180152819871145286559)
        ·
          refine ⟨10405770229229806717929839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6937180152819871145286559 10405770229229806717929839)
          ·
            refine ⟨15608655343844710076894759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10405770229229806717929839 15608655343844710076894759)
            ·
              refine ⟨23412983015767065115342139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15608655343844710076894759 23412983015767065115342139)
              ·
                refine ⟨35119474523650597673013209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23412983015767065115342139 35119474523650597673013209)
                ·
                  refine ⟨26339605892737948254759907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35119474523650597673013209 26339605892737948254759907)
                  ·
                    refine ⟨39509408839106922382139861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26339605892737948254759907 39509408839106922382139861)
                    ·
                      refine ⟨926001769666568493331403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39509408839106922382139861 926001769666568493331403)
                      ·
                        rfl

theorem cell23_1803382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_1803382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803382 prefixEnd_1803382 := by exact prefixLift 1803382
  have htrace : WordTrace (prefixWord ++ tailWord_1803382) baseStart_1803382 baseEnd_1803382 := by
    simpa [prefixWord, tailWord_1803382, baseEnd_1803382] using wordTrace_append hprefix tailTrace_1803382
  have hstable : (prefixWord ++ tailWord_1803382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803382).length < 2 ^ (prefixWord ++ tailWord_1803382).sum := by decide
  have hdescent : baseEnd_1803382 < baseStart_1803382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803392 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 4]
def baseStart_1803392 : Nat := 118140960795 + 1803392 * 2 ^ 59
def prefixEnd_1803392 : Nat := 4983230072969 + 3 ^ 40 * 1803392 * 2
def baseEnd_1803392 : Nat := 926006904473113454206357

theorem tailTrace_1803392 : CollatzResearch.WordTrace tailWord_1803392 prefixEnd_1803392 926006904473113454206357 := by
  unfold tailWord_1803392
  simp only [CollatzResearch.WordTrace]
  refine ⟨32887554941313126838994215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43850073255084169118658953 32887554941313126838994215)
  ·
    refine ⟨49331332411969690258491323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32887554941313126838994215 49331332411969690258491323)
    ·
      refine ⟨73996998617954535387736985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49331332411969690258491323 73996998617954535387736985)
      ·
        refine ⟨55497748963465901540802739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73996998617954535387736985 55497748963465901540802739)
        ·
          refine ⟨83246623445198852311204109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55497748963465901540802739 83246623445198852311204109)
          ·
            refine ⟨31217483791949569616701541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83246623445198852311204109 31217483791949569616701541)
            ·
              refine ⟨5853278210990544303131539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31217483791949569616701541 5853278210990544303131539)
              ·
                refine ⟨8779917316485816454697309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5853278210990544303131539 8779917316485816454697309)
                ·
                  refine ⟨3292468993682181170511491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8779917316485816454697309 3292468993682181170511491)
                  ·
                    refine ⟨4938703490523271755767237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3292468993682181170511491 4938703490523271755767237)
                    ·
                      refine ⟨926006904473113454206357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4938703490523271755767237 926006904473113454206357)
                      ·
                        rfl

theorem cell23_1803392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_1803392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803392 prefixEnd_1803392 := by exact prefixLift 1803392
  have htrace : WordTrace (prefixWord ++ tailWord_1803392) baseStart_1803392 baseEnd_1803392 := by
    simpa [prefixWord, tailWord_1803392, baseEnd_1803392] using wordTrace_append hprefix tailTrace_1803392
  have hstable : (prefixWord ++ tailWord_1803392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803392).length < 2 ^ (prefixWord ++ tailWord_1803392).sum := by decide
  have hdescent : baseEnd_1803392 < baseStart_1803392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803396 : List Nat := [2, 3, 2, 1, 2, 2, 3, 1, 2, 3, 2]
def baseStart_1803396 : Nat := 118140960795 + 1803396 * 2 ^ 59
def prefixEnd_1803396 : Nat := 4983230072969 + 3 ^ 40 * 1803396 * 2
def baseEnd_1803396 : Nat := 926008958395731438556339

theorem tailTrace_1803396 : CollatzResearch.WordTrace tailWord_1803396 prefixEnd_1803396 926008958395731438556339 := by
  unfold tailWord_1803396
  simp only [CollatzResearch.WordTrace]
  refine ⟨32887627887305881180567021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43850170516407841574089361 32887627887305881180567021)
  ·
    refine ⟨12332860457739705442712633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32887627887305881180567021 12332860457739705442712633)
    ·
      refine ⟨9249645343304779082034475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12332860457739705442712633 9249645343304779082034475)
      ·
        refine ⟨13874468014957168623051713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9249645343304779082034475 13874468014957168623051713)
        ·
          refine ⟨10405851011217876467288785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13874468014957168623051713 10405851011217876467288785)
          ·
            refine ⟨7804388258413407350466589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10405851011217876467288785 7804388258413407350466589)
            ·
              refine ⟨2926645596905027756424971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7804388258413407350466589 2926645596905027756424971)
              ·
                refine ⟨4389968395357541634637457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2926645596905027756424971 4389968395357541634637457)
                ·
                  refine ⟨3292476296518156225978093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4389968395357541634637457 3292476296518156225978093)
                  ·
                    refine ⟨1234678611194308584741785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3292476296518156225978093 1234678611194308584741785)
                    ·
                      refine ⟨926008958395731438556339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1234678611194308584741785 926008958395731438556339)
                      ·
                        rfl

theorem cell23_1803396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_1803396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803396 prefixEnd_1803396 := by exact prefixLift 1803396
  have htrace : WordTrace (prefixWord ++ tailWord_1803396) baseStart_1803396 baseEnd_1803396 := by
    simpa [prefixWord, tailWord_1803396, baseEnd_1803396] using wordTrace_append hprefix tailTrace_1803396
  have hstable : (prefixWord ++ tailWord_1803396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803396).length < 2 ^ (prefixWord ++ tailWord_1803396).sum := by decide
  have hdescent : baseEnd_1803396 < baseStart_1803396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803402 : List Nat := [3, 1, 2, 3, 1, 1, 1, 4, 1, 6]
def baseStart_1803402 : Nat := 118140960795 + 1803402 * 2 ^ 59
def prefixEnd_1803402 : Nat := 4983230072969 + 3 ^ 40 * 1803402 * 2
def baseEnd_1803402 : Nat := 308670679759886138360437

theorem tailTrace_1803402 : CollatzResearch.WordTrace tailWord_1803402 prefixEnd_1803402 308670679759886138360437 := by
  unfold tailWord_1803402
  simp only [CollatzResearch.WordTrace]
  refine ⟨16443868653147506346463115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43850316408393350257234973 16443868653147506346463115)
  ·
    refine ⟨24665802979721259519694673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16443868653147506346463115 24665802979721259519694673)
    ·
      refine ⟨18499352234790944639771005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24665802979721259519694673 18499352234790944639771005)
      ·
        refine ⟨6937257088046604239914127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18499352234790944639771005 6937257088046604239914127)
        ·
          refine ⟨10405885632069906359871191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6937257088046604239914127 10405885632069906359871191)
          ·
            refine ⟨15608828448104859539806787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10405885632069906359871191 15608828448104859539806787)
            ·
              refine ⟨23413242672157289309710181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15608828448104859539806787 23413242672157289309710181)
              ·
                refine ⟨4389983001029491745570659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23413242672157289309710181 4389983001029491745570659)
                ·
                  refine ⟨6584974501544237618355989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4389983001029491745570659 6584974501544237618355989)
                  ·
                    refine ⟨308670679759886138360437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6584974501544237618355989 308670679759886138360437)
                    ·
                      rfl

theorem cell23_1803402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_1803402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803402 prefixEnd_1803402 := by exact prefixLift 1803402
  have htrace : WordTrace (prefixWord ++ tailWord_1803402) baseStart_1803402 baseEnd_1803402 := by
    simpa [prefixWord, tailWord_1803402, baseEnd_1803402] using wordTrace_append hprefix tailTrace_1803402
  have hstable : (prefixWord ++ tailWord_1803402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803402).length < 2 ^ (prefixWord ++ tailWord_1803402).sum := by decide
  have hdescent : baseEnd_1803402 < baseStart_1803402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803406 : List Nat := [4, 1, 1, 3, 2, 1, 4, 1, 1, 5]
def baseStart_1803406 : Nat := 118140960795 + 1803406 * 2 ^ 59
def prefixEnd_1803406 : Nat := 4983230072969 + 3 ^ 40 * 1803406 * 2
def baseEnd_1803406 : Nat := 308671364400758799810431

theorem tailTrace_1803406 : CollatzResearch.WordTrace tailWord_1803406 prefixEnd_1803406 308671364400758799810431 := by
  unfold tailWord_1803406
  simp only [CollatzResearch.WordTrace]
  refine ⟨8221952563071941758624759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43850413669717022712665381 8221952563071941758624759)
  ·
    refine ⟨12332928844607912637937139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8221952563071941758624759 12332928844607912637937139)
    ·
      refine ⟨18499393266911868956905709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12332928844607912637937139 18499393266911868956905709)
      ·
        refine ⟨6937272475091950858839641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18499393266911868956905709 6937272475091950858839641)
        ·
          refine ⟨5202954356318963144129731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6937272475091950858839641 5202954356318963144129731)
          ·
            refine ⟨7804431534478444716194597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5202954356318963144129731 7804431534478444716194597)
            ·
              refine ⟨1463330912714708384286487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7804431534478444716194597 1463330912714708384286487)
              ·
                refine ⟨2194996369072062576429731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1463330912714708384286487 2194996369072062576429731)
                ·
                  refine ⟨3292494553608093864644597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2194996369072062576429731 3292494553608093864644597)
                  ·
                    refine ⟨308671364400758799810431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3292494553608093864644597 308671364400758799810431)
                    ·
                      rfl

theorem cell23_1803406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_1803406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803406 prefixEnd_1803406 := by exact prefixLift 1803406
  have htrace : WordTrace (prefixWord ++ tailWord_1803406) baseStart_1803406 baseEnd_1803406 := by
    simpa [prefixWord, tailWord_1803406, baseEnd_1803406] using wordTrace_append hprefix tailTrace_1803406
  have hstable : (prefixWord ++ tailWord_1803406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803406).length < 2 ^ (prefixWord ++ tailWord_1803406).sum := by decide
  have hdescent : baseEnd_1803406 < baseStart_1803406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803449 : List Nat := [1, 2, 1, 4, 1, 5, 2, 7]
def baseStart_1803449 : Nat := 118140960795 + 1803449 * 2 ^ 59
def prefixEnd_1803449 : Nat := 4983230072969 + 3 ^ 40 * 1803449 * 2
def baseEnd_1803449 : Nat := 34297636032237767821985

theorem tailTrace_1803449 : CollatzResearch.WordTrace tailWord_1803449 prefixEnd_1803449 34297636032237767821985 := by
  unfold tailWord_1803449
  simp only [CollatzResearch.WordTrace]
  refine ⟨65777188843419752412813401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43851459228946501608542267 65777188843419752412813401)
  ·
    refine ⟨49332891632564814309610051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65777188843419752412813401 49332891632564814309610051)
    ·
      refine ⟨73999337448847221464415077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49332891632564814309610051 73999337448847221464415077)
      ·
        refine ⟨13874875771658854024577827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73999337448847221464415077 13874875771658854024577827)
        ·
          refine ⟨20812313657488281036866741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13874875771658854024577827 20812313657488281036866741)
          ·
            refine ⟨1951154405389526347206257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20812313657488281036866741 1951154405389526347206257)
            ·
              refine ⟨1463365804042144760404693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1951154405389526347206257 1463365804042144760404693)
              ·
                refine ⟨34297636032237767821985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1463365804042144760404693 34297636032237767821985)
                ·
                  rfl

theorem cell23_1803449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 7].length) (baseStart_1803449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803449 prefixEnd_1803449 := by exact prefixLift 1803449
  have htrace : WordTrace (prefixWord ++ tailWord_1803449) baseStart_1803449 baseEnd_1803449 := by
    simpa [prefixWord, tailWord_1803449, baseEnd_1803449] using wordTrace_append hprefix tailTrace_1803449
  have hstable : (prefixWord ++ tailWord_1803449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803449).length < 2 ^ (prefixWord ++ tailWord_1803449).sum := by decide
  have hdescent : baseEnd_1803449 < baseStart_1803449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803477 : List Nat := [1, 3, 2, 4, 1, 2, 3, 2, 1, 2, 2]
def baseStart_1803477 : Nat := 118140960795 + 1803477 * 2 ^ 59
def prefixEnd_1803477 : Nat := 4983230072969 + 3 ^ 40 * 1803477 * 2
def baseEnd_1803477 : Nat := 926050550328745621643467

theorem tailTrace_1803477 : CollatzResearch.WordTrace tailWord_1803477 prefixEnd_1803477 926050550328745621643467 := by
  unfold tailWord_1803477
  simp only [CollatzResearch.WordTrace]
  refine ⟨65778210087318313194832685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43852140058212208796555123 65778210087318313194832685)
  ·
    refine ⟨24666828782744367448062257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65778210087318313194832685 24666828782744367448062257)
    ·
      refine ⟨18500121587058275586046693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24666828782744367448062257 18500121587058275586046693)
      ·
        refine ⟨3468772797573426672383755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18500121587058275586046693 3468772797573426672383755)
        ·
          refine ⟨5203159196360140008575633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3468772797573426672383755 5203159196360140008575633)
          ·
            refine ⟨3902369397270105006431725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5203159196360140008575633 3902369397270105006431725)
            ·
              refine ⟨1463388523976289377411897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3902369397270105006431725 1463388523976289377411897)
              ·
                refine ⟨1097541392982217033058923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1463388523976289377411897 1097541392982217033058923)
                ·
                  refine ⟨1646312089473325549588385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097541392982217033058923 1646312089473325549588385)
                  ·
                    refine ⟨1234734067104994162191289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1646312089473325549588385 1234734067104994162191289)
                    ·
                      refine ⟨926050550328745621643467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1234734067104994162191289 926050550328745621643467)
                      ·
                        rfl

theorem cell23_1803477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_1803477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803477 prefixEnd_1803477 := by exact prefixLift 1803477
  have htrace : WordTrace (prefixWord ++ tailWord_1803477) baseStart_1803477 baseEnd_1803477 := by
    simpa [prefixWord, tailWord_1803477, baseEnd_1803477] using wordTrace_append hprefix tailTrace_1803477
  have hstable : (prefixWord ++ tailWord_1803477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803477).length < 2 ^ (prefixWord ++ tailWord_1803477).sum := by decide
  have hdescent : baseEnd_1803477 < baseStart_1803477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803482 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4]
def baseStart_1803482 : Nat := 118140960795 + 1803482 * 2 ^ 59
def prefixEnd_1803482 : Nat := 4983230072969 + 3 ^ 40 * 1803482 * 2
def baseEnd_1803482 : Nat := 926053117732018102080943

theorem tailTrace_1803482 : CollatzResearch.WordTrace tailWord_1803482 prefixEnd_1803482 926053117732018102080943 := by
  unfold tailWord_1803482
  simp only [CollatzResearch.WordTrace]
  refine ⟨16444598113075049762191175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43852261634866799365843133 16444598113075049762191175)
  ·
    refine ⟨24666897169612574643286763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16444598113075049762191175 24666897169612574643286763)
    ·
      refine ⟨37000345754418861964930145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24666897169612574643286763 37000345754418861964930145)
      ·
        refine ⟨27750259315814146473697609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37000345754418861964930145 27750259315814146473697609)
        ·
          refine ⟨20812694486860609855273207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27750259315814146473697609 20812694486860609855273207)
          ·
            refine ⟨31219041730290914782909811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20812694486860609855273207 31219041730290914782909811)
            ·
              refine ⟨46828562595436372174364717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31219041730290914782909811 46828562595436372174364717)
              ·
                refine ⟨17560710973288639565386769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46828562595436372174364717 17560710973288639565386769)
                ·
                  refine ⟨13170533229966479674040077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17560710973288639565386769 13170533229966479674040077)
                  ·
                    refine ⟨4938949961237429877765029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13170533229966479674040077 4938949961237429877765029)
                    ·
                      refine ⟨926053117732018102080943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4938949961237429877765029 926053117732018102080943)
                      ·
                        rfl

theorem cell23_1803482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_1803482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803482 prefixEnd_1803482 := by exact prefixLift 1803482
  have htrace : WordTrace (prefixWord ++ tailWord_1803482) baseStart_1803482 baseEnd_1803482 := by
    simpa [prefixWord, tailWord_1803482, baseEnd_1803482] using wordTrace_append hprefix tailTrace_1803482
  have hstable : (prefixWord ++ tailWord_1803482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803482).length < 2 ^ (prefixWord ++ tailWord_1803482).sum := by decide
  have hdescent : baseEnd_1803482 < baseStart_1803482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803492 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 2, 6]
def baseStart_1803492 : Nat := 118140960795 + 1803492 * 2 ^ 59
def prefixEnd_1803492 : Nat := 4983230072969 + 3 ^ 40 * 1803492 * 2
def baseEnd_1803492 : Nat := 308686084179521020985299

theorem tailTrace_1803492 : CollatzResearch.WordTrace tailWord_1803492 prefixEnd_1803492 308686084179521020985299 := by
  unfold tailWord_1803492
  simp only [CollatzResearch.WordTrace]
  refine ⟨32889378591131985378314365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43852504788175980504419153 32889378591131985378314365)
  ·
    refine ⟨12333516971674494516867887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32889378591131985378314365 12333516971674494516867887)
    ·
      refine ⟨18500275457511741775301831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12333516971674494516867887 18500275457511741775301831)
      ·
        refine ⟨27750413186267612662952747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18500275457511741775301831 27750413186267612662952747)
        ·
          refine ⟨41625619779401418994429121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27750413186267612662952747 41625619779401418994429121)
          ·
            refine ⟨31219214834551064245821841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41625619779401418994429121 31219214834551064245821841)
            ·
              refine ⟨23414411125913298184366381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31219214834551064245821841 23414411125913298184366381)
              ·
                refine ⟨8780404172217486819137393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23414411125913298184366381 8780404172217486819137393)
                ·
                  refine ⟨6585303129163115114353045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8780404172217486819137393 6585303129163115114353045)
                  ·
                    refine ⟨308686084179521020985299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6585303129163115114353045 308686084179521020985299)
                    ·
                      rfl

theorem cell23_1803492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_1803492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803492 prefixEnd_1803492 := by exact prefixLift 1803492
  have htrace : WordTrace (prefixWord ++ tailWord_1803492) baseStart_1803492 baseEnd_1803492 := by
    simpa [prefixWord, tailWord_1803492, baseEnd_1803492] using wordTrace_append hprefix tailTrace_1803492
  have hstable : (prefixWord ++ tailWord_1803492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803492).length < 2 ^ (prefixWord ++ tailWord_1803492).sum := by decide
  have hdescent : baseEnd_1803492 < baseStart_1803492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803493 : List Nat := [1, 3, 1, 4, 3, 1, 1, 3, 2, 1, 3]
def baseStart_1803493 : Nat := 118140960795 + 1803493 * 2 ^ 59
def prefixEnd_1803493 : Nat := 4983230072969 + 3 ^ 40 * 1803493 * 2
def baseEnd_1803493 : Nat := 926058766019217559043393

theorem tailTrace_1803493 : CollatzResearch.WordTrace tailWord_1803493 prefixEnd_1803493 926058766019217559043393 := by
  unfold tailWord_1803493
  simp only [CollatzResearch.WordTrace]
  refine ⟨65778793655260347927415133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43852529103506898618276755 65778793655260347927415133)
  ·
    refine ⟨24667047620722630472780675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65778793655260347927415133 24667047620722630472780675)
    ·
      refine ⟨37000571431083945709171013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24667047620722630472780675 37000571431083945709171013)
      ·
        refine ⟨6937607143328239820469565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37000571431083945709171013 6937607143328239820469565)
        ·
          refine ⟨2601602678748089932676087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6937607143328239820469565 2601602678748089932676087)
          ·
            refine ⟨3902404018122134899014131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2601602678748089932676087 3902404018122134899014131)
            ·
              refine ⟨5853606027183202348521197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3902404018122134899014131 5853606027183202348521197)
              ·
                refine ⟨2195102260193700880695449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5853606027183202348521197 2195102260193700880695449)
                ·
                  refine ⟨1646326695145275660521587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2195102260193700880695449 1646326695145275660521587)
                  ·
                    refine ⟨2469490042717913490782381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1646326695145275660521587 2469490042717913490782381)
                    ·
                      refine ⟨926058766019217559043393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2469490042717913490782381 926058766019217559043393)
                      ·
                        rfl

theorem cell23_1803493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_1803493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803493 prefixEnd_1803493 := by exact prefixLift 1803493
  have htrace : WordTrace (prefixWord ++ tailWord_1803493) baseStart_1803493 baseEnd_1803493 := by
    simpa [prefixWord, tailWord_1803493, baseEnd_1803493] using wordTrace_append hprefix tailTrace_1803493
  have hstable : (prefixWord ++ tailWord_1803493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803493).length < 2 ^ (prefixWord ++ tailWord_1803493).sum := by decide
  have hdescent : baseEnd_1803493 < baseStart_1803493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803512 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 6, 2, 4]
def baseStart_1803512 : Nat := 118140960795 + 1803512 * 2 ^ 59
def prefixEnd_1803512 : Nat := 4983230072969 + 3 ^ 40 * 1803512 * 2
def baseEnd_1803512 : Nat := 926068522151652984705805

theorem tailTrace_1803512 : CollatzResearch.WordTrace tailWord_1803512 prefixEnd_1803512 926068522151652984705805 := by
  unfold tailWord_1803512
  simp only [CollatzResearch.WordTrace]
  refine ⟨32889743321095757086178395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43852991094794342781571193 32889743321095757086178395)
  ·
    refine ⟨49334614981643635629267593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32889743321095757086178395 49334614981643635629267593)
    ·
      refine ⟨37000961236232726721950695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49334614981643635629267593 37000961236232726721950695)
      ·
        refine ⟨55501441854349090082926043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37000961236232726721950695 55501441854349090082926043)
        ·
          refine ⟨83252162781523635124389065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55501441854349090082926043 83252162781523635124389065)
          ·
            refine ⟨62439122086142726343291799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83252162781523635124389065 62439122086142726343291799)
            ·
              refine ⟨93658683129214089514937699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62439122086142726343291799 93658683129214089514937699)
              ·
                refine ⟨140488024693821134272406549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93658683129214089514937699 140488024693821134272406549)
                ·
                  refine ⟨6585376157522865669019057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 140488024693821134272406549 6585376157522865669019057)
                  ·
                    refine ⟨4939032118142149251764293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6585376157522865669019057 4939032118142149251764293)
                    ·
                      refine ⟨926068522151652984705805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4939032118142149251764293 926068522151652984705805)
                      ·
                        rfl

theorem cell23_1803512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_1803512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803512 prefixEnd_1803512 := by exact prefixLift 1803512
  have htrace : WordTrace (prefixWord ++ tailWord_1803512) baseStart_1803512 baseEnd_1803512 := by
    simpa [prefixWord, tailWord_1803512, baseEnd_1803512] using wordTrace_append hprefix tailTrace_1803512
  have hstable : (prefixWord ++ tailWord_1803512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803512).length < 2 ^ (prefixWord ++ tailWord_1803512).sum := by decide
  have hdescent : baseEnd_1803512 < baseStart_1803512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803569 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 1, 7]
def baseStart_1803569 : Nat := 118140960795 + 1803569 * 2 ^ 59
def prefixEnd_1803569 : Nat := 4983230072969 + 3 ^ 40 * 1803569 * 2
def baseEnd_1803569 : Nat := 308699263516319753897681

theorem tailTrace_1803569 : CollatzResearch.WordTrace tailWord_1803569 prefixEnd_1803569 308699263516319753897681 := by
  unfold tailWord_1803569
  simp only [CollatzResearch.WordTrace]
  refine ⟨65781565602985012907181761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43854377068656675271454507 65781565602985012907181761)
  ·
    refine ⟨49336174202238759680386321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65781565602985012907181761 49336174202238759680386321)
    ·
      refine ⟨37002130651679069760289741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49336174202238759680386321 37002130651679069760289741)
      ·
        refine ⟨13875798994379651160108653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37002130651679069760289741 13875798994379651160108653)
        ·
          refine ⟨5203424622892369185040745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13875798994379651160108653 5203424622892369185040745)
          ·
            refine ⟨3902568467169276888780559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5203424622892369185040745 3902568467169276888780559)
            ·
              refine ⟨5853852700753915333170839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3902568467169276888780559 5853852700753915333170839)
              ·
                refine ⟨8780779051130872999756259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5853852700753915333170839 8780779051130872999756259)
                ·
                  refine ⟨13171168576696309499634389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8780779051130872999756259 13171168576696309499634389)
                  ·
                    refine ⟨308699263516319753897681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13171168576696309499634389 308699263516319753897681)
                    ·
                      rfl

theorem cell23_1803569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_1803569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803569 prefixEnd_1803569 := by exact prefixLift 1803569
  have htrace : WordTrace (prefixWord ++ tailWord_1803569) baseStart_1803569 baseEnd_1803569 := by
    simpa [prefixWord, tailWord_1803569, baseEnd_1803569] using wordTrace_append hprefix tailTrace_1803569
  have hstable : (prefixWord ++ tailWord_1803569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803569).length < 2 ^ (prefixWord ++ tailWord_1803569).sum := by decide
  have hdescent : baseEnd_1803569 < baseStart_1803569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803589 : List Nat := [1, 3, 1, 1, 1, 2, 1, 6, 2, 1, 4]
def baseStart_1803589 : Nat := 118140960795 + 1803589 * 2 ^ 59
def prefixEnd_1803589 : Nat := 4983230072969 + 3 ^ 40 * 1803589 * 2
def baseEnd_1803589 : Nat := 926108060162049183442951

theorem tailTrace_1803589 : CollatzResearch.WordTrace tailWord_1803589 prefixEnd_1803589 926108060162049183442951 := by
  unfold tailWord_1803589
  simp only [CollatzResearch.WordTrace]
  refine ⟨65782295062912556322909821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43854863375275037548606547 65782295062912556322909821)
  ·
    refine ⟨24668360648592208621091183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65782295062912556322909821 24668360648592208621091183)
    ·
      refine ⟨37002540972888312931636775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24668360648592208621091183 37002540972888312931636775)
      ·
        refine ⟨55503811459332469397455163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37002540972888312931636775 55503811459332469397455163)
        ·
          refine ⟨83255717188998704096182745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55503811459332469397455163 83255717188998704096182745)
          ·
            refine ⟨62441787891749028072137059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83255717188998704096182745 62441787891749028072137059)
            ·
              refine ⟨93662681837623542108205589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62441787891749028072137059 93662681837623542108205589)
              ·
                refine ⟨4390438211138603536322137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93662681837623542108205589 4390438211138603536322137)
                ·
                  refine ⟨3292828658353952652241603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4390438211138603536322137 3292828658353952652241603)
                  ·
                    refine ⟨4939242987530928978362405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3292828658353952652241603 4939242987530928978362405)
                    ·
                      refine ⟨926108060162049183442951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4939242987530928978362405 926108060162049183442951)
                      ·
                        rfl

theorem cell23_1803589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_1803589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803589 prefixEnd_1803589 := by exact prefixLift 1803589
  have htrace : WordTrace (prefixWord ++ tailWord_1803589) baseStart_1803589 baseEnd_1803589 := by
    simpa [prefixWord, tailWord_1803589, baseEnd_1803589] using wordTrace_append hprefix tailTrace_1803589
  have hstable : (prefixWord ++ tailWord_1803589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803589).length < 2 ^ (prefixWord ++ tailWord_1803589).sum := by decide
  have hdescent : baseEnd_1803589 < baseStart_1803589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803590 : List Nat := [6, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_1803590 : Nat := 118140960795 + 1803590 * 2 ^ 59
def prefixEnd_1803590 : Nat := 4983230072969 + 3 ^ 40 * 1803590 * 2
def baseEnd_1803590 : Nat := 102900952626967075503383

theorem tailTrace_1803590 : CollatzResearch.WordTrace tailWord_1803590 prefixEnd_1803590 102900952626967075503383 := by
  unfold tailWord_1803590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2055697860497154171678007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43854887690605955662464149 2055697860497154171678007)
  ·
    refine ⟨3083546790745731257517011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2055697860497154171678007 3083546790745731257517011)
    ·
      refine ⟨4625320186118596886275517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3083546790745731257517011 4625320186118596886275517)
      ·
        refine ⟨1734495069794473832353319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4625320186118596886275517 1734495069794473832353319)
        ·
          refine ⟨2601742604691710748529979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1734495069794473832353319 2601742604691710748529979)
          ·
            refine ⟨3902613907037566122794969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2601742604691710748529979 3902613907037566122794969)
            ·
              refine ⟨2926960430278174592096227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3902613907037566122794969 2926960430278174592096227)
              ·
                refine ⟨4390440645417261888144341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2926960430278174592096227 4390440645417261888144341)
                ·
                  refine ⟨102900952626967075503383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4390440645417261888144341 102900952626967075503383)
                  ·
                    rfl

theorem cell23_1803590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_1803590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803590 prefixEnd_1803590 := by exact prefixLift 1803590
  have htrace : WordTrace (prefixWord ++ tailWord_1803590) baseStart_1803590 baseEnd_1803590 := by
    simpa [prefixWord, tailWord_1803590, baseEnd_1803590] using wordTrace_append hprefix tailTrace_1803590
  have hstable : (prefixWord ++ tailWord_1803590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803590).length < 2 ^ (prefixWord ++ tailWord_1803590).sum := by decide
  have hdescent : baseEnd_1803590 < baseStart_1803590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803609 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 1, 4, 3]
def baseStart_1803609 : Nat := 118140960795 + 1803609 * 2 ^ 59
def prefixEnd_1803609 : Nat := 4983230072969 + 3 ^ 40 * 1803609 * 2
def baseEnd_1803609 : Nat := 926118329775139105192859

theorem tailTrace_1803609 : CollatzResearch.WordTrace tailWord_1803609 prefixEnd_1803609 926118329775139105192859 := by
  unfold tailWord_1803609
  simp only [CollatzResearch.WordTrace]
  refine ⟨65783024522840099738637881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43855349681893399825758587 65783024522840099738637881)
  ·
    refine ⟨49337268392130074803978411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65783024522840099738637881 49337268392130074803978411)
    ·
      refine ⟨74005902588195112205967617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49337268392130074803978411 74005902588195112205967617)
      ·
        refine ⟨55504426941146334154475713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74005902588195112205967617 55504426941146334154475713)
        ·
          refine ⟨41628320205859750615856785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55504426941146334154475713 41628320205859750615856785)
          ·
            refine ⟨31221240154394812961892589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41628320205859750615856785 31221240154394812961892589)
            ·
              refine ⟨11707965057898054860709721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31221240154394812961892589 11707965057898054860709721)
              ·
                refine ⟨8780973793423541145532291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11707965057898054860709721 8780973793423541145532291)
                ·
                  refine ⟨13171460690135311718298437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8780973793423541145532291 13171460690135311718298437)
                  ·
                    refine ⟨2469648879400370947180957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13171460690135311718298437 2469648879400370947180957)
                    ·
                      refine ⟨926118329775139105192859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2469648879400370947180957 926118329775139105192859)
                      ·
                        rfl

theorem cell23_1803609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_1803609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803609 prefixEnd_1803609 := by exact prefixLift 1803609
  have htrace : WordTrace (prefixWord ++ tailWord_1803609) baseStart_1803609 baseEnd_1803609 := by
    simpa [prefixWord, tailWord_1803609, baseEnd_1803609] using wordTrace_append hprefix tailTrace_1803609
  have hstable : (prefixWord ++ tailWord_1803609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803609).length < 2 ^ (prefixWord ++ tailWord_1803609).sum := by decide
  have hdescent : baseEnd_1803609 < baseStart_1803609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803616 : List Nat := [2, 1, 1, 3, 4, 1, 2, 2, 3, 4]
def baseStart_1803616 : Nat := 118140960795 + 1803616 * 2 ^ 59
def prefixEnd_1803616 : Nat := 4983230072969 + 3 ^ 40 * 1803616 * 2
def baseEnd_1803616 : Nat := 308707308046573525935109

theorem tailTrace_1803616 : CollatzResearch.WordTrace tailWord_1803616 prefixEnd_1803616 308707308046573525935109 := by
  unfold tailWord_1803616
  simp only [CollatzResearch.WordTrace]
  refine ⟨32891639916907369967071351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43855519889209826622761801 32891639916907369967071351)
  ·
    refine ⟨49337459875361054950607027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32891639916907369967071351 49337459875361054950607027)
    ·
      refine ⟨74006189813041582425910541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49337459875361054950607027 74006189813041582425910541)
      ·
        refine ⟨27752321179890593409716453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74006189813041582425910541 27752321179890593409716453)
        ·
          refine ⟨5203560221229486264321835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27752321179890593409716453 5203560221229486264321835)
          ·
            refine ⟨7805340331844229396482753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5203560221229486264321835 7805340331844229396482753)
            ·
              refine ⟨5854005248883172047362065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7805340331844229396482753 5854005248883172047362065)
              ·
                refine ⟨4390503936662379035521549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5854005248883172047362065 4390503936662379035521549)
                ·
                  refine ⟨1646438976248392138320581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4390503936662379035521549 1646438976248392138320581)
                  ·
                    refine ⟨308707308046573525935109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1646438976248392138320581 308707308046573525935109)
                    ·
                      rfl

theorem cell23_1803616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 3, 4].length) (baseStart_1803616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803616 prefixEnd_1803616 := by exact prefixLift 1803616
  have htrace : WordTrace (prefixWord ++ tailWord_1803616) baseStart_1803616 baseEnd_1803616 := by
    simpa [prefixWord, tailWord_1803616, baseEnd_1803616] using wordTrace_append hprefix tailTrace_1803616
  have hstable : (prefixWord ++ tailWord_1803616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803616).length < 2 ^ (prefixWord ++ tailWord_1803616).sum := by decide
  have hdescent : baseEnd_1803616 < baseStart_1803616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803629 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 8]
def baseStart_1803629 : Nat := 118140960795 + 1803629 * 2 ^ 59
def prefixEnd_1803629 : Nat := 4983230072969 + 3 ^ 40 * 1803629 * 2
def baseEnd_1803629 : Nat := 102903177709803225215863

theorem tailTrace_1803629 : CollatzResearch.WordTrace tailWord_1803629 prefixEnd_1803629 102903177709803225215863 := by
  unfold tailWord_1803629
  simp only [CollatzResearch.WordTrace]
  refine ⟨65783753982767643154365941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43855835988511762102910627 65783753982767643154365941)
  ·
    refine ⟨6167226935884466545721807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65783753982767643154365941 6167226935884466545721807)
    ·
      refine ⟨9250840403826699818582711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6167226935884466545721807 9250840403826699818582711)
      ·
        refine ⟨13876260605740049727874067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9250840403826699818582711 13876260605740049727874067)
        ·
          refine ⟨20814390908610074591811101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13876260605740049727874067 20814390908610074591811101)
          ·
            refine ⟨7805396590728777971929163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20814390908610074591811101 7805396590728777971929163)
            ·
              refine ⟨11708094886093166957893745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7805396590728777971929163 11708094886093166957893745)
              ·
                refine ⟨8781071164569875218420309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11708094886093166957893745 8781071164569875218420309)
                ·
                  refine ⟨102903177709803225215863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8781071164569875218420309 102903177709803225215863)
                  ·
                    rfl

theorem cell23_1803629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_1803629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803629 prefixEnd_1803629 := by exact prefixLift 1803629
  have htrace : WordTrace (prefixWord ++ tailWord_1803629) baseStart_1803629 baseEnd_1803629 := by
    simpa [prefixWord, tailWord_1803629, baseEnd_1803629] using wordTrace_append hprefix tailTrace_1803629
  have hstable : (prefixWord ++ tailWord_1803629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803629).length < 2 ^ (prefixWord ++ tailWord_1803629).sum := by decide
  have hdescent : baseEnd_1803629 < baseStart_1803629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803633 : List Nat := [1, 2, 2, 2, 1, 2, 5, 3, 1, 4]
def baseStart_1803633 : Nat := 118140960795 + 1803633 * 2 ^ 59
def prefixEnd_1803633 : Nat := 4983230072969 + 3 ^ 40 * 1803633 * 2
def baseEnd_1803633 : Nat := 308710217770282337097583

theorem tailTrace_1803633 : CollatzResearch.WordTrace tailWord_1803633 prefixEnd_1803633 308710217770282337097583 := by
  unfold tailWord_1803633
  simp only [CollatzResearch.WordTrace]
  refine ⟨65783899874753151837511553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43855933249835434558341035 65783899874753151837511553)
  ·
    refine ⟨49337924906064863878133665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65783899874753151837511553 49337924906064863878133665)
    ·
      refine ⟨37003443679548647908600249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49337924906064863878133665 37003443679548647908600249)
      ·
        refine ⟨27752582759661485931450187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37003443679548647908600249 27752582759661485931450187)
        ·
          refine ⟨41628874139492228897175281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27752582759661485931450187 41628874139492228897175281)
          ·
            refine ⟨31221655604619171672881461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41628874139492228897175281 31221655604619171672881461)
            ·
              refine ⟨2927030212933047344332637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31221655604619171672881461 2927030212933047344332637)
              ·
                refine ⟨1097636329849892754124739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2927030212933047344332637 1097636329849892754124739)
                ·
                  refine ⟨1646454494774839131187109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097636329849892754124739 1646454494774839131187109)
                  ·
                    refine ⟨308710217770282337097583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1646454494774839131187109 308710217770282337097583)
                    ·
                      rfl

theorem cell23_1803633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 1, 4].length) (baseStart_1803633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803633 prefixEnd_1803633 := by exact prefixLift 1803633
  have htrace : WordTrace (prefixWord ++ tailWord_1803633) baseStart_1803633 baseEnd_1803633 := by
    simpa [prefixWord, tailWord_1803633, baseEnd_1803633] using wordTrace_append hprefix tailTrace_1803633
  have hstable : (prefixWord ++ tailWord_1803633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803633).length < 2 ^ (prefixWord ++ tailWord_1803633).sum := by decide
  have hdescent : baseEnd_1803633 < baseStart_1803633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803650 : List Nat := [3, 4, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1803650 : Nat := 118140960795 + 1803650 * 2 ^ 59
def prefixEnd_1803650 : Nat := 4983230072969 + 3 ^ 40 * 1803650 * 2
def baseEnd_1803650 : Nat := 308713127493991148260057

theorem tailTrace_1803650 : CollatzResearch.WordTrace tailWord_1803650 prefixEnd_1803650 308713127493991148260057 := by
  unfold tailWord_1803650
  simp only [CollatzResearch.WordTrace]
  refine ⟨16446129978922890935220101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43856346610461042493920269 16446129978922890935220101)
  ·
    refine ⟨3083649371048042050353769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16446129978922890935220101 3083649371048042050353769)
    ·
      refine ⟨2312737028286031537765327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3083649371048042050353769 2312737028286031537765327)
      ·
        refine ⟨3469105542429047306647991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2312737028286031537765327 3469105542429047306647991)
        ·
          refine ⟨5203658313643570959971987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3469105542429047306647991 5203658313643570959971987)
          ·
            refine ⟨7805487470465356439957981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5203658313643570959971987 7805487470465356439957981)
            ·
              refine ⟨2927057801424508664984243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7805487470465356439957981 2927057801424508664984243)
              ·
                refine ⟨4390586702136762997476365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2927057801424508664984243 4390586702136762997476365)
                ·
                  refine ⟨1646470013301286124053637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4390586702136762997476365 1646470013301286124053637)
                  ·
                    refine ⟨308713127493991148260057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1646470013301286124053637 308713127493991148260057)
                    ·
                      rfl

theorem cell23_1803650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1803650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803650 prefixEnd_1803650 := by exact prefixLift 1803650
  have htrace : WordTrace (prefixWord ++ tailWord_1803650) baseStart_1803650 baseEnd_1803650 := by
    simpa [prefixWord, tailWord_1803650, baseEnd_1803650] using wordTrace_append hprefix tailTrace_1803650
  have hstable : (prefixWord ++ tailWord_1803650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803650).length < 2 ^ (prefixWord ++ tailWord_1803650).sum := by decide
  have hdescent : baseEnd_1803650 < baseStart_1803650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803659 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 3, 5]
def baseStart_1803659 : Nat := 118140960795 + 1803659 * 2 ^ 59
def prefixEnd_1803659 : Nat := 4983230072969 + 3 ^ 40 * 1803659 * 2
def baseEnd_1803659 : Nat := 308714667935954636522543

theorem tailTrace_1803659 : CollatzResearch.WordTrace tailWord_1803659 prefixEnd_1803659 308714667935954636522543 := by
  unfold tailWord_1803659
  simp only [CollatzResearch.WordTrace]
  refine ⟨65784848172658958277958031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43856565448439305518638687 65784848172658958277958031)
  ·
    refine ⟨98677272258988437416937047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65784848172658958277958031 98677272258988437416937047)
    ·
      refine ⟨148015908388482656125405571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98677272258988437416937047 148015908388482656125405571)
      ·
        refine ⟨222023862582723984188108357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148015908388482656125405571 222023862582723984188108357)
        ·
          refine ⟨41629474234260747035270317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222023862582723984188108357 41629474234260747035270317)
          ·
            refine ⟨15611052837847780138226369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41629474234260747035270317 15611052837847780138226369)
            ·
              refine ⟨11708289628385835103669777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15611052837847780138226369 11708289628385835103669777)
              ·
                refine ⟨8781217221289376327752333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11708289628385835103669777 8781217221289376327752333)
                ·
                  refine ⟨3292956457983516122907125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8781217221289376327752333 3292956457983516122907125)
                  ·
                    refine ⟨308714667935954636522543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3292956457983516122907125 308714667935954636522543)
                    ·
                      rfl

theorem cell23_1803659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 5].length) (baseStart_1803659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803659 prefixEnd_1803659 := by exact prefixLift 1803659
  have htrace : WordTrace (prefixWord ++ tailWord_1803659) baseStart_1803659 baseEnd_1803659 := by
    simpa [prefixWord, tailWord_1803659, baseEnd_1803659] using wordTrace_append hprefix tailTrace_1803659
  have hstable : (prefixWord ++ tailWord_1803659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803659).length < 2 ^ (prefixWord ++ tailWord_1803659).sum := by decide
  have hdescent : baseEnd_1803659 < baseStart_1803659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803683 : List Nat := [1, 1, 1, 4, 1, 3, 4, 1, 2, 3, 2]
def baseStart_1803683 : Nat := 118140960795 + 1803683 * 2 ^ 59
def prefixEnd_1803683 : Nat := 4983230072969 + 3 ^ 40 * 1803683 * 2
def baseEnd_1803683 : Nat := 926156327343571815667519

theorem tailTrace_1803683 : CollatzResearch.WordTrace tailWord_1803683 prefixEnd_1803683 926156327343571815667519 := by
  unfold tailWord_1803683
  simp only [CollatzResearch.WordTrace]
  refine ⟨65785723524572010376831703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43857149016381340251221135 65785723524572010376831703)
  ·
    refine ⟨98678585286858015565247555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65785723524572010376831703 98678585286858015565247555)
    ·
      refine ⟨148017877930287023347871333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98678585286858015565247555 148017877930287023347871333)
      ·
        refine ⟨27753352111928816877725875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148017877930287023347871333 27753352111928816877725875)
        ·
          refine ⟨41630028167893225316588813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27753352111928816877725875 41630028167893225316588813)
          ·
            refine ⟨15611260562959959493720805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41630028167893225316588813 15611260562959959493720805)
            ·
              refine ⟨2927111355554992405072651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15611260562959959493720805 2927111355554992405072651)
              ·
                refine ⟨4390667033332488607608977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2927111355554992405072651 4390667033332488607608977)
                ·
                  refine ⟨3293000274999366455706733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4390667033332488607608977 3293000274999366455706733)
                  ·
                    refine ⟨1234875103124762420890025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3293000274999366455706733 1234875103124762420890025)
                    ·
                      refine ⟨926156327343571815667519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1234875103124762420890025 926156327343571815667519)
                      ·
                        rfl

theorem cell23_1803683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_1803683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803683 prefixEnd_1803683 := by exact prefixLift 1803683
  have htrace : WordTrace (prefixWord ++ tailWord_1803683) baseStart_1803683 baseEnd_1803683 := by
    simpa [prefixWord, tailWord_1803683, baseEnd_1803683] using wordTrace_append hprefix tailTrace_1803683
  have hstable : (prefixWord ++ tailWord_1803683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803683).length < 2 ^ (prefixWord ++ tailWord_1803683).sum := by decide
  have hdescent : baseEnd_1803683 < baseStart_1803683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803726 : List Nat := [4, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_1803726 : Nat := 118140960795 + 1803726 * 2 ^ 59
def prefixEnd_1803726 : Nat := 4983230072969 + 3 ^ 40 * 1803726 * 2
def baseEnd_1803726 : Nat := 926178407011715147429821

theorem tailTrace_1803726 : CollatzResearch.WordTrace tailWord_1803726 prefixEnd_1803726 926178407011715147429821 := by
  unfold tailWord_1803726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8223411482927028590080879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43858194575610819147098021 8223411482927028590080879)
  ·
    refine ⟨12335117224390542885121319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8223411482927028590080879 12335117224390542885121319)
    ·
      refine ⟨18502675836585814327681979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12335117224390542885121319 18502675836585814327681979)
      ·
        refine ⟨27754013754878721491522969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18502675836585814327681979 27754013754878721491522969)
        ·
          refine ⟨20815510316159041118642227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27754013754878721491522969 20815510316159041118642227)
          ·
            refine ⟨31223265474238561677963341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20815510316159041118642227 31223265474238561677963341)
            ·
              refine ⟨11708724552839460629236253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31223265474238561677963341 11708724552839460629236253)
              ·
                refine ⟨4390771707314797735963595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11708724552839460629236253 4390771707314797735963595)
                ·
                  refine ⟨6586157560972196603945393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4390771707314797735963595 6586157560972196603945393)
                  ·
                    refine ⟨4939618170729147452959045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6586157560972196603945393 4939618170729147452959045)
                    ·
                      refine ⟨926178407011715147429821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4939618170729147452959045 926178407011715147429821)
                      ·
                        rfl

theorem cell23_1803726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_1803726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803726 prefixEnd_1803726 := by exact prefixLift 1803726
  have htrace : WordTrace (prefixWord ++ tailWord_1803726) baseStart_1803726 baseEnd_1803726 := by
    simpa [prefixWord, tailWord_1803726, baseEnd_1803726] using wordTrace_append hprefix tailTrace_1803726
  have hstable : (prefixWord ++ tailWord_1803726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803726).length < 2 ^ (prefixWord ++ tailWord_1803726).sum := by decide
  have hdescent : baseEnd_1803726 < baseStart_1803726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803733 : List Nat := [1, 3, 2, 3, 1, 1, 2, 4, 1, 2, 3]
def baseStart_1803733 : Nat := 118140960795 + 1803733 * 2 ^ 59
def prefixEnd_1803733 : Nat := 4983230072969 + 3 ^ 40 * 1803733 * 2
def baseEnd_1803733 : Nat := 926182001376296620042289

theorem tailTrace_1803733 : CollatzResearch.WordTrace tailWord_1803733 prefixEnd_1803733 926182001376296620042289 := by
  unfold tailWord_1803733
  simp only [CollatzResearch.WordTrace]
  refine ⟨65787547174390868916151853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43858364782927245944101235 65787547174390868916151853)
  ·
    refine ⟨24670330190396575843556945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65787547174390868916151853 24670330190396575843556945)
    ·
      refine ⟨18502747642797431882667709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24670330190396575843556945 18502747642797431882667709)
      ·
        refine ⟨6938530366049036956000391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18502747642797431882667709 6938530366049036956000391)
        ·
          refine ⟨10407795549073555434000587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6938530366049036956000391 10407795549073555434000587)
          ·
            refine ⟨15611693323610333151000881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10407795549073555434000587 15611693323610333151000881)
            ·
              refine ⟨11708769992707749863250661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15611693323610333151000881 11708769992707749863250661)
              ·
                refine ⟨2195394373632703099359499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11708769992707749863250661 2195394373632703099359499)
                ·
                  refine ⟨3293091560449054649039249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2195394373632703099359499 3293091560449054649039249)
                  ·
                    refine ⟨2469818670336790986779437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3293091560449054649039249 2469818670336790986779437)
                    ·
                      refine ⟨926182001376296620042289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2469818670336790986779437 926182001376296620042289)
                      ·
                        rfl

theorem cell23_1803733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_1803733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803733 prefixEnd_1803733 := by exact prefixLift 1803733
  have htrace : WordTrace (prefixWord ++ tailWord_1803733) baseStart_1803733 baseEnd_1803733 := by
    simpa [prefixWord, tailWord_1803733, baseEnd_1803733] using wordTrace_append hprefix tailTrace_1803733
  have hstable : (prefixWord ++ tailWord_1803733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803733).length < 2 ^ (prefixWord ++ tailWord_1803733).sum := by decide
  have hdescent : baseEnd_1803733 < baseStart_1803733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803747 : List Nat := [1, 1, 1, 6, 2, 1, 1, 5, 1, 2, 2]
def baseStart_1803747 : Nat := 118140960795 + 1803747 * 2 ^ 59
def prefixEnd_1803747 : Nat := 4983230072969 + 3 ^ 40 * 1803747 * 2
def baseEnd_1803747 : Nat := 926189190105459565267225

theorem tailTrace_1803747 : CollatzResearch.WordTrace tailWord_1803747 prefixEnd_1803747 926189190105459565267225 := by
  unfold tailWord_1803747
  simp only [CollatzResearch.WordTrace]
  refine ⟨65788057796340149307161495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43858705197560099538107663 65788057796340149307161495)
  ·
    refine ⟨98682086694510223960742243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65788057796340149307161495 98682086694510223960742243)
    ·
      refine ⟨148023130041765335941113365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98682086694510223960742243 148023130041765335941113365)
      ·
        refine ⟨6938584220707750122239689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 148023130041765335941113365 6938584220707750122239689)
        ·
          refine ⟨5203938165530812591679767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6938584220707750122239689 5203938165530812591679767)
          ·
            refine ⟨7805907248296218887519651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5203938165530812591679767 7805907248296218887519651)
            ·
              refine ⟨11708860872444328331279477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7805907248296218887519651 11708860872444328331279477)
              ·
                refine ⟨1097705706791655781057451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11708860872444328331279477 1097705706791655781057451)
                ·
                  refine ⟨1646558560187483671586177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097705706791655781057451 1646558560187483671586177)
                  ·
                    refine ⟨1234918920140612753689633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1646558560187483671586177 1234918920140612753689633)
                    ·
                      refine ⟨926189190105459565267225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1234918920140612753689633 926189190105459565267225)
                      ·
                        rfl

theorem cell23_1803747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_1803747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803747 prefixEnd_1803747 := by exact prefixLift 1803747
  have htrace : WordTrace (prefixWord ++ tailWord_1803747) baseStart_1803747 baseEnd_1803747 := by
    simpa [prefixWord, tailWord_1803747, baseEnd_1803747] using wordTrace_append hprefix tailTrace_1803747
  have hstable : (prefixWord ++ tailWord_1803747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803747).length < 2 ^ (prefixWord ++ tailWord_1803747).sum := by decide
  have hdescent : baseEnd_1803747 < baseStart_1803747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803757 : List Nat := [1, 5, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_1803757 : Nat := 118140960795 + 1803757 * 2 ^ 59
def prefixEnd_1803757 : Nat := 4983230072969 + 3 ^ 40 * 1803757 * 2
def baseEnd_1803757 : Nat := 308731441637334842047393

theorem tailTrace_1803757 : CollatzResearch.WordTrace tailWord_1803757 prefixEnd_1803757 308731441637334842047393 := by
  unfold tailWord_1803757
  simp only [CollatzResearch.WordTrace]
  refine ⟨65788422526303921015025525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43858948350869280676683683 65788422526303921015025525)
  ·
    refine ⟨6167664611840992595158643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65788422526303921015025525 6167664611840992595158643)
    ·
      refine ⟨9251496917761488892737965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6167664611840992595158643 9251496917761488892737965)
      ·
        refine ⟨3469311344160558334776737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9251496917761488892737965 3469311344160558334776737)
        ·
          refine ⟨2601983508120418751082553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3469311344160558334776737 2601983508120418751082553)
          ·
            refine ⟨1951487631090314063311915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2601983508120418751082553 1951487631090314063311915)
            ·
              refine ⟨2927231446635471094967873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1951487631090314063311915 2927231446635471094967873)
              ·
                refine ⟨2195423584976603321225905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2927231446635471094967873 2195423584976603321225905)
                ·
                  refine ⟨1646567688732452490919429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2195423584976603321225905 1646567688732452490919429)
                  ·
                    refine ⟨308731441637334842047393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1646567688732452490919429 308731441637334842047393)
                    ·
                      rfl

theorem cell23_1803757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_1803757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803757 prefixEnd_1803757 := by exact prefixLift 1803757
  have htrace : WordTrace (prefixWord ++ tailWord_1803757) baseStart_1803757 baseEnd_1803757 := by
    simpa [prefixWord, tailWord_1803757, baseEnd_1803757] using wordTrace_append hprefix tailTrace_1803757
  have hstable : (prefixWord ++ tailWord_1803757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803757).length < 2 ^ (prefixWord ++ tailWord_1803757).sum := by decide
  have hdescent : baseEnd_1803757 < baseStart_1803757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803763 : List Nat := [1, 1, 1, 2, 2, 2, 2, 6, 2, 1, 3]
def baseStart_1803763 : Nat := 118140960795 + 1803763 * 2 ^ 59
def prefixEnd_1803763 : Nat := 4983230072969 + 3 ^ 40 * 1803763 * 2
def baseEnd_1803763 : Nat := 926197405795931502667151

theorem tailTrace_1803763 : CollatzResearch.WordTrace tailWord_1803763 prefixEnd_1803763 926197405795931502667151 := by
  unfold tailWord_1803763
  simp only [CollatzResearch.WordTrace]
  refine ⟨65788641364282184039743943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43859094242854789359829295 65788641364282184039743943)
  ·
    refine ⟨98682962046423276059615915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65788641364282184039743943 98682962046423276059615915)
    ·
      refine ⟨148024443069634914089423873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98682962046423276059615915 148024443069634914089423873)
      ·
        refine ⟨111018332302226185567067905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148024443069634914089423873 111018332302226185567067905)
        ·
          refine ⟨83263749226669639175300929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111018332302226185567067905 83263749226669639175300929)
          ·
            refine ⟨62447811920002229381475697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83263749226669639175300929 62447811920002229381475697)
            ·
              refine ⟨46835858940001672036106773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62447811920002229381475697 46835858940001672036106773)
              ·
                refine ⟨2195430887812578376692505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46835858940001672036106773 2195430887812578376692505)
                ·
                  refine ⟨1646573165859433782519379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2195430887812578376692505 1646573165859433782519379)
                  ·
                    refine ⟨2469859748789150673779069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1646573165859433782519379 2469859748789150673779069)
                    ·
                      refine ⟨926197405795931502667151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2469859748789150673779069 926197405795931502667151)
                      ·
                        rfl

theorem cell23_1803763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 1, 3].length) (baseStart_1803763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803763 prefixEnd_1803763 := by exact prefixLift 1803763
  have htrace : WordTrace (prefixWord ++ tailWord_1803763) baseStart_1803763 baseEnd_1803763 := by
    simpa [prefixWord, tailWord_1803763, baseEnd_1803763] using wordTrace_append hprefix tailTrace_1803763
  have hstable : (prefixWord ++ tailWord_1803763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803763).length < 2 ^ (prefixWord ++ tailWord_1803763).sum := by decide
  have hdescent : baseEnd_1803763 < baseStart_1803763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803774 : List Nat := [4, 2, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_1803774 : Nat := 118140960795 + 1803774 * 2 ^ 59
def prefixEnd_1803774 : Nat := 4983230072969 + 3 ^ 40 * 1803774 * 2
def baseEnd_1803774 : Nat := 308734351361043653209867

theorem tailTrace_1803774 : CollatzResearch.WordTrace tailWord_1803774 prefixEnd_1803774 308734351361043653209867 := by
  unfold tailWord_1803774
  simp only [CollatzResearch.WordTrace]
  refine ⟨8223630320905291614799297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43859361711494888612262917 8223630320905291614799297)
  ·
    refine ⟨6167722740678968711099473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8223630320905291614799297 6167722740678968711099473)
    ·
      refine ⟨4625792055509226533324605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6167722740678968711099473 4625792055509226533324605)
      ·
        refine ⟨1734672020815959949996727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4625792055509226533324605 1734672020815959949996727)
        ·
          refine ⟨2602008031223939924995091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1734672020815959949996727 2602008031223939924995091)
          ·
            refine ⟨3903012046835909887492637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602008031223939924995091 3903012046835909887492637)
            ·
              refine ⟨1463629517563466207809739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3903012046835909887492637 1463629517563466207809739)
              ·
                refine ⟨2195444276345199311714609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1463629517563466207809739 2195444276345199311714609)
                ·
                  refine ⟨1646583207258899483785957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2195444276345199311714609 1646583207258899483785957)
                  ·
                    refine ⟨308734351361043653209867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1646583207258899483785957 308734351361043653209867)
                    ·
                      rfl

theorem cell23_1803774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_1803774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803774 prefixEnd_1803774 := by exact prefixLift 1803774
  have htrace : WordTrace (prefixWord ++ tailWord_1803774) baseStart_1803774 baseEnd_1803774 := by
    simpa [prefixWord, tailWord_1803774, baseEnd_1803774] using wordTrace_append hprefix tailTrace_1803774
  have hstable : (prefixWord ++ tailWord_1803774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803774).length < 2 ^ (prefixWord ++ tailWord_1803774).sum := by decide
  have hdescent : baseEnd_1803774 < baseStart_1803774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803779 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 1, 8]
def baseStart_1803779 : Nat := 118140960795 + 1803779 * 2 ^ 59
def prefixEnd_1803779 : Nat := 4983230072969 + 3 ^ 40 * 1803779 * 2
def baseEnd_1803779 : Nat := 308735207162134480022359

theorem tailTrace_1803779 : CollatzResearch.WordTrace tailWord_1803779 prefixEnd_1803779 308735207162134480022359 := by
  unfold tailWord_1803779
  simp only [CollatzResearch.WordTrace]
  refine ⟨65789224932224218772326391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43859483288149479181550927 65789224932224218772326391)
  ·
    refine ⟨98683837398336328158489587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65789224932224218772326391 98683837398336328158489587)
    ·
      refine ⟨148025756097504492237734381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98683837398336328158489587 148025756097504492237734381)
      ·
        refine ⟨55509658536564184589150393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148025756097504492237734381 55509658536564184589150393)
        ·
          refine ⟨41632243902423138441862795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55509658536564184589150393 41632243902423138441862795)
          ·
            refine ⟨62448365853634707662794193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41632243902423138441862795 62448365853634707662794193)
            ·
              refine ⟨46836274390226030747095645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62448365853634707662794193 46836274390226030747095645)
              ·
                refine ⟨17563602896334761530160867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46836274390226030747095645 17563602896334761530160867)
                ·
                  refine ⟨26345404344502142295241301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17563602896334761530160867 26345404344502142295241301)
                  ·
                    refine ⟨308735207162134480022359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26345404344502142295241301 308735207162134480022359)
                    ·
                      rfl

theorem cell23_1803779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 8].length) (baseStart_1803779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803779 prefixEnd_1803779 := by exact prefixLift 1803779
  have htrace : WordTrace (prefixWord ++ tailWord_1803779) baseStart_1803779 baseEnd_1803779 := by
    simpa [prefixWord, tailWord_1803779, baseEnd_1803779] using wordTrace_append hprefix tailTrace_1803779
  have hstable : (prefixWord ++ tailWord_1803779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803779).length < 2 ^ (prefixWord ++ tailWord_1803779).sum := by decide
  have hdescent : baseEnd_1803779 < baseStart_1803779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803877 : List Nat := [1, 3, 1, 3, 3, 3, 2, 2, 5]
def baseStart_1803877 : Nat := 118140960795 + 1803877 * 2 ^ 59
def prefixEnd_1803877 : Nat := 4983230072969 + 3 ^ 40 * 1803877 * 2
def baseEnd_1803877 : Nat := 102917326954504895182403

theorem tailTrace_1803877 : CollatzResearch.WordTrace tailWord_1803877 prefixEnd_1803877 102917326954504895182403 := by
  unfold tailWord_1803877
  simp only [CollatzResearch.WordTrace]
  refine ⟨65792799285869181509393885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43861866190579454339595923 65792799285869181509393885)
  ·
    refine ⟨24672299732200943066022707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65792799285869181509393885 24672299732200943066022707)
    ·
      refine ⟨37008449598301414599034061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24672299732200943066022707 37008449598301414599034061)
      ·
        refine ⟨13878168599363030474637773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37008449598301414599034061 13878168599363030474637773)
        ·
          refine ⟨5204313224761136427989165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13878168599363030474637773 5204313224761136427989165)
          ·
            refine ⟨1951617459285426160495937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5204313224761136427989165 1951617459285426160495937)
            ·
              refine ⟨1463713094464069620371953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1951617459285426160495937 1463713094464069620371953)
              ·
                refine ⟨1097784820848052215278965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1463713094464069620371953 1097784820848052215278965)
                ·
                  refine ⟨102917326954504895182403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1097784820848052215278965 102917326954504895182403)
                  ·
                    rfl

theorem cell23_1803877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 5].length) (baseStart_1803877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803877 prefixEnd_1803877 := by exact prefixLift 1803877
  have htrace : WordTrace (prefixWord ++ tailWord_1803877) baseStart_1803877 baseEnd_1803877 := by
    simpa [prefixWord, tailWord_1803877, baseEnd_1803877] using wordTrace_append hprefix tailTrace_1803877
  have hstable : (prefixWord ++ tailWord_1803877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803877).length < 2 ^ (prefixWord ++ tailWord_1803877).sum := by decide
  have hdescent : baseEnd_1803877 < baseStart_1803877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803880 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 2, 5, 2]
def baseStart_1803880 : Nat := 118140960795 + 1803880 * 2 ^ 59
def prefixEnd_1803880 : Nat := 4983230072969 + 3 ^ 40 * 1803880 * 2
def baseEnd_1803880 : Nat := 926257483032507544904113

theorem tailTrace_1803880 : CollatzResearch.WordTrace tailWord_1803880 prefixEnd_1803880 926257483032507544904113 := by
  unfold tailWord_1803880
  simp only [CollatzResearch.WordTrace]
  refine ⟨32896454352429156510876547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43861939136572208681168729 32896454352429156510876547)
  ·
    refine ⟨49344681528643734766314821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32896454352429156510876547 49344681528643734766314821)
    ·
      refine ⟨9252127786620700268684029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49344681528643734766314821 9252127786620700268684029)
      ·
        refine ⟨3469547919982762600756511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9252127786620700268684029 3469547919982762600756511)
        ·
          refine ⟨5204321879974143901134767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3469547919982762600756511 5204321879974143901134767)
          ·
            refine ⟨7806482819961215851702151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5204321879974143901134767 7806482819961215851702151)
            ·
              refine ⟨11709724229941823777553227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7806482819961215851702151 11709724229941823777553227)
              ·
                refine ⟨17564586344912735666329841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11709724229941823777553227 17564586344912735666329841)
                ·
                  refine ⟨13173439758684551749747381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17564586344912735666329841 13173439758684551749747381)
                  ·
                    refine ⟨1235009977376676726538817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13173439758684551749747381 1235009977376676726538817)
                    ·
                      refine ⟨926257483032507544904113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1235009977376676726538817 926257483032507544904113)
                      ·
                        rfl

theorem cell23_1803880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_1803880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803880 prefixEnd_1803880 := by exact prefixLift 1803880
  have htrace : WordTrace (prefixWord ++ tailWord_1803880) baseStart_1803880 baseEnd_1803880 := by
    simpa [prefixWord, tailWord_1803880, baseEnd_1803880] using wordTrace_append hprefix tailTrace_1803880
  have hstable : (prefixWord ++ tailWord_1803880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803880).length < 2 ^ (prefixWord ++ tailWord_1803880).sum := by decide
  have hdescent : baseEnd_1803880 < baseStart_1803880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803916 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 8]
def baseStart_1803916 : Nat := 118140960795 + 1803916 * 2 ^ 59
def prefixEnd_1803916 : Nat := 4983230072969 + 3 ^ 40 * 1803916 * 2
def baseEnd_1803916 : Nat := 102919552037341044894883

theorem tailTrace_1803916 : CollatzResearch.WordTrace tailWord_1803916 prefixEnd_1803916 102919552037341044894883 := by
  unfold tailWord_1803916
  simp only [CollatzResearch.WordTrace]
  refine ⟨32897110866363945585031801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43862814488485260780042401 32897110866363945585031801)
  ·
    refine ⟨24672833149772959188773851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32897110866363945585031801 24672833149772959188773851)
    ·
      refine ⟨37009249724659438783160777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24672833149772959188773851 37009249724659438783160777)
      ·
        refine ⟨27756937293494579087370583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37009249724659438783160777 27756937293494579087370583)
        ·
          refine ⟨41635405940241868631055875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27756937293494579087370583 41635405940241868631055875)
          ·
            refine ⟨62453108910362802946583813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41635405940241868631055875 62453108910362802946583813)
            ·
              refine ⟨11709957920693025552484465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62453108910362802946583813 11709957920693025552484465)
              ·
                refine ⟨8782468440519769164363349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11709957920693025552484465 8782468440519769164363349)
                ·
                  refine ⟨102919552037341044894883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8782468440519769164363349 102919552037341044894883)
                  ·
                    rfl

theorem cell23_1803916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 8].length) (baseStart_1803916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803916 prefixEnd_1803916 := by exact prefixLift 1803916
  have htrace : WordTrace (prefixWord ++ tailWord_1803916) baseStart_1803916 baseEnd_1803916 := by
    simpa [prefixWord, tailWord_1803916, baseEnd_1803916] using wordTrace_append hprefix tailTrace_1803916
  have hstable : (prefixWord ++ tailWord_1803916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803916).length < 2 ^ (prefixWord ++ tailWord_1803916).sum := by decide
  have hdescent : baseEnd_1803916 < baseStart_1803916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803937 : List Nat := [1, 2, 3, 3, 2, 1, 2, 4, 1, 4]
def baseStart_1803937 : Nat := 118140960795 + 1803937 * 2 ^ 59
def prefixEnd_1803937 : Nat := 4983230072969 + 3 ^ 40 * 1803937 * 2
def baseEnd_1803937 : Nat := 308762250476604607297117

theorem tailTrace_1803937 : CollatzResearch.WordTrace tailWord_1803937 prefixEnd_1803937 308762250476604607297117 := by
  unfold tailWord_1803937
  simp only [CollatzResearch.WordTrace]
  refine ⟨65794987665651811756578065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43863325110434541171052043 65794987665651811756578065)
  ·
    refine ⟨49346240749238858817433549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65794987665651811756578065 49346240749238858817433549)
    ·
      refine ⟨18504840280964572056537581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49346240749238858817433549 18504840280964572056537581)
      ·
        refine ⟨6939315105361714521201593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18504840280964572056537581 6939315105361714521201593)
        ·
          refine ⟨5204486329021285890901195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6939315105361714521201593 5204486329021285890901195)
          ·
            refine ⟨7806729493531928836351793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5204486329021285890901195 7806729493531928836351793)
            ·
              refine ⟨5855047120148946627263845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7806729493531928836351793 5855047120148946627263845)
              ·
                refine ⟨1097821335027927492611971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5855047120148946627263845 1097821335027927492611971)
                ·
                  refine ⟨1646732002541891238917957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097821335027927492611971 1646732002541891238917957)
                  ·
                    refine ⟨308762250476604607297117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1646732002541891238917957 308762250476604607297117)
                    ·
                      rfl

theorem cell23_1803937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_1803937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1803937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1803937 prefixEnd_1803937 := by exact prefixLift 1803937
  have htrace : WordTrace (prefixWord ++ tailWord_1803937) baseStart_1803937 baseEnd_1803937 := by
    simpa [prefixWord, tailWord_1803937, baseEnd_1803937] using wordTrace_append hprefix tailTrace_1803937
  have hstable : (prefixWord ++ tailWord_1803937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803937).length < 2 ^ (prefixWord ++ tailWord_1803937).sum := by decide
  have hdescent : baseEnd_1803937 < baseStart_1803937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804017 : List Nat := [1, 2, 2, 2, 2, 5, 1, 2, 1, 1, 4]
def baseStart_1804017 : Nat := 118140960795 + 1804017 * 2 ^ 59
def prefixEnd_1804017 : Nat := 4983230072969 + 3 ^ 40 * 1804017 * 2
def baseEnd_1804017 : Nat := 926327829882173508890983

theorem tailTrace_1804017 : CollatzResearch.WordTrace tailWord_1804017 prefixEnd_1804017 926327829882173508890983 := by
  unfold tailWord_1804017
  simp only [CollatzResearch.WordTrace]
  refine ⟨65797905505361985419490305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43865270336907990279660203 65797905505361985419490305)
  ·
    refine ⟨49348429129021489064617729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65797905505361985419490305 49348429129021489064617729)
    ·
      refine ⟨37011321846766116798463297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49348429129021489064617729 37011321846766116798463297)
      ·
        refine ⟨27758491385074587598847473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37011321846766116798463297 27758491385074587598847473)
        ·
          refine ⟨20818868538805940699135605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27758491385074587598847473 20818868538805940699135605)
          ·
            refine ⟨1951768925513056940543963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20818868538805940699135605 1951768925513056940543963)
            ·
              refine ⟨2927653388269585410815945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1951768925513056940543963 2927653388269585410815945)
              ·
                refine ⟨2195740041202189058111959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2927653388269585410815945 2195740041202189058111959)
                ·
                  refine ⟨3293610061803283587167939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2195740041202189058111959 3293610061803283587167939)
                  ·
                    refine ⟨4940415092704925380751909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3293610061803283587167939 4940415092704925380751909)
                    ·
                      refine ⟨926327829882173508890983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4940415092704925380751909 926327829882173508890983)
                      ·
                        rfl

theorem cell23_1804017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_1804017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804017 prefixEnd_1804017 := by exact prefixLift 1804017
  have htrace : WordTrace (prefixWord ++ tailWord_1804017) baseStart_1804017 baseEnd_1804017 := by
    simpa [prefixWord, tailWord_1804017, baseEnd_1804017] using wordTrace_append hprefix tailTrace_1804017
  have hstable : (prefixWord ++ tailWord_1804017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804017).length < 2 ^ (prefixWord ++ tailWord_1804017).sum := by decide
  have hdescent : baseEnd_1804017 < baseStart_1804017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
