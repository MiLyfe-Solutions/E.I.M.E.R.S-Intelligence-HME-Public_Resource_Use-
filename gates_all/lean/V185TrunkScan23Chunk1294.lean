import V185TrunkScan23Chunk1293

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7664202 : List Nat := [3, 1, 2, 1, 1, 4, 2, 4, 1, 2, 2]
def baseStart_7664202 : Nat := 118140960795 + 7664202 * 2 ^ 59
def prefixEnd_7664202 : Nat := 4983230072969 + 3 ^ 40 * 7664202 * 2
def baseEnd_7664202 : Nat := 3935419459150328008127983

theorem tailTrace_7664202 : CollatzResearch.WordTrace tailWord_7664202 prefixEnd_7664202 3935419459150328008127983 := by
  unfold tailWord_7664202
  simp only [CollatzResearch.WordTrace]
  refine ⟨69884102944978142584138715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186357607853275046891036573 69884102944978142584138715)
  ·
    refine ⟨104826154417467213876208073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69884102944978142584138715 104826154417467213876208073)
    ·
      refine ⟨78619615813100410407156055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104826154417467213876208073 78619615813100410407156055)
      ·
        refine ⟨117929423719650615610734083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78619615813100410407156055 117929423719650615610734083)
        ·
          refine ⟨176894135579475923416101125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117929423719650615610734083 176894135579475923416101125)
          ·
            refine ⟨33167650421151735640518961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176894135579475923416101125 33167650421151735640518961)
            ·
              refine ⟨24875737815863801730389221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33167650421151735640518961 24875737815863801730389221)
              ·
                refine ⟨4664200840474462824447979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24875737815863801730389221 4664200840474462824447979)
                ·
                  refine ⟨6996301260711694236671969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4664200840474462824447979 6996301260711694236671969)
                  ·
                    refine ⟨5247225945533770677503977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6996301260711694236671969 5247225945533770677503977)
                    ·
                      refine ⟨3935419459150328008127983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5247225945533770677503977 3935419459150328008127983)
                      ·
                        rfl

theorem cell23_7664202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 1, 2, 2].length) (baseStart_7664202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664202 prefixEnd_7664202 := by exact prefixLift 7664202
  have htrace : WordTrace (prefixWord ++ tailWord_7664202) baseStart_7664202 baseEnd_7664202 := by
    simpa [prefixWord, tailWord_7664202, baseEnd_7664202] using wordTrace_append hprefix tailTrace_7664202
  have hstable : (prefixWord ++ tailWord_7664202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664202).length < 2 ^ (prefixWord ++ tailWord_7664202).sum := by decide
  have hdescent : baseEnd_7664202 < baseStart_7664202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664275 : List Nat := [1, 1, 1, 2, 1, 2, 2, 7, 2, 2, 2]
def baseStart_7664275 : Nat := 118140960795 + 7664275 * 2 ^ 59
def prefixEnd_7664275 : Nat := 4983230072969 + 3 ^ 40 * 7664275 * 2
def baseEnd_7664275 : Nat := 3935456943238106222515147

theorem tailTrace_7664275 : CollatzResearch.WordTrace tailWord_7664275 prefixEnd_7664275 3935456943238106222515147 := by
  unfold tailWord_7664275
  simp only [CollatzResearch.WordTrace]
  refine ⟨279539074308648103803962279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186359382872432069202641519 279539074308648103803962279)
  ·
    refine ⟨419308611462972155705943419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279539074308648103803962279 419308611462972155705943419)
    ·
      refine ⟨628962917194458233558915129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419308611462972155705943419 628962917194458233558915129)
      ·
        refine ⟨471722187895843675169186347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 628962917194458233558915129 471722187895843675169186347)
        ·
          refine ⟨707583281843765512753779521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471722187895843675169186347 707583281843765512753779521)
          ·
            refine ⟨530687461382824134565334641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 707583281843765512753779521 530687461382824134565334641)
            ·
              refine ⟨398015596037118100924000981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530687461382824134565334641 398015596037118100924000981)
              ·
                refine ⟨9328490532119955490406273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 398015596037118100924000981 9328490532119955490406273)
                ·
                  refine ⟨6996367899089966617804705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9328490532119955490406273 6996367899089966617804705)
                  ·
                    refine ⟨5247275924317474963353529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6996367899089966617804705 5247275924317474963353529)
                    ·
                      refine ⟨3935456943238106222515147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5247275924317474963353529 3935456943238106222515147)
                      ·
                        rfl

theorem cell23_7664275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 2, 2].length) (baseStart_7664275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664275 prefixEnd_7664275 := by exact prefixLift 7664275
  have htrace : WordTrace (prefixWord ++ tailWord_7664275) baseStart_7664275 baseEnd_7664275 := by
    simpa [prefixWord, tailWord_7664275, baseEnd_7664275] using wordTrace_append hprefix tailTrace_7664275
  have hstable : (prefixWord ++ tailWord_7664275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664275).length < 2 ^ (prefixWord ++ tailWord_7664275).sum := by decide
  have hdescent : baseEnd_7664275 < baseStart_7664275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664291 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 3]
def baseStart_7664291 : Nat := 118140960795 + 7664291 * 2 ^ 59
def prefixEnd_7664291 : Nat := 4983230072969 + 3 ^ 40 * 7664291 * 2
def baseEnd_7664291 : Nat := 3935465158928578159915073

theorem tailTrace_7664291 : CollatzResearch.WordTrace tailWord_7664291 prefixEnd_7664291 3935465158928578159915073 := by
  unfold tailWord_7664291
  simp only [CollatzResearch.WordTrace]
  refine ⟨279539657876590138536544727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186359771917726759024363151 279539657876590138536544727)
  ·
    refine ⟨419309486814885207804817091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279539657876590138536544727 419309486814885207804817091)
    ·
      refine ⟨628964230222327811707225637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419309486814885207804817091 628964230222327811707225637)
      ·
        refine ⟨117930793166686464695104807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 628964230222327811707225637 117930793166686464695104807)
        ·
          refine ⟨176896189750029697042657211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117930793166686464695104807 176896189750029697042657211)
          ·
            refine ⟨265344284625044545563985817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176896189750029697042657211 265344284625044545563985817)
            ·
              refine ⟨199008213468783409172989363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265344284625044545563985817 199008213468783409172989363)
              ·
                refine ⟨298512320203175113759484045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199008213468783409172989363 298512320203175113759484045)
                ·
                  refine ⟨111942120076190667659806517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 298512320203175113759484045 111942120076190667659806517)
                  ·
                    refine ⟨10494573757142875093106861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111942120076190667659806517 10494573757142875093106861)
                    ·
                      refine ⟨3935465158928578159915073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10494573757142875093106861 3935465158928578159915073)
                      ·
                        rfl

theorem cell23_7664291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_7664291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664291 prefixEnd_7664291 := by exact prefixLift 7664291
  have htrace : WordTrace (prefixWord ++ tailWord_7664291) baseStart_7664291 baseEnd_7664291 := by
    simpa [prefixWord, tailWord_7664291, baseEnd_7664291] using wordTrace_append hprefix tailTrace_7664291
  have hstable : (prefixWord ++ tailWord_7664291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664291).length < 2 ^ (prefixWord ++ tailWord_7664291).sum := by decide
  have hdescent : baseEnd_7664291 < baseStart_7664291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664309 : List Nat := [1, 3, 3, 3, 1, 2, 2, 2, 2, 2, 2]
def baseStart_7664309 : Nat := 118140960795 + 7664309 * 2 ^ 59
def prefixEnd_7664309 : Nat := 4983230072969 + 3 ^ 40 * 7664309 * 2
def baseEnd_7664309 : Nat := 3935474401580359089489991

theorem tailTrace_7664309 : CollatzResearch.WordTrace tailWord_7664309 prefixEnd_7664309 3935474401580359089489991 := by
  unfold tailWord_7664309
  simp only [CollatzResearch.WordTrace]
  refine ⟨279540314390524927610699981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186360209593683285073799987 279540314390524927610699981)
  ·
    refine ⟨104827617896446847854012493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279540314390524927610699981 104827617896446847854012493)
    ·
      refine ⟨39310356711167567945254685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104827617896446847854012493 39310356711167567945254685)
      ·
        refine ⟨14741383766687837979470507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39310356711167567945254685 14741383766687837979470507)
        ·
          refine ⟨22112075650031756969205761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14741383766687837979470507 22112075650031756969205761)
          ·
            refine ⟨16584056737523817726904321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22112075650031756969205761 16584056737523817726904321)
            ·
              refine ⟨12438042553142863295178241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16584056737523817726904321 12438042553142863295178241)
              ·
                refine ⟨9328531914857147471383681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12438042553142863295178241 9328531914857147471383681)
                ·
                  refine ⟨6996398936142860603537761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9328531914857147471383681 6996398936142860603537761)
                  ·
                    refine ⟨5247299202107145452653321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6996398936142860603537761 5247299202107145452653321)
                    ·
                      refine ⟨3935474401580359089489991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5247299202107145452653321 3935474401580359089489991)
                      ·
                        rfl

theorem cell23_7664309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_7664309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664309 prefixEnd_7664309 := by exact prefixLift 7664309
  have htrace : WordTrace (prefixWord ++ tailWord_7664309) baseStart_7664309 baseEnd_7664309 := by
    simpa [prefixWord, tailWord_7664309, baseEnd_7664309] using wordTrace_append hprefix tailTrace_7664309
  have hstable : (prefixWord ++ tailWord_7664309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664309).length < 2 ^ (prefixWord ++ tailWord_7664309).sum := by decide
  have hdescent : baseEnd_7664309 < baseStart_7664309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664326 : List Nat := [6, 1, 2, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_7664326 : Nat := 118140960795 + 7664326 * 2 ^ 59
def prefixEnd_7664326 : Nat := 4983230072969 + 3 ^ 40 * 7664326 * 2
def baseEnd_7664326 : Nat := 3935483130751485522977413

theorem tailTrace_7664326 : CollatzResearch.WordTrace tailWord_7664326 prefixEnd_7664326 3935483130751485522977413 := by
  unfold tailWord_7664326
  simp only [CollatzResearch.WordTrace]
  refine ⟨8735654200983229359814651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 186360622954308893009379221 8735654200983229359814651)
  ·
    refine ⟨13103481301474844039721977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8735654200983229359814651 13103481301474844039721977)
    ·
      refine ⟨9827610976106133029791483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13103481301474844039721977 9827610976106133029791483)
      ·
        refine ⟨14741416464159199544687225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9827610976106133029791483 14741416464159199544687225)
        ·
          refine ⟨11056062348119399658515419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14741416464159199544687225 11056062348119399658515419)
          ·
            refine ⟨16584093522179099487773129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11056062348119399658515419 16584093522179099487773129)
            ·
              refine ⟨12438070141634324615829847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16584093522179099487773129 12438070141634324615829847)
              ·
                refine ⟨18657105212451486923744771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12438070141634324615829847 18657105212451486923744771)
                ·
                  refine ⟨27985657818677230385617157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18657105212451486923744771 27985657818677230385617157)
                  ·
                    refine ⟨5247310841001980697303217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27985657818677230385617157 5247310841001980697303217)
                    ·
                      refine ⟨3935483130751485522977413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5247310841001980697303217 3935483130751485522977413)
                      ·
                        rfl

theorem cell23_7664326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_7664326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664326 prefixEnd_7664326 := by exact prefixLift 7664326
  have htrace : WordTrace (prefixWord ++ tailWord_7664326) baseStart_7664326 baseEnd_7664326 := by
    simpa [prefixWord, tailWord_7664326, baseEnd_7664326] using wordTrace_append hprefix tailTrace_7664326
  have hstable : (prefixWord ++ tailWord_7664326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664326).length < 2 ^ (prefixWord ++ tailWord_7664326).sum := by decide
  have hdescent : baseEnd_7664326 < baseStart_7664326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664361 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 2, 1, 6]
def baseStart_7664361 : Nat := 118140960795 + 7664361 * 2 ^ 59
def prefixEnd_7664361 : Nat := 4983230072969 + 3 ^ 40 * 7664361 * 2
def baseEnd_7664361 : Nat := 3935501102574392886039751

theorem tailTrace_7664361 : CollatzResearch.WordTrace tailWord_7664361 prefixEnd_7664361 3935501102574392886039751 := by
  unfold tailWord_7664361
  simp only [CollatzResearch.WordTrace]
  refine ⟨279542210986336540491592937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186361473990891026994395291 279542210986336540491592937)
  ·
    refine ⟨209656658239752405368694703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279542210986336540491592937 209656658239752405368694703)
    ·
      refine ⟨314484987359628608053042055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209656658239752405368694703 314484987359628608053042055)
      ·
        refine ⟨471727481039442912079563083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314484987359628608053042055 471727481039442912079563083)
        ·
          refine ⟨707591221559164368119344625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471727481039442912079563083 707591221559164368119344625)
          ·
            refine ⟨530693416169373276089508469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 707591221559164368119344625 530693416169373276089508469)
            ·
              refine ⟨49752507765878744633391419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 530693416169373276089508469 49752507765878744633391419)
              ·
                refine ⟨74628761648818116950087129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49752507765878744633391419 74628761648818116950087129)
                ·
                  refine ⟨55971571236613587712565347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74628761648818116950087129 55971571236613587712565347)
                  ·
                    refine ⟨83957356854920381568848021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55971571236613587712565347 83957356854920381568848021)
                    ·
                      refine ⟨3935501102574392886039751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83957356854920381568848021 3935501102574392886039751)
                      ·
                        rfl

theorem cell23_7664361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_7664361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664361 prefixEnd_7664361 := by exact prefixLift 7664361
  have htrace : WordTrace (prefixWord ++ tailWord_7664361) baseStart_7664361 baseEnd_7664361 := by
    simpa [prefixWord, tailWord_7664361, baseEnd_7664361] using wordTrace_append hprefix tailTrace_7664361
  have hstable : (prefixWord ++ tailWord_7664361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664361).length < 2 ^ (prefixWord ++ tailWord_7664361).sum := by decide
  have hdescent : baseEnd_7664361 < baseStart_7664361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664365 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 4, 4, 2]
def baseStart_7664365 : Nat := 118140960795 + 7664365 * 2 ^ 59
def prefixEnd_7664365 : Nat := 4983230072969 + 3 ^ 40 * 7664365 * 2
def baseEnd_7664365 : Nat := 3935503156497010870389733

theorem tailTrace_7664365 : CollatzResearch.WordTrace tailWord_7664365 prefixEnd_7664365 3935503156497010870389733 := by
  unfold tailWord_7664365
  simp only [CollatzResearch.WordTrace]
  refine ⟨279542356878322049174738549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186361571252214699449825699 279542356878322049174738549)
  ·
    refine ⟨26207095957342692110131739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279542356878322049174738549 26207095957342692110131739)
    ·
      refine ⟨39310643936014038165197609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26207095957342692110131739 39310643936014038165197609)
      ·
        refine ⟨29482982952010528623898207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39310643936014038165197609 29482982952010528623898207)
        ·
          refine ⟨44224474428015792935847311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29482982952010528623898207 44224474428015792935847311)
          ·
            refine ⟨66336711642023689403770967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44224474428015792935847311 66336711642023689403770967)
            ·
              refine ⟨99505067463035534105656451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66336711642023689403770967 99505067463035534105656451)
              ·
                refine ⟨149257601194553301158484677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99505067463035534105656451 149257601194553301158484677)
                ·
                  refine ⟨27985800223978743967215877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149257601194553301158484677 27985800223978743967215877)
                  ·
                    refine ⟨5247337541996014493852977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27985800223978743967215877 5247337541996014493852977)
                    ·
                      refine ⟨3935503156497010870389733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5247337541996014493852977 3935503156497010870389733)
                      ·
                        rfl

theorem cell23_7664365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_7664365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664365 prefixEnd_7664365 := by exact prefixLift 7664365
  have htrace : WordTrace (prefixWord ++ tailWord_7664365) baseStart_7664365 baseEnd_7664365 := by
    simpa [prefixWord, tailWord_7664365, baseEnd_7664365] using wordTrace_append hprefix tailTrace_7664365
  have hstable : (prefixWord ++ tailWord_7664365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664365).length < 2 ^ (prefixWord ++ tailWord_7664365).sum := by decide
  have hdescent : baseEnd_7664365 < baseStart_7664365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664368 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 3]
def baseStart_7664368 : Nat := 118140960795 + 7664368 * 2 ^ 59
def prefixEnd_7664368 : Nat := 4983230072969 + 3 ^ 40 * 7664368 * 2
def baseEnd_7664368 : Nat := 3935504696938974358652219

theorem tailTrace_7664368 : CollatzResearch.WordTrace tailWord_7664368 prefixEnd_7664368 3935504696938974358652219 := by
  unfold tailWord_7664368
  simp only [CollatzResearch.WordTrace]
  refine ⟨139771233148655590343548879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186361644198207453791398505 139771233148655590343548879)
  ·
    refine ⟨209656849722983385515323319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139771233148655590343548879 209656849722983385515323319)
    ·
      refine ⟨314485274584475078272984979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209656849722983385515323319 314485274584475078272984979)
      ·
        refine ⟨471727911876712617409477469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314485274584475078272984979 471727911876712617409477469)
        ·
          refine ⟨176897966953767231528554051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 471727911876712617409477469 176897966953767231528554051)
          ·
            refine ⟨265346950430650847292831077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176897966953767231528554051 265346950430650847292831077)
            ·
              refine ⟨49752553205747033867405827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265346950430650847292831077 49752553205747033867405827)
              ·
                refine ⟨74628829808620550801108741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49752553205747033867405827 74628829808620550801108741)
                ·
                  refine ⟨13992905589116353275207889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74628829808620550801108741 13992905589116353275207889)
                  ·
                    refine ⟨10494679191837264956405917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13992905589116353275207889 10494679191837264956405917)
                    ·
                      refine ⟨3935504696938974358652219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10494679191837264956405917 3935504696938974358652219)
                      ·
                        rfl

theorem cell23_7664368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 3].length) (baseStart_7664368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664368 prefixEnd_7664368 := by exact prefixLift 7664368
  have htrace : WordTrace (prefixWord ++ tailWord_7664368) baseStart_7664368 baseEnd_7664368 := by
    simpa [prefixWord, tailWord_7664368, baseEnd_7664368] using wordTrace_append hprefix tailTrace_7664368
  have hstable : (prefixWord ++ tailWord_7664368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664368).length < 2 ^ (prefixWord ++ tailWord_7664368).sum := by decide
  have hdescent : baseEnd_7664368 < baseStart_7664368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664382 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_7664382 : Nat := 118140960795 + 7664382 * 2 ^ 59
def prefixEnd_7664382 : Nat := 4983230072969 + 3 ^ 40 * 7664382 * 2
def baseEnd_7664382 : Nat := 3935511885668137303877155

theorem tailTrace_7664382 : CollatzResearch.WordTrace tailWord_7664382 prefixEnd_7664382 3935511885668137303877155 := by
  unfold tailWord_7664382
  simp only [CollatzResearch.WordTrace]
  refine ⟨34942872114907557634763425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186361984612840307385404933 34942872114907557634763425)
  ·
    refine ⟨26207154086180668226072569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34942872114907557634763425 26207154086180668226072569)
    ·
      refine ⟨19655365564635501169554427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26207154086180668226072569 19655365564635501169554427)
      ·
        refine ⟨29483048346953251754331641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19655365564635501169554427 29483048346953251754331641)
        ·
          refine ⟨22112286260214938815748731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29483048346953251754331641 22112286260214938815748731)
          ·
            refine ⟨33168429390322408223623097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22112286260214938815748731 33168429390322408223623097)
            ·
              refine ⟨24876322042741806167717323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33168429390322408223623097 24876322042741806167717323)
              ·
                refine ⟨37314483064112709251575985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24876322042741806167717323 37314483064112709251575985)
                ·
                  refine ⟨27985862298084531938681989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37314483064112709251575985 27985862298084531938681989)
                  ·
                    refine ⟨5247349180890849738502873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27985862298084531938681989 5247349180890849738502873)
                    ·
                      refine ⟨3935511885668137303877155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5247349180890849738502873 3935511885668137303877155)
                      ·
                        rfl

theorem cell23_7664382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_7664382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664382 prefixEnd_7664382 := by exact prefixLift 7664382
  have htrace : WordTrace (prefixWord ++ tailWord_7664382) baseStart_7664382 baseEnd_7664382 := by
    simpa [prefixWord, tailWord_7664382, baseEnd_7664382] using wordTrace_append hprefix tailTrace_7664382
  have hstable : (prefixWord ++ tailWord_7664382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664382).length < 2 ^ (prefixWord ++ tailWord_7664382).sum := by decide
  have hdescent : baseEnd_7664382 < baseStart_7664382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664398 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3]
def baseStart_7664398 : Nat := 118140960795 + 7664398 * 2 ^ 59
def prefixEnd_7664398 : Nat := 4983230072969 + 3 ^ 40 * 7664398 * 2
def baseEnd_7664398 : Nat := 3935520101358609241277081

theorem tailTrace_7664398 : CollatzResearch.WordTrace tailWord_7664398 prefixEnd_7664398 3935520101358609241277081 := by
  unfold tailWord_7664398
  simp only [CollatzResearch.WordTrace]
  refine ⟨34942945060900311976336231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186362373658134997207126565 34942945060900311976336231)
  ·
    refine ⟨52414417591350467964504347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34942945060900311976336231 52414417591350467964504347)
    ·
      refine ⟨78621626387025701946756521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52414417591350467964504347 78621626387025701946756521)
      ·
        refine ⟨58966219790269276460067391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78621626387025701946756521 58966219790269276460067391)
        ·
          refine ⟨88449329685403914690101087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58966219790269276460067391 88449329685403914690101087)
          ·
            refine ⟨132673994528105872035151631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88449329685403914690101087 132673994528105872035151631)
            ·
              refine ⟨199010991792158808052727447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132673994528105872035151631 199010991792158808052727447)
              ·
                refine ⟨298516487688238212079091171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199010991792158808052727447 298516487688238212079091171)
                ·
                  refine ⟨447774731532357318118636757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298516487688238212079091171 447774731532357318118636757)
                  ·
                    refine ⟨10494720270289624643405549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 447774731532357318118636757 10494720270289624643405549)
                    ·
                      refine ⟨3935520101358609241277081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10494720270289624643405549 3935520101358609241277081)
                      ·
                        rfl

theorem cell23_7664398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_7664398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664398 prefixEnd_7664398 := by exact prefixLift 7664398
  have htrace : WordTrace (prefixWord ++ tailWord_7664398) baseStart_7664398 baseEnd_7664398 := by
    simpa [prefixWord, tailWord_7664398, baseEnd_7664398] using wordTrace_append hprefix tailTrace_7664398
  have hstable : (prefixWord ++ tailWord_7664398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664398).length < 2 ^ (prefixWord ++ tailWord_7664398).sum := by decide
  have hdescent : baseEnd_7664398 < baseStart_7664398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664411 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 5]
def baseStart_7664411 : Nat := 118140960795 + 7664411 * 2 ^ 59
def prefixEnd_7664411 : Nat := 4983230072969 + 3 ^ 40 * 7664411 * 2
def baseEnd_7664411 : Nat := 3935526776607117690414521

theorem tailTrace_7664411 : CollatzResearch.WordTrace tailWord_7664411 prefixEnd_7664411 3935526776607117690414521 := by
  unfold tailWord_7664411
  simp only [CollatzResearch.WordTrace]
  refine ⟨279544034636155399030913087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186362689757436932687275391 279544034636155399030913087)
  ·
    refine ⟨419316051954233098546369631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279544034636155399030913087 419316051954233098546369631)
    ·
      refine ⟨628974077931349647819554447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419316051954233098546369631 628974077931349647819554447)
      ·
        refine ⟨943461116897024471729331671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628974077931349647819554447 943461116897024471729331671)
        ·
          refine ⟨1415191675345536707593997507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943461116897024471729331671 1415191675345536707593997507)
          ·
            refine ⟨2122787513018305061390996261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1415191675345536707593997507 2122787513018305061390996261)
            ·
              refine ⟨398022658690932199010811799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2122787513018305061390996261 398022658690932199010811799)
              ·
                refine ⟨597033988036398298516217699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398022658690932199010811799 597033988036398298516217699)
                ·
                  refine ⟨895550982054597447774326549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 597033988036398298516217699 895550982054597447774326549)
                  ·
                    refine ⟨41978952283809255364421557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 895550982054597447774326549 41978952283809255364421557)
                    ·
                      refine ⟨3935526776607117690414521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41978952283809255364421557 3935526776607117690414521)
                      ·
                        rfl

theorem cell23_7664411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 5].length) (baseStart_7664411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664411 prefixEnd_7664411 := by exact prefixLift 7664411
  have htrace : WordTrace (prefixWord ++ tailWord_7664411) baseStart_7664411 baseEnd_7664411 := by
    simpa [prefixWord, tailWord_7664411, baseEnd_7664411] using wordTrace_append hprefix tailTrace_7664411
  have hstable : (prefixWord ++ tailWord_7664411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664411).length < 2 ^ (prefixWord ++ tailWord_7664411).sum := by decide
  have hdescent : baseEnd_7664411 < baseStart_7664411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664425 : List Nat := [1, 2, 1, 1, 1, 1, 1, 8, 2, 3, 2]
def baseStart_7664425 : Nat := 118140960795 + 7664425 * 2 ^ 59
def prefixEnd_7664425 : Nat := 4983230072969 + 3 ^ 40 * 7664425 * 2
def baseEnd_7664425 : Nat := 3935533965336280635639457

theorem tailTrace_7664425 : CollatzResearch.WordTrace tailWord_7664425 prefixEnd_7664425 3935533965336280635639457 := by
  unfold tailWord_7664425
  simp only [CollatzResearch.WordTrace]
  refine ⟨279544545258104679421922729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186363030172069786281281819 279544545258104679421922729)
  ·
    refine ⟨209658408943578509566442047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279544545258104679421922729 209658408943578509566442047)
    ·
      refine ⟨314487613415367764349663071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209658408943578509566442047 314487613415367764349663071)
      ·
        refine ⟨471731420123051646524494607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314487613415367764349663071 471731420123051646524494607)
        ·
          refine ⟨707597130184577469786741911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471731420123051646524494607 707597130184577469786741911)
          ·
            refine ⟨1061395695276866204680112867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707597130184577469786741911 1061395695276866204680112867)
            ·
              refine ⟨1592093542915299307020169301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061395695276866204680112867 1592093542915299307020169301)
              ·
                refine ⟨18657346206038663754142609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1592093542915299307020169301 18657346206038663754142609)
                ·
                  refine ⟨13993009654528997815606957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18657346206038663754142609 13993009654528997815606957)
                  ·
                    refine ⟨5247378620448374180852609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13993009654528997815606957 5247378620448374180852609)
                    ·
                      refine ⟨3935533965336280635639457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5247378620448374180852609 3935533965336280635639457)
                      ·
                        rfl

theorem cell23_7664425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 3, 2].length) (baseStart_7664425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664425 prefixEnd_7664425 := by exact prefixLift 7664425
  have htrace : WordTrace (prefixWord ++ tailWord_7664425) baseStart_7664425 baseEnd_7664425 := by
    simpa [prefixWord, tailWord_7664425, baseEnd_7664425] using wordTrace_append hprefix tailTrace_7664425
  have hstable : (prefixWord ++ tailWord_7664425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664425).length < 2 ^ (prefixWord ++ tailWord_7664425).sum := by decide
  have hdescent : baseEnd_7664425 < baseStart_7664425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664426 : List Nat := [3, 1, 4, 3, 2, 1, 1, 1, 3, 4]
def baseStart_7664426 : Nat := 118140960795 + 7664426 * 2 ^ 59
def prefixEnd_7664426 : Nat := 4983230072969 + 3 ^ 40 * 7664426 * 2
def baseEnd_7664426 : Nat := 1311844826272311710575651

theorem tailTrace_7664426 : CollatzResearch.WordTrace tailWord_7664426 prefixEnd_7664426 1311844826272311710575651 := by
  unfold tailWord_7664426
  simp only [CollatzResearch.WordTrace]
  refine ⟨69886145432775264148177283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186363054487400704395139421 69886145432775264148177283)
  ·
    refine ⟨104829218149162896222265925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69886145432775264148177283 104829218149162896222265925)
    ·
      refine ⟨19655478402968043041674861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104829218149162896222265925 19655478402968043041674861)
      ·
        refine ⟨7370804401113016140628073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19655478402968043041674861 7370804401113016140628073)
        ·
          refine ⟨5528103300834762105471055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7370804401113016140628073 5528103300834762105471055)
          ·
            refine ⟨8292154951252143158206583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5528103300834762105471055 8292154951252143158206583)
            ·
              refine ⟨12438232426878214737309875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8292154951252143158206583 12438232426878214737309875)
              ·
                refine ⟨18657348640317322105964813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12438232426878214737309875 18657348640317322105964813)
                ·
                  refine ⟨6996505740118995789736805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18657348640317322105964813 6996505740118995789736805)
                  ·
                    refine ⟨1311844826272311710575651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6996505740118995789736805 1311844826272311710575651)
                    ·
                      rfl

theorem cell23_7664426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_7664426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664426 prefixEnd_7664426 := by exact prefixLift 7664426
  have htrace : WordTrace (prefixWord ++ tailWord_7664426) baseStart_7664426 baseEnd_7664426 := by
    simpa [prefixWord, tailWord_7664426, baseEnd_7664426] using wordTrace_append hprefix tailTrace_7664426
  have hstable : (prefixWord ++ tailWord_7664426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664426).length < 2 ^ (prefixWord ++ tailWord_7664426).sum := by decide
  have hdescent : baseEnd_7664426 < baseStart_7664426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664431 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 2, 10]
def baseStart_7664431 : Nat := 118140960795 + 7664431 * 2 ^ 59
def prefixEnd_7664431 : Nat := 4983230072969 + 3 ^ 40 * 7664431 * 2
def baseEnd_7664431 : Nat := 1311845682073402537388143

theorem tailTrace_7664431 : CollatzResearch.WordTrace tailWord_7664431 prefixEnd_7664431 1311845682073402537388143 := by
  unfold tailWord_7664431
  simp only [CollatzResearch.WordTrace]
  refine ⟨279544764096082942446641147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186363176064055294964427431 279544764096082942446641147)
  ·
    refine ⟨419317146144124413669961721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279544764096082942446641147 419317146144124413669961721)
    ·
      refine ⟨314487859608093310252471291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419317146144124413669961721 314487859608093310252471291)
      ·
        refine ⟨471731789412139965378706937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314487859608093310252471291 471731789412139965378706937)
        ·
          refine ⟨353798842059104974034030203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471731789412139965378706937 353798842059104974034030203)
          ·
            refine ⟨530698263088657461051045305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353798842059104974034030203 530698263088657461051045305)
            ·
              refine ⟨398023697316493095788283979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530698263088657461051045305 398023697316493095788283979)
              ·
                refine ⟨597035545974739643682425969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398023697316493095788283979 597035545974739643682425969)
                ·
                  refine ⟨447776659481054732761819477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597035545974739643682425969 447776659481054732761819477)
                  ·
                    refine ⟨1311845682073402537388143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 447776659481054732761819477 1311845682073402537388143)
                    ·
                      rfl

theorem cell23_7664431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 10].length) (baseStart_7664431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664431 prefixEnd_7664431 := by exact prefixLift 7664431
  have htrace : WordTrace (prefixWord ++ tailWord_7664431) baseStart_7664431 baseEnd_7664431 := by
    simpa [prefixWord, tailWord_7664431, baseEnd_7664431] using wordTrace_append hprefix tailTrace_7664431
  have hstable : (prefixWord ++ tailWord_7664431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664431).length < 2 ^ (prefixWord ++ tailWord_7664431).sum := by decide
  have hdescent : baseEnd_7664431 < baseStart_7664431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664432 : List Nat := [2, 1, 1, 1, 2, 2, 1, 8, 1, 1, 3]
def baseStart_7664432 : Nat := 118140960795 + 7664432 * 2 ^ 59
def prefixEnd_7664432 : Nat := 4983230072969 + 3 ^ 40 * 7664432 * 2
def baseEnd_7664432 : Nat := 3935537559700862108251925

theorem tailTrace_7664432 : CollatzResearch.WordTrace tailWord_7664432 prefixEnd_7664432 3935537559700862108251925 := by
  unfold tailWord_7664432
  simp only [CollatzResearch.WordTrace]
  refine ⟨139772400284539659808713775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186363200379386213078285033 139772400284539659808713775)
  ·
    refine ⟨209658600426809489713070663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139772400284539659808713775 209658600426809489713070663)
    ·
      refine ⟨314487900640214234569605995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209658600426809489713070663 314487900640214234569605995)
      ·
        refine ⟨471731850960321351854408993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314487900640214234569605995 471731850960321351854408993)
        ·
          refine ⟨353798888220241013890806745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471731850960321351854408993 353798888220241013890806745)
          ·
            refine ⟨265349166165180760418105059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353798888220241013890806745 265349166165180760418105059)
            ·
              refine ⟨398023749247771140627157589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265349166165180760418105059 398023749247771140627157589)
              ·
                refine ⟨4664340811497318054224503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 398023749247771140627157589 4664340811497318054224503)
                ·
                  refine ⟨6996511217245977081336755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4664340811497318054224503 6996511217245977081336755)
                  ·
                    refine ⟨10494766825868965622005133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6996511217245977081336755 10494766825868965622005133)
                    ·
                      refine ⟨3935537559700862108251925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10494766825868965622005133 3935537559700862108251925)
                      ·
                        rfl

theorem cell23_7664432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 1, 1, 3].length) (baseStart_7664432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664432 prefixEnd_7664432 := by exact prefixLift 7664432
  have htrace : WordTrace (prefixWord ++ tailWord_7664432) baseStart_7664432 baseEnd_7664432 := by
    simpa [prefixWord, tailWord_7664432, baseEnd_7664432] using wordTrace_append hprefix tailTrace_7664432
  have hstable : (prefixWord ++ tailWord_7664432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664432).length < 2 ^ (prefixWord ++ tailWord_7664432).sum := by decide
  have hdescent : baseEnd_7664432 < baseStart_7664432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664465 : List Nat := [1, 2, 2, 1, 6, 1, 1, 2, 1, 6]
def baseStart_7664465 : Nat := 118140960795 + 7664465 * 2 ^ 59
def prefixEnd_7664465 : Nat := 4983230072969 + 3 ^ 40 * 7664465 * 2
def baseEnd_7664465 : Nat := 1311851501520820159713091

theorem tailTrace_7664465 : CollatzResearch.WordTrace tailWord_7664465 prefixEnd_7664465 1311851501520820159713091 := by
  unfold tailWord_7664465
  simp only [CollatzResearch.WordTrace]
  refine ⟨279546004177959766253378849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186364002785306510835585899 279546004177959766253378849)
  ·
    refine ⟨209659503133469824690034137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279546004177959766253378849 209659503133469824690034137)
    ·
      refine ⟨157244627350102368517525603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209659503133469824690034137 157244627350102368517525603)
      ·
        refine ⟨235866941025153552776288405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157244627350102368517525603 235866941025153552776288405)
        ·
          refine ⟨11056262860554072786388519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 235866941025153552776288405 11056262860554072786388519)
          ·
            refine ⟨16584394290831109179582779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11056262860554072786388519 16584394290831109179582779)
            ·
              refine ⟨24876591436246663769374169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16584394290831109179582779 24876591436246663769374169)
              ·
                refine ⟨18657443577184997827030627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24876591436246663769374169 18657443577184997827030627)
                ·
                  refine ⟨27986165365777496740545941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18657443577184997827030627 27986165365777496740545941)
                  ·
                    refine ⟨1311851501520820159713091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27986165365777496740545941 1311851501520820159713091)
                    ·
                      rfl

theorem cell23_7664465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_7664465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664465 prefixEnd_7664465 := by exact prefixLift 7664465
  have htrace : WordTrace (prefixWord ++ tailWord_7664465) baseStart_7664465 baseEnd_7664465 := by
    simpa [prefixWord, tailWord_7664465, baseEnd_7664465] using wordTrace_append hprefix tailTrace_7664465
  have hstable : (prefixWord ++ tailWord_7664465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664465).length < 2 ^ (prefixWord ++ tailWord_7664465).sum := by decide
  have hdescent : baseEnd_7664465 < baseStart_7664465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664498 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_7664498 : Nat := 118140960795 + 7664498 * 2 ^ 59
def prefixEnd_7664498 : Nat := 4983230072969 + 3 ^ 40 * 7664498 * 2
def baseEnd_7664498 : Nat := 3935571449424058850026621

theorem tailTrace_7664498 : CollatzResearch.WordTrace tailWord_7664498 prefixEnd_7664498 3935571449424058850026621 := by
  unfold tailWord_7664498
  simp only [CollatzResearch.WordTrace]
  refine ⟨69886801946710053222332537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186364805191226808592886765 69886801946710053222332537)
  ·
    refine ⟨52415101460032539916749403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69886801946710053222332537 52415101460032539916749403)
    ·
      refine ⟨78622652190048809875124105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52415101460032539916749403 78622652190048809875124105)
      ·
        refine ⟨58966989142536607406343079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78622652190048809875124105 58966989142536607406343079)
        ·
          refine ⟨88450483713804911109514619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58966989142536607406343079 88450483713804911109514619)
          ·
            refine ⟨132675725570707366664271929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88450483713804911109514619 132675725570707366664271929)
            ·
              refine ⟨99506794178030524998203947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132675725570707366664271929 99506794178030524998203947)
              ·
                refine ⟨149260191267045787497305921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99506794178030524998203947 149260191267045787497305921)
                ·
                  refine ⟨111945143450284340622979441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149260191267045787497305921 111945143450284340622979441)
                  ·
                    refine ⟨83958857587713255467234581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111945143450284340622979441 83958857587713255467234581)
                    ·
                      refine ⟨3935571449424058850026621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83958857587713255467234581 3935571449424058850026621)
                      ·
                        rfl

theorem cell23_7664498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_7664498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664498 prefixEnd_7664498 := by exact prefixLift 7664498
  have htrace : WordTrace (prefixWord ++ tailWord_7664498) baseStart_7664498 baseEnd_7664498 := by
    simpa [prefixWord, tailWord_7664498, baseEnd_7664498] using wordTrace_append hprefix tailTrace_7664498
  have hstable : (prefixWord ++ tailWord_7664498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664498).length < 2 ^ (prefixWord ++ tailWord_7664498).sum := by decide
  have hdescent : baseEnd_7664498 < baseStart_7664498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664502 : List Nat := [5, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_7664502 : Nat := 118140960795 + 7664502 * 2 ^ 59
def prefixEnd_7664502 : Nat := 4983230072969 + 3 ^ 40 * 7664502 * 2
def baseEnd_7664502 : Nat := 3935573503346676834376603

theorem tailTrace_7664502 : CollatzResearch.WordTrace tailWord_7664502 prefixEnd_7664502 3935573503346676834376603 := by
  unfold tailWord_7664502
  simp only [CollatzResearch.WordTrace]
  refine ⟨17471709604926607598279735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186364902452550481048317173 17471709604926607598279735)
  ·
    refine ⟨26207564407389911397419603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17471709604926607598279735 26207564407389911397419603)
    ·
      refine ⟨39311346611084867096129405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26207564407389911397419603 39311346611084867096129405)
      ·
        refine ⟨14741754979156825161048527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39311346611084867096129405 14741754979156825161048527)
        ·
          refine ⟨22112632468735237741572791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14741754979156825161048527 22112632468735237741572791)
          ·
            refine ⟨33168948703102856612359187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22112632468735237741572791 33168948703102856612359187)
            ·
              refine ⟨49753423054654284918538781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33168948703102856612359187 49753423054654284918538781)
              ·
                refine ⟨18657533645495356844452043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49753423054654284918538781 18657533645495356844452043)
                ·
                  refine ⟨27986300468243035266678065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18657533645495356844452043 27986300468243035266678065)
                  ·
                    refine ⟨20989725351182276450008549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27986300468243035266678065 20989725351182276450008549)
                    ·
                      refine ⟨3935573503346676834376603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20989725351182276450008549 3935573503346676834376603)
                      ·
                        rfl

theorem cell23_7664502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_7664502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664502 prefixEnd_7664502 := by exact prefixLift 7664502
  have htrace : WordTrace (prefixWord ++ tailWord_7664502) baseStart_7664502 baseEnd_7664502 := by
    simpa [prefixWord, tailWord_7664502, baseEnd_7664502] using wordTrace_append hprefix tailTrace_7664502
  have hstable : (prefixWord ++ tailWord_7664502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664502).length < 2 ^ (prefixWord ++ tailWord_7664502).sum := by decide
  have hdescent : baseEnd_7664502 < baseStart_7664502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664505 : List Nat := [1, 2, 1, 3, 2, 3, 1, 3, 1, 3, 3]
def baseStart_7664505 : Nat := 118140960795 + 7664505 * 2 ^ 59
def prefixEnd_7664505 : Nat := 4983230072969 + 3 ^ 40 * 7664505 * 2
def baseEnd_7664505 : Nat := 3935575043788640322639089

theorem tailTrace_7664505 : CollatzResearch.WordTrace tailWord_7664505 prefixEnd_7664505 3935575043788640322639089 := by
  unfold tailWord_7664505
  simp only [CollatzResearch.WordTrace]
  refine ⟨279547463097814853084834969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186364975398543235389889979 279547463097814853084834969)
  ·
    refine ⟨209660597323361139813626227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279547463097814853084834969 209660597323361139813626227)
    ·
      refine ⟨314490895985041709720439341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209660597323361139813626227 314490895985041709720439341)
      ·
        refine ⟨117934085994390641145164753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314490895985041709720439341 117934085994390641145164753)
        ·
          refine ⟨88450564495792980858873565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117934085994390641145164753 88450564495792980858873565)
          ·
            refine ⟨33168961685922367822077587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88450564495792980858873565 33168961685922367822077587)
            ·
              refine ⟨49753442528883551733116381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33168961685922367822077587 49753442528883551733116381)
              ·
                refine ⟨18657540948331331899918643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49753442528883551733116381 18657540948331331899918643)
                ·
                  refine ⟨27986311422496997849877965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18657540948331331899918643 27986311422496997849877965)
                  ·
                    refine ⟨10494866783436374193704237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27986311422496997849877965 10494866783436374193704237)
                    ·
                      refine ⟨3935575043788640322639089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10494866783436374193704237 3935575043788640322639089)
                      ·
                        rfl

theorem cell23_7664505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_7664505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664505 prefixEnd_7664505 := by exact prefixLift 7664505
  have htrace : WordTrace (prefixWord ++ tailWord_7664505) baseStart_7664505 baseEnd_7664505 := by
    simpa [prefixWord, tailWord_7664505, baseEnd_7664505] using wordTrace_append hprefix tailTrace_7664505
  have hstable : (prefixWord ++ tailWord_7664505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664505).length < 2 ^ (prefixWord ++ tailWord_7664505).sum := by decide
  have hdescent : baseEnd_7664505 < baseStart_7664505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664522 : List Nat := [3, 1, 2, 4, 1, 1, 2, 2, 1, 3, 3]
def baseStart_7664522 : Nat := 118140960795 + 7664522 * 2 ^ 59
def prefixEnd_7664522 : Nat := 4983230072969 + 3 ^ 40 * 7664522 * 2
def baseEnd_7664522 : Nat := 3935583772959766756126511

theorem tailTrace_7664522 : CollatzResearch.WordTrace tailWord_7664522 prefixEnd_7664522 3935583772959766756126511 := by
  unfold tailWord_7664522
  simp only [CollatzResearch.WordTrace]
  refine ⟨69887020784688316247050955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186365388759168843325469213 69887020784688316247050955)
  ·
    refine ⟨104830531177032474370576433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69887020784688316247050955 104830531177032474370576433)
    ·
      refine ⟨78622898382774355777932325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104830531177032474370576433 78622898382774355777932325)
      ·
        refine ⟨14741793446770191708362311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78622898382774355777932325 14741793446770191708362311)
        ·
          refine ⟨22112690170155287562543467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14741793446770191708362311 22112690170155287562543467)
          ·
            refine ⟨33169035255232931343815201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22112690170155287562543467 33169035255232931343815201)
            ·
              refine ⟨24876776441424698507861401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33169035255232931343815201 24876776441424698507861401)
              ·
                refine ⟨18657582331068523880896051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24876776441424698507861401 18657582331068523880896051)
                ·
                  refine ⟨27986373496602785821344077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18657582331068523880896051 27986373496602785821344077)
                  ·
                    refine ⟨10494890061226044683004029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27986373496602785821344077 10494890061226044683004029)
                    ·
                      refine ⟨3935583772959766756126511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10494890061226044683004029 3935583772959766756126511)
                      ·
                        rfl

theorem cell23_7664522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_7664522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664522 prefixEnd_7664522 := by exact prefixLift 7664522
  have htrace : WordTrace (prefixWord ++ tailWord_7664522) baseStart_7664522 baseEnd_7664522 := by
    simpa [prefixWord, tailWord_7664522, baseEnd_7664522] using wordTrace_append hprefix tailTrace_7664522
  have hstable : (prefixWord ++ tailWord_7664522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664522).length < 2 ^ (prefixWord ++ tailWord_7664522).sum := by decide
  have hdescent : baseEnd_7664522 < baseStart_7664522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664565 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_7664565 : Nat := 118140960795 + 7664565 * 2 ^ 59
def prefixEnd_7664565 : Nat := 4983230072969 + 3 ^ 40 * 7664565 * 2
def baseEnd_7664565 : Nat := 3935605852627910087888813

theorem tailTrace_7664565 : CollatzResearch.WordTrace tailWord_7664565 prefixEnd_7664565 3935605852627910087888813 := by
  unfold tailWord_7664565
  simp only [CollatzResearch.WordTrace]
  refine ⟨279549651477597483332019149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186366434318398322221346099 279549651477597483332019149)
  ·
    refine ⟨104831119304099056249507181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279549651477597483332019149 104831119304099056249507181)
    ·
      refine ⟨39311669739037146093565193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104831119304099056249507181 39311669739037146093565193)
      ·
        refine ⟨29483752304277859570173895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39311669739037146093565193 29483752304277859570173895)
        ·
          refine ⟨44225628456416789355260843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29483752304277859570173895 44225628456416789355260843)
          ·
            refine ⟨66338442684625184032891265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44225628456416789355260843 66338442684625184032891265)
            ·
              refine ⟨49753832013468888024668449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66338442684625184032891265 49753832013468888024668449)
              ·
                refine ⟨37315374010101666018501337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49753832013468888024668449 37315374010101666018501337)
                ·
                  refine ⟨27986530507576249513876003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37315374010101666018501337 27986530507576249513876003)
                  ·
                    refine ⟨41979795761364374270814005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27986530507576249513876003 41979795761364374270814005)
                    ·
                      refine ⟨3935605852627910087888813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41979795761364374270814005 3935605852627910087888813)
                      ·
                        rfl

theorem cell23_7664565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_7664565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664565 prefixEnd_7664565 := by exact prefixLift 7664565
  have htrace : WordTrace (prefixWord ++ tailWord_7664565) baseStart_7664565 baseEnd_7664565 := by
    simpa [prefixWord, tailWord_7664565, baseEnd_7664565] using wordTrace_append hprefix tailTrace_7664565
  have hstable : (prefixWord ++ tailWord_7664565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664565).length < 2 ^ (prefixWord ++ tailWord_7664565).sum := by decide
  have hdescent : baseEnd_7664565 < baseStart_7664565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664602 : List Nat := [3, 1, 1, 2, 4, 3, 1, 1, 7]
def baseStart_7664602 : Nat := 118140960795 + 7664602 * 2 ^ 59
def prefixEnd_7664602 : Nat := 4983230072969 + 3 ^ 40 * 7664602 * 2
def baseEnd_7664602 : Nat := 437291650156902938125127

theorem tailTrace_7664602 : CollatzResearch.WordTrace tailWord_7664602 prefixEnd_7664602 437291650156902938125127 := by
  unfold tailWord_7664602
  simp only [CollatzResearch.WordTrace]
  refine ⟨69887750244615859662779015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186367333985642292434077373 69887750244615859662779015)
  ·
    refine ⟨104831625366923789494168523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69887750244615859662779015 104831625366923789494168523)
    ·
      refine ⟨157247438050385684241252785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104831625366923789494168523 157247438050385684241252785)
      ·
        refine ⟨117935578537789263180939589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157247438050385684241252785 117935578537789263180939589)
        ·
          refine ⟨22112920975835486846426173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117935578537789263180939589 22112920975835486846426173)
          ·
            refine ⟨8292345365938307567409815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22112920975835486846426173 8292345365938307567409815)
            ·
              refine ⟨12438518048907461351114723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8292345365938307567409815 12438518048907461351114723)
              ·
                refine ⟨18657777073361192026672085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12438518048907461351114723 18657777073361192026672085)
                ·
                  refine ⟨437291650156902938125127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18657777073361192026672085 437291650156902938125127)
                  ·
                    rfl

theorem cell23_7664602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 7].length) (baseStart_7664602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664602 prefixEnd_7664602 := by exact prefixLift 7664602
  have htrace : WordTrace (prefixWord ++ tailWord_7664602) baseStart_7664602 baseEnd_7664602 := by
    simpa [prefixWord, tailWord_7664602, baseEnd_7664602] using wordTrace_append hprefix tailTrace_7664602
  have hstable : (prefixWord ++ tailWord_7664602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664602).length < 2 ^ (prefixWord ++ tailWord_7664602).sum := by decide
  have hdescent : baseEnd_7664602 < baseStart_7664602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664613 : List Nat := [1, 3, 1, 6, 1, 1, 1, 3, 2, 2, 2]
def baseStart_7664613 : Nat := 118140960795 + 7664613 * 2 ^ 59
def prefixEnd_7664613 : Nat := 4983230072969 + 3 ^ 40 * 7664613 * 2
def baseEnd_7664613 : Nat := 3935630499699325900088593

theorem tailTrace_7664613 : CollatzResearch.WordTrace tailWord_7664613 prefixEnd_7664613 3935630499699325900088593 := by
  unfold tailWord_7664613
  simp only [CollatzResearch.WordTrace]
  refine ⟨279551402181423587529766493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186367601454282391686510995 279551402181423587529766493)
  ·
    refine ⟨104831775818033845323662435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279551402181423587529766493 104831775818033845323662435)
    ·
      refine ⟨157247663727050767985493653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104831775818033845323662435 157247663727050767985493653)
      ·
        refine ⟨7370984237205504749320015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 157247663727050767985493653 7370984237205504749320015)
        ·
          refine ⟨11056476355808257123980023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7370984237205504749320015 11056476355808257123980023)
          ·
            refine ⟨16584714533712385685970035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11056476355808257123980023 16584714533712385685970035)
            ·
              refine ⟨24877071800568578528955053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16584714533712385685970035 24877071800568578528955053)
              ·
                refine ⟨9328901925213216948358145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24877071800568578528955053 9328901925213216948358145)
                ·
                  refine ⟨6996676443909912711268609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9328901925213216948358145 6996676443909912711268609)
                  ·
                    refine ⟨5247507332932434533451457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6996676443909912711268609 5247507332932434533451457)
                    ·
                      refine ⟨3935630499699325900088593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5247507332932434533451457 3935630499699325900088593)
                      ·
                        rfl

theorem cell23_7664613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_7664613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664613 prefixEnd_7664613 := by exact prefixLift 7664613
  have htrace : WordTrace (prefixWord ++ tailWord_7664613) baseStart_7664613 baseEnd_7664613 := by
    simpa [prefixWord, tailWord_7664613, baseEnd_7664613] using wordTrace_append hprefix tailTrace_7664613
  have hstable : (prefixWord ++ tailWord_7664613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664613).length < 2 ^ (prefixWord ++ tailWord_7664613).sum := by decide
  have hdescent : baseEnd_7664613 < baseStart_7664613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664652 : List Nat := [2, 2, 1, 2, 3, 2, 2, 2, 2, 1, 4]
def baseStart_7664652 : Nat := 118140960795 + 7664652 * 2 ^ 59
def prefixEnd_7664652 : Nat := 4983230072969 + 3 ^ 40 * 7664652 * 2
def baseEnd_7664652 : Nat := 3935650525444851247500913

theorem tailTrace_7664652 : CollatzResearch.WordTrace tailWord_7664652 prefixEnd_7664652 3935650525444851247500913 := by
  unfold tailWord_7664652
  simp only [CollatzResearch.WordTrace]
  refine ⟨139776412314141148595218105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186368549752188198126957473 139776412314141148595218105)
  ·
    refine ⟨104832309235605861446413579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139776412314141148595218105 104832309235605861446413579)
    ·
      refine ⟨157248463853408792169620369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104832309235605861446413579 157248463853408792169620369)
      ·
        refine ⟨117936347890056594127215277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157248463853408792169620369 117936347890056594127215277)
        ·
          refine ⟨44226130458771222797705729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117936347890056594127215277 44226130458771222797705729)
          ·
            refine ⟨33169597844078417098279297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44226130458771222797705729 33169597844078417098279297)
            ·
              refine ⟨24877198383058812823709473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33169597844078417098279297 24877198383058812823709473)
              ·
                refine ⟨18657898787294109617782105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24877198383058812823709473 18657898787294109617782105)
                ·
                  refine ⟨13993424090470582213336579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18657898787294109617782105 13993424090470582213336579)
                  ·
                    refine ⟨20990136135705873320004869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13993424090470582213336579 20990136135705873320004869)
                    ·
                      refine ⟨3935650525444851247500913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20990136135705873320004869 3935650525444851247500913)
                      ·
                        rfl

theorem cell23_7664652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_7664652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664652 prefixEnd_7664652 := by exact prefixLift 7664652
  have htrace : WordTrace (prefixWord ++ tailWord_7664652) baseStart_7664652 baseEnd_7664652 := by
    simpa [prefixWord, tailWord_7664652, baseEnd_7664652] using wordTrace_append hprefix tailTrace_7664652
  have hstable : (prefixWord ++ tailWord_7664652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664652).length < 2 ^ (prefixWord ++ tailWord_7664652).sum := by decide
  have hdescent : baseEnd_7664652 < baseStart_7664652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664679 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 5, 4]
def baseStart_7664679 : Nat := 118140960795 + 7664679 * 2 ^ 59
def prefixEnd_7664679 : Nat := 4983230072969 + 3 ^ 40 * 7664679 * 2
def baseEnd_7664679 : Nat := 1311888129807507547287763

theorem tailTrace_7664679 : CollatzResearch.WordTrace tailWord_7664679 prefixEnd_7664679 1311888129807507547287763 := by
  unfold tailWord_7664679
  simp only [CollatzResearch.WordTrace]
  refine ⟨279553809399184480801669091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186369206266122987201112727 279553809399184480801669091)
  ·
    refine ⟨419330714098776721202503637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279553809399184480801669091 419330714098776721202503637)
    ·
      refine ⟨9828063611690079403183679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 419330714098776721202503637 9828063611690079403183679)
      ·
        refine ⟨14742095417535119104775519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9828063611690079403183679 14742095417535119104775519)
        ·
          refine ⟨22113143126302678657163279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14742095417535119104775519 22113143126302678657163279)
          ·
            refine ⟨33169714689454017985744919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22113143126302678657163279 33169714689454017985744919)
            ·
              refine ⟨49754572034181026978617379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33169714689454017985744919 49754572034181026978617379)
              ·
                refine ⟨74631858051271540467926069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49754572034181026978617379 74631858051271540467926069)
                ·
                  refine ⟨6996736692306706918868069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74631858051271540467926069 6996736692306706918868069)
                  ·
                    refine ⟨1311888129807507547287763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6996736692306706918868069 1311888129807507547287763)
                    ·
                      rfl

theorem cell23_7664679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_7664679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664679 prefixEnd_7664679 := by exact prefixLift 7664679
  have htrace : WordTrace (prefixWord ++ tailWord_7664679) baseStart_7664679 baseEnd_7664679 := by
    simpa [prefixWord, tailWord_7664679, baseEnd_7664679] using wordTrace_append hprefix tailTrace_7664679
  have hstable : (prefixWord ++ tailWord_7664679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664679).length < 2 ^ (prefixWord ++ tailWord_7664679).sum := by decide
  have hdescent : baseEnd_7664679 < baseStart_7664679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664696 : List Nat := [2, 1, 2, 1, 5, 2, 2, 3, 1, 4]
def baseStart_7664696 : Nat := 118140960795 + 7664696 * 2 ^ 59
def prefixEnd_7664696 : Nat := 4983230072969 + 3 ^ 40 * 7664696 * 2
def baseEnd_7664696 : Nat := 1311891039531216358450237

theorem tailTrace_7664696 : CollatzResearch.WordTrace tailWord_7664696 prefixEnd_7664696 1311891039531216358450237 := by
  unfold tailWord_7664696
  simp only [CollatzResearch.WordTrace]
  refine ⟨139777214720061446352518971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186369619626748595136691961 139777214720061446352518971)
  ·
    refine ⟨209665822080092169528778457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139777214720061446352518971 209665822080092169528778457)
    ·
      refine ⟨157249366560069127146583843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209665822080092169528778457 157249366560069127146583843)
      ·
        refine ⟨235874049840103690719875765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157249366560069127146583843 235874049840103690719875765)
        ·
          refine ⟨22113192172509721004988353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 235874049840103690719875765 22113192172509721004988353)
          ·
            refine ⟨16584894129382290753741265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22113192172509721004988353 16584894129382290753741265)
            ·
              refine ⟨12438670597036718065305949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16584894129382290753741265 12438670597036718065305949)
              ·
                refine ⟨4664501473888769274489731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12438670597036718065305949 4664501473888769274489731)
                ·
                  refine ⟨6996752210833153911734597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4664501473888769274489731 6996752210833153911734597)
                  ·
                    refine ⟨1311891039531216358450237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6996752210833153911734597 1311891039531216358450237)
                    ·
                      rfl

theorem cell23_7664696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 1, 4].length) (baseStart_7664696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664696 prefixEnd_7664696 := by exact prefixLift 7664696
  have htrace : WordTrace (prefixWord ++ tailWord_7664696) baseStart_7664696 baseEnd_7664696 := by
    simpa [prefixWord, tailWord_7664696, baseEnd_7664696] using wordTrace_append hprefix tailTrace_7664696
  have hstable : (prefixWord ++ tailWord_7664696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664696).length < 2 ^ (prefixWord ++ tailWord_7664696).sum := by decide
  have hdescent : baseEnd_7664696 < baseStart_7664696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664752 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 6, 4]
def baseStart_7664752 : Nat := 118140960795 + 7664752 * 2 ^ 59
def prefixEnd_7664752 : Nat := 4983230072969 + 3 ^ 40 * 7664752 * 2
def baseEnd_7664752 : Nat := 1311900624503433618750151

theorem tailTrace_7664752 : CollatzResearch.WordTrace tailWord_7664752 prefixEnd_7664752 1311900624503433618750151 := by
  unfold tailWord_7664752
  simp only [CollatzResearch.WordTrace]
  refine ⟨139778235963960007134538255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186370981285280009512717673 139778235963960007134538255)
  ·
    refine ⟨209667353945940010701807383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139778235963960007134538255 209667353945940010701807383)
    ·
      refine ⟨314501030918910016052711075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209667353945940010701807383 314501030918910016052711075)
      ·
        refine ⟨471751546378365024079066613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314501030918910016052711075 471751546378365024079066613)
        ·
          refine ⟨44226707472971721007412495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 471751546378365024079066613 44226707472971721007412495)
          ·
            refine ⟨66340061209457581511118743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44226707472971721007412495 66340061209457581511118743)
            ·
              refine ⟨99510091814186372266678115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66340061209457581511118743 99510091814186372266678115)
              ·
                refine ⟨149265137721279558400017173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99510091814186372266678115 149265137721279558400017173)
                ·
                  refine ⟨6996803330684979300000805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 149265137721279558400017173 6996803330684979300000805)
                  ·
                    refine ⟨1311900624503433618750151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6996803330684979300000805 1311900624503433618750151)
                    ·
                      rfl

theorem cell23_7664752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 6, 4].length) (baseStart_7664752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664752 prefixEnd_7664752 := by exact prefixLift 7664752
  have htrace : WordTrace (prefixWord ++ tailWord_7664752) baseStart_7664752 baseEnd_7664752 := by
    simpa [prefixWord, tailWord_7664752, baseEnd_7664752] using wordTrace_append hprefix tailTrace_7664752
  have hstable : (prefixWord ++ tailWord_7664752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664752).length < 2 ^ (prefixWord ++ tailWord_7664752).sum := by decide
  have hdescent : baseEnd_7664752 < baseStart_7664752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664769 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 4, 4]
def baseStart_7664769 : Nat := 118140960795 + 7664769 * 2 ^ 59
def prefixEnd_7664769 : Nat := 4983230072969 + 3 ^ 40 * 7664769 * 2
def baseEnd_7664769 : Nat := 1311903534227142429912625

theorem tailTrace_7664769 : CollatzResearch.WordTrace tailWord_7664769 prefixEnd_7664769 1311903534227142429912625 := by
  unfold tailWord_7664769
  simp only [CollatzResearch.WordTrace]
  refine ⟨279557091968858426172445361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186371394645905617448296907 279557091968858426172445361)
  ·
    refine ⟨209667818976643819629334021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279557091968858426172445361 209667818976643819629334021)
    ·
      refine ⟨39312716058120716180500129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209667818976643819629334021 39312716058120716180500129)
      ·
        refine ⟨29484537043590537135375097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39312716058120716180500129 29484537043590537135375097)
        ·
          refine ⟨22113402782692902851531323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29484537043590537135375097 22113402782692902851531323)
          ·
            refine ⟨33170104174039354277296985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22113402782692902851531323 33170104174039354277296985)
            ·
              refine ⟨24877578130529515707972739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33170104174039354277296985 24877578130529515707972739)
              ·
                refine ⟨37316367195794273561959109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24877578130529515707972739 37316367195794273561959109)
                ·
                  refine ⟨6996818849211426292867333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37316367195794273561959109 6996818849211426292867333)
                  ·
                    refine ⟨1311903534227142429912625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6996818849211426292867333 1311903534227142429912625)
                    ·
                      rfl

theorem cell23_7664769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_7664769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664769 prefixEnd_7664769 := by exact prefixLift 7664769
  have htrace : WordTrace (prefixWord ++ tailWord_7664769) baseStart_7664769 baseEnd_7664769 := by
    simpa [prefixWord, tailWord_7664769, baseEnd_7664769] using wordTrace_append hprefix tailTrace_7664769
  have hstable : (prefixWord ++ tailWord_7664769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664769).length < 2 ^ (prefixWord ++ tailWord_7664769).sum := by decide
  have hdescent : baseEnd_7664769 < baseStart_7664769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664772 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_7664772 : Nat := 118140960795 + 7664772 * 2 ^ 59
def prefixEnd_7664772 : Nat := 4983230072969 + 3 ^ 40 * 7664772 * 2
def baseEnd_7664772 : Nat := 3935712143123390778000361

theorem tailTrace_7664772 : CollatzResearch.WordTrace tailWord_7664772 prefixEnd_7664772 3935712143123390778000361 := by
  unfold tailWord_7664772
  simp only [CollatzResearch.WordTrace]
  refine ⟨139778600693923778842402285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186371467591898371789869713 139778600693923778842402285)
  ·
    refine ⟨52416975260221417065900857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139778600693923778842402285 52416975260221417065900857)
    ·
      refine ⟨39312731445166062799425643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52416975260221417065900857 39312731445166062799425643)
      ·
        refine ⟨58969097167749094199138465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39312731445166062799425643 58969097167749094199138465)
        ·
          refine ⟨44226822875811820649353849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58969097167749094199138465 44226822875811820649353849)
          ·
            refine ⟨33170117156858865487015387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44226822875811820649353849 33170117156858865487015387)
            ·
              refine ⟨49755175735288298230523081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33170117156858865487015387 49755175735288298230523081)
              ·
                refine ⟨37316381801466223672892311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49755175735288298230523081 37316381801466223672892311)
                ·
                  refine ⟨55974572702199335509338467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37316381801466223672892311 55974572702199335509338467)
                  ·
                    refine ⟨83961859053299003264007701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55974572702199335509338467 83961859053299003264007701)
                    ·
                      refine ⟨3935712143123390778000361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83961859053299003264007701 3935712143123390778000361)
                      ·
                        rfl

theorem cell23_7664772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_7664772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664772 prefixEnd_7664772 := by exact prefixLift 7664772
  have htrace : WordTrace (prefixWord ++ tailWord_7664772) baseStart_7664772 baseEnd_7664772 := by
    simpa [prefixWord, tailWord_7664772, baseEnd_7664772] using wordTrace_append hprefix tailTrace_7664772
  have hstable : (prefixWord ++ tailWord_7664772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664772).length < 2 ^ (prefixWord ++ tailWord_7664772).sum := by decide
  have hdescent : baseEnd_7664772 < baseStart_7664772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664782 : List Nat := [4, 1, 1, 3, 2, 1, 1, 10]
def baseStart_7664782 : Nat := 118140960795 + 7664782 * 2 ^ 59
def prefixEnd_7664782 : Nat := 4983230072969 + 3 ^ 40 * 7664782 * 2
def baseEnd_7664782 : Nat := 145767306589997619958345

theorem tailTrace_7664782 : CollatzResearch.WordTrace tailWord_7664782 prefixEnd_7664782 145767306589997619958345 := by
  unfold tailWord_7664782
  simp only [CollatzResearch.WordTrace]
  refine ⟨34944695764726416174083575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186371710745207552928445733 34944695764726416174083575)
  ·
    refine ⟨52417043647089624261125363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34944695764726416174083575 52417043647089624261125363)
    ·
      refine ⟨78625565470634436391688045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52417043647089624261125363 78625565470634436391688045)
      ·
        refine ⟨29484587051487913646883017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78625565470634436391688045 29484587051487913646883017)
        ·
          refine ⟨22113440288615935235162263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29484587051487913646883017 22113440288615935235162263)
          ·
            refine ⟨33170160432923902852743395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22113440288615935235162263 33170160432923902852743395)
            ·
              refine ⟨49755240649385854279115093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33170160432923902852743395 49755240649385854279115093)
              ·
                refine ⟨145767306589997619958345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49755240649385854279115093 145767306589997619958345)
                ·
                  rfl

theorem cell23_7664782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 10].length) (baseStart_7664782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664782 prefixEnd_7664782 := by exact prefixLift 7664782
  have htrace : WordTrace (prefixWord ++ tailWord_7664782) baseStart_7664782 baseEnd_7664782 := by
    simpa [prefixWord, tailWord_7664782, baseEnd_7664782] using wordTrace_append hprefix tailTrace_7664782
  have hstable : (prefixWord ++ tailWord_7664782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664782).length < 2 ^ (prefixWord ++ tailWord_7664782).sum := by decide
  have hdescent : baseEnd_7664782 < baseStart_7664782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664786 : List Nat := [3, 2, 3, 1, 1, 3, 1, 3, 2, 4]
def baseStart_7664786 : Nat := 118140960795 + 7664786 * 2 ^ 59
def prefixEnd_7664786 : Nat := 4983230072969 + 3 ^ 40 * 7664786 * 2
def baseEnd_7664786 : Nat := 1311906443950851241075099

theorem tailTrace_7664786 : CollatzResearch.WordTrace tailWord_7664786 prefixEnd_7664786 1311906443950851241075099 := by
  unfold tailWord_7664786
  simp only [CollatzResearch.WordTrace]
  refine ⟨69889428002449209518953553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186371808006531225383876141 69889428002449209518953553)
  ·
    refine ⟨52417071001836907139215165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69889428002449209518953553 52417071001836907139215165)
    ·
      refine ⟨19656401625688840177205687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52417071001836907139215165 19656401625688840177205687)
      ·
        refine ⟨29484602438533260265808531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19656401625688840177205687 29484602438533260265808531)
        ·
          refine ⟨44226903657799890398712797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29484602438533260265808531 44226903657799890398712797)
          ·
            refine ⟨16585088871674958899517299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44226903657799890398712797 16585088871674958899517299)
            ·
              refine ⟨24877633307512438349275949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16585088871674958899517299 24877633307512438349275949)
              ·
                refine ⟨9329112490317164380978481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24877633307512438349275949 9329112490317164380978481)
                ·
                  refine ⟨6996834367737873285733861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9329112490317164380978481 6996834367737873285733861)
                  ·
                    refine ⟨1311906443950851241075099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6996834367737873285733861 1311906443950851241075099)
                    ·
                      rfl

theorem cell23_7664786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_7664786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664786 prefixEnd_7664786 := by exact prefixLift 7664786
  have htrace : WordTrace (prefixWord ++ tailWord_7664786) baseStart_7664786 baseEnd_7664786 := by
    simpa [prefixWord, tailWord_7664786, baseEnd_7664786] using wordTrace_append hprefix tailTrace_7664786
  have hstable : (prefixWord ++ tailWord_7664786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664786).length < 2 ^ (prefixWord ++ tailWord_7664786).sum := by decide
  have hdescent : baseEnd_7664786 < baseStart_7664786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664796 : List Nat := [2, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_7664796 : Nat := 118140960795 + 7664796 * 2 ^ 59
def prefixEnd_7664796 : Nat := 4983230072969 + 3 ^ 40 * 7664796 * 2
def baseEnd_7664796 : Nat := 3935724466659098684100251

theorem tailTrace_7664796 : CollatzResearch.WordTrace tailWord_7664796 prefixEnd_7664796 3935724466659098684100251 := by
  unfold tailWord_7664796
  simp only [CollatzResearch.WordTrace]
  refine ⟨139779038369880304891839121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186372051159840406522452161 139779038369880304891839121)
  ·
    refine ⟨104834278777410228668879341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139779038369880304891839121 104834278777410228668879341)
    ·
      refine ⟨39312854541528835750829753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104834278777410228668879341 39312854541528835750829753)
      ·
        refine ⟨29484640906146626813122315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39312854541528835750829753 29484640906146626813122315)
        ·
          refine ⟨44226961359219940219683473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29484640906146626813122315 44226961359219940219683473)
          ·
            refine ⟨33170221019414955164762605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44226961359219940219683473 33170221019414955164762605)
            ·
              refine ⟨12438832882280608186785977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33170221019414955164762605 12438832882280608186785977)
              ·
                refine ⟨9329124661710456140089483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12438832882280608186785977 9329124661710456140089483)
                ·
                  refine ⟨13993686992565684210134225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9329124661710456140089483 13993686992565684210134225)
                  ·
                    refine ⟨10495265244424263157600669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13993686992565684210134225 10495265244424263157600669)
                    ·
                      refine ⟨3935724466659098684100251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10495265244424263157600669 3935724466659098684100251)
                      ·
                        rfl

theorem cell23_7664796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_7664796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664796 prefixEnd_7664796 := by exact prefixLift 7664796
  have htrace : WordTrace (prefixWord ++ tailWord_7664796) baseStart_7664796 baseEnd_7664796 := by
    simpa [prefixWord, tailWord_7664796, baseEnd_7664796] using wordTrace_append hprefix tailTrace_7664796
  have hstable : (prefixWord ++ tailWord_7664796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664796).length < 2 ^ (prefixWord ++ tailWord_7664796).sum := by decide
  have hdescent : baseEnd_7664796 < baseStart_7664796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664813 : List Nat := [1, 5, 2, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_7664813 : Nat := 118140960795 + 7664813 * 2 ^ 59
def prefixEnd_7664813 : Nat := 4983230072969 + 3 ^ 40 * 7664813 * 2
def baseEnd_7664813 : Nat := 3935733195830225117587673

theorem tailTrace_7664813 : CollatzResearch.WordTrace tailWord_7664813 prefixEnd_7664813 3935733195830225117587673 := by
  unfold tailWord_7664813
  simp only [CollatzResearch.WordTrace]
  refine ⟨279558696780699021687047093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186372464520466014458031395 279558696780699021687047093)
  ·
    refine ⟨26208627823190533283160665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279558696780699021687047093 26208627823190533283160665)
    ·
      refine ⟨19656470867392899962370499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26208627823190533283160665 19656470867392899962370499)
      ·
        refine ⟨29484706301089349943555749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19656470867392899962370499 29484706301089349943555749)
        ·
          refine ⟨5528382431454253114416703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29484706301089349943555749 5528382431454253114416703)
          ·
            refine ⟨8292573647181379671625055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5528382431454253114416703 8292573647181379671625055)
            ·
              refine ⟨12438860470772069507437583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8292573647181379671625055 12438860470772069507437583)
              ·
                refine ⟨18658290706158104261156375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12438860470772069507437583 18658290706158104261156375)
                ·
                  refine ⟨27987436059237156391734563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18658290706158104261156375 27987436059237156391734563)
                  ·
                    refine ⟨41981154088855734587601845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27987436059237156391734563 41981154088855734587601845)
                    ·
                      refine ⟨3935733195830225117587673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41981154088855734587601845 3935733195830225117587673)
                      ·
                        rfl

theorem cell23_7664813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_7664813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664813 prefixEnd_7664813 := by exact prefixLift 7664813
  have htrace : WordTrace (prefixWord ++ tailWord_7664813) baseStart_7664813 baseEnd_7664813 := by
    simpa [prefixWord, tailWord_7664813, baseEnd_7664813] using wordTrace_append hprefix tailTrace_7664813
  have hstable : (prefixWord ++ tailWord_7664813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664813).length < 2 ^ (prefixWord ++ tailWord_7664813).sum := by decide
  have hdescent : baseEnd_7664813 < baseStart_7664813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664842 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 1, 8]
def baseStart_7664842 : Nat := 118140960795 + 7664842 * 2 ^ 59
def prefixEnd_7664842 : Nat := 4983230072969 + 3 ^ 40 * 7664842 * 2
def baseEnd_7664842 : Nat := 1311916028923068501375013

theorem tailTrace_7664842 : CollatzResearch.WordTrace tailWord_7664842 prefixEnd_7664842 1311916028923068501375013 := by
  unfold tailWord_7664842
  simp only [CollatzResearch.WordTrace]
  refine ⟨69889938624398489909963195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186373169665062639759901853 69889938624398489909963195)
  ·
    refine ⟨104834907936597734864944793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69889938624398489909963195 104834907936597734864944793)
    ·
      refine ⟨78626180952448301148708595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104834907936597734864944793 78626180952448301148708595)
      ·
        refine ⟨117939271428672451723062893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78626180952448301148708595 117939271428672451723062893)
        ·
          refine ⟨44227226785752169396148585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117939271428672451723062893 44227226785752169396148585)
          ·
            refine ⟨33170420089314127047111439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44227226785752169396148585 33170420089314127047111439)
            ·
              refine ⟨49755630133971190570667159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33170420089314127047111439 49755630133971190570667159)
              ·
                refine ⟨74633445200956785856000739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49755630133971190570667159 74633445200956785856000739)
                ·
                  refine ⟨111950167801435178784001109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74633445200956785856000739 111950167801435178784001109)
                  ·
                    refine ⟨1311916028923068501375013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111950167801435178784001109 1311916028923068501375013)
                    ·
                      rfl

theorem cell23_7664842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_7664842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664842 prefixEnd_7664842 := by exact prefixLift 7664842
  have htrace : WordTrace (prefixWord ++ tailWord_7664842) baseStart_7664842 baseEnd_7664842 := by
    simpa [prefixWord, tailWord_7664842, baseEnd_7664842] using wordTrace_append hprefix tailTrace_7664842
  have hstable : (prefixWord ++ tailWord_7664842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664842).length < 2 ^ (prefixWord ++ tailWord_7664842).sum := by decide
  have hdescent : baseEnd_7664842 < baseStart_7664842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664872 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 9]
def baseStart_7664872 : Nat := 118140960795 + 7664872 * 2 ^ 59
def prefixEnd_7664872 : Nat := 4983230072969 + 3 ^ 40 * 7664872 * 2
def baseEnd_7664872 : Nat := 437307054576537820749989

theorem tailTrace_7664872 : CollatzResearch.WordTrace tailWord_7664872 prefixEnd_7664872 437307054576537820749989 := by
  unfold tailWord_7664872
  simp only [CollatzResearch.WordTrace]
  refine ⟨139780424343742637381722435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186373899124990183175629913 139780424343742637381722435)
  ·
    refine ⟨209670636515613956072583653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139780424343742637381722435 209670636515613956072583653)
    ·
      refine ⟨39313244346677616763609435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209670636515613956072583653 39313244346677616763609435)
      ·
        refine ⟨58969866520016425145414153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39313244346677616763609435 58969866520016425145414153)
        ·
          refine ⟨44227399890012318859060615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58969866520016425145414153 44227399890012318859060615)
          ·
            refine ⟨66341099835018478288590923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44227399890012318859060615 66341099835018478288590923)
            ·
              refine ⟨99511649752527717432886385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66341099835018478288590923 99511649752527717432886385)
              ·
                refine ⟨74633737314395788074664789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99511649752527717432886385 74633737314395788074664789)
                ·
                  refine ⟨437307054576537820749989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74633737314395788074664789 437307054576537820749989)
                  ·
                    rfl

theorem cell23_7664872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 9].length) (baseStart_7664872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664872 prefixEnd_7664872 := by exact prefixLift 7664872
  have htrace : WordTrace (prefixWord ++ tailWord_7664872) baseStart_7664872 baseEnd_7664872 := by
    simpa [prefixWord, tailWord_7664872, baseEnd_7664872] using wordTrace_append hprefix tailTrace_7664872
  have hstable : (prefixWord ++ tailWord_7664872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664872).length < 2 ^ (prefixWord ++ tailWord_7664872).sum := by decide
  have hdescent : baseEnd_7664872 < baseStart_7664872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664883 : List Nat := [1, 1, 1, 2, 2, 5, 3, 2, 2, 2, 2]
def baseStart_7664883 : Nat := 118140960795 + 7664883 * 2 ^ 59
def prefixEnd_7664883 : Nat := 4983230072969 + 3 ^ 40 * 7664883 * 2
def baseEnd_7664883 : Nat := 3935769139476039843712351

theorem tailTrace_7664883 : CollatzResearch.WordTrace tailWord_7664883 prefixEnd_7664883 3935769139476039843712351 := by
  unfold tailWord_7664883
  simp only [CollatzResearch.WordTrace]
  refine ⟨279561249890445423642095303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186374166593630282428063535 279561249890445423642095303)
  ·
    refine ⟨419341874835668135463142955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279561249890445423642095303 419341874835668135463142955)
    ·
      refine ⟨629012812253502203194714433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419341874835668135463142955 629012812253502203194714433)
      ·
        refine ⟨471759609190126652396035825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629012812253502203194714433 471759609190126652396035825)
        ·
          refine ⟨353819706892594989297026869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471759609190126652396035825 353819706892594989297026869)
          ·
            refine ⟨33170597521180780246596269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 353819706892594989297026869 33170597521180780246596269)
            ·
              refine ⟨12438974070442792592473601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33170597521180780246596269 12438974070442792592473601)
              ·
                refine ⟨9329230552832094444355201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12438974070442792592473601 9329230552832094444355201)
                ·
                  refine ⟨6996922914624070833266401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9329230552832094444355201 6996922914624070833266401)
                  ·
                    refine ⟨5247692185968053124949801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6996922914624070833266401 5247692185968053124949801)
                    ·
                      refine ⟨3935769139476039843712351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5247692185968053124949801 3935769139476039843712351)
                      ·
                        rfl

theorem cell23_7664883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 2, 2].length) (baseStart_7664883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664883 prefixEnd_7664883 := by exact prefixLift 7664883
  have htrace : WordTrace (prefixWord ++ tailWord_7664883) baseStart_7664883 baseEnd_7664883 := by
    simpa [prefixWord, tailWord_7664883, baseEnd_7664883] using wordTrace_append hprefix tailTrace_7664883
  have hstable : (prefixWord ++ tailWord_7664883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664883).length < 2 ^ (prefixWord ++ tailWord_7664883).sum := by decide
  have hdescent : baseEnd_7664883 < baseStart_7664883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664889 : List Nat := [1, 2, 1, 3, 1, 1, 3, 6, 5]
def baseStart_7664889 : Nat := 118140960795 + 7664889 * 2 ^ 59
def prefixEnd_7664889 : Nat := 4983230072969 + 3 ^ 40 * 7664889 * 2
def baseEnd_7664889 : Nat := 437308024484440757804147

theorem tailTrace_7664889 : CollatzResearch.WordTrace tailWord_7664889 prefixEnd_7664889 437308024484440757804147 := by
  unfold tailWord_7664889
  simp only [CollatzResearch.WordTrace]
  refine ⟨279561468728423686666813721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186374312485615791111209147 279561468728423686666813721)
  ·
    refine ⟨209671101546317765000110291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279561468728423686666813721 209671101546317765000110291)
    ·
      refine ⟨314506652319476647500165437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209671101546317765000110291 314506652319476647500165437)
      ·
        refine ⟨117939994619803742812562039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314506652319476647500165437 117939994619803742812562039)
        ·
          refine ⟨176909991929705614218843059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117939994619803742812562039 176909991929705614218843059)
          ·
            refine ⟨265364987894558421328264589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176909991929705614218843059 265364987894558421328264589)
            ·
              refine ⟨99511870460459407998099221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265364987894558421328264589 99511870460459407998099221)
              ·
                refine ⟨4664618927834034749910901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99511870460459407998099221 4664618927834034749910901)
                ·
                  refine ⟨437308024484440757804147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4664618927834034749910901 437308024484440757804147)
                  ·
                    rfl

theorem cell23_7664889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 5].length) (baseStart_7664889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664889 prefixEnd_7664889 := by exact prefixLift 7664889
  have htrace : WordTrace (prefixWord ++ tailWord_7664889) baseStart_7664889 baseEnd_7664889 := by
    simpa [prefixWord, tailWord_7664889, baseEnd_7664889] using wordTrace_append hprefix tailTrace_7664889
  have hstable : (prefixWord ++ tailWord_7664889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664889).length < 2 ^ (prefixWord ++ tailWord_7664889).sum := by decide
  have hdescent : baseEnd_7664889 < baseStart_7664889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664899 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 3]
def baseStart_7664899 : Nat := 118140960795 + 7664899 * 2 ^ 59
def prefixEnd_7664899 : Nat := 4983230072969 + 3 ^ 40 * 7664899 * 2
def baseEnd_7664899 : Nat := 3935777355166511781112277

theorem tailTrace_7664899 : CollatzResearch.WordTrace tailWord_7664899 prefixEnd_7664899 3935777355166511781112277 := by
  unfold tailWord_7664899
  simp only [CollatzResearch.WordTrace]
  refine ⟨279561833458387458374677751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186374555638924972249785167 279561833458387458374677751)
  ·
    refine ⟨419342750187581187562016627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279561833458387458374677751 419342750187581187562016627)
    ·
      refine ⟨629014125281371781343024941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419342750187581187562016627 629014125281371781343024941)
      ·
        refine ⟨235880296980514418003634353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 629014125281371781343024941 235880296980514418003634353)
        ·
          refine ⟨176910222735385813502725765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235880296980514418003634353 176910222735385813502725765)
          ·
            refine ⟨33170666762884840031761081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176910222735385813502725765 33170666762884840031761081)
            ·
              refine ⟨24878000072163630023820811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33170666762884840031761081 24878000072163630023820811)
              ·
                refine ⟨37317000108245445035731217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24878000072163630023820811 37317000108245445035731217)
                ·
                  refine ⟨27987750081184083776798413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37317000108245445035731217 27987750081184083776798413)
                  ·
                    refine ⟨10495406280444031416299405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27987750081184083776798413 10495406280444031416299405)
                    ·
                      refine ⟨3935777355166511781112277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10495406280444031416299405 3935777355166511781112277)
                      ·
                        rfl

theorem cell23_7664899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_7664899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664899 prefixEnd_7664899 := by exact prefixLift 7664899
  have htrace : WordTrace (prefixWord ++ tailWord_7664899) baseStart_7664899 baseEnd_7664899 := by
    simpa [prefixWord, tailWord_7664899, baseEnd_7664899] using wordTrace_append hprefix tailTrace_7664899
  have hstable : (prefixWord ++ tailWord_7664899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664899).length < 2 ^ (prefixWord ++ tailWord_7664899).sum := by decide
  have hdescent : baseEnd_7664899 < baseStart_7664899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664919 : List Nat := [1, 1, 3, 4, 1, 1, 2, 3, 2, 5]
def baseStart_7664919 : Nat := 118140960795 + 7664919 * 2 ^ 59
def prefixEnd_7664919 : Nat := 4983230072969 + 3 ^ 40 * 7664919 * 2
def baseEnd_7664919 : Nat := 1311929208259867234287395

theorem tailTrace_7664919 : CollatzResearch.WordTrace tailWord_7664919 prefixEnd_7664919 1311929208259867234287395 := by
  unfold tailWord_7664919
  simp only [CollatzResearch.WordTrace]
  refine ⟨279562562918315001790405811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186375041945543334526937207 279562562918315001790405811)
  ·
    refine ⟨419343844377472502685608717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279562562918315001790405811 419343844377472502685608717)
    ·
      refine ⟨157253941641552188507103269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419343844377472502685608717 157253941641552188507103269)
      ·
        refine ⟨29485114057791035345081863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157253941641552188507103269 29485114057791035345081863)
        ·
          refine ⟨44227671086686553017622795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29485114057791035345081863 44227671086686553017622795)
          ·
            refine ⟨66341506630029829526434193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44227671086686553017622795 66341506630029829526434193)
            ·
              refine ⟨49756129972522372144825645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66341506630029829526434193 49756129972522372144825645)
              ·
                refine ⟨18658548739695889554309617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49756129972522372144825645 18658548739695889554309617)
                ·
                  refine ⟨13993911554771917165732213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18658548739695889554309617 13993911554771917165732213)
                  ·
                    refine ⟨1311929208259867234287395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13993911554771917165732213 1311929208259867234287395)
                    ·
                      rfl

theorem cell23_7664919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_7664919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664919 prefixEnd_7664919 := by exact prefixLift 7664919
  have htrace : WordTrace (prefixWord ++ tailWord_7664919) baseStart_7664919 baseEnd_7664919 := by
    simpa [prefixWord, tailWord_7664919, baseEnd_7664919] using wordTrace_append hprefix tailTrace_7664919
  have hstable : (prefixWord ++ tailWord_7664919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664919).length < 2 ^ (prefixWord ++ tailWord_7664919).sum := by decide
  have hdescent : baseEnd_7664919 < baseStart_7664919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664936 : List Nat := [2, 1, 5, 1, 2, 2, 1, 2, 2, 5]
def baseStart_7664936 : Nat := 118140960795 + 7664936 * 2 ^ 59
def prefixEnd_7664936 : Nat := 4983230072969 + 3 ^ 40 * 7664936 * 2
def baseEnd_7664936 : Nat := 1311932117983576045449869

theorem tailTrace_7664936 : CollatzResearch.WordTrace tailWord_7664936 prefixEnd_7664936 1311932117983576045449869 := by
  unfold tailWord_7664936
  simp only [CollatzResearch.WordTrace]
  refine ⟨139781591479626706846887331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186375455306168942462516441 139781591479626706846887331)
  ·
    refine ⟨209672387219440060270330997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139781591479626706846887331 209672387219440060270330997)
    ·
      refine ⟨19656786301822505650343531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209672387219440060270330997 19656786301822505650343531)
      ·
        refine ⟨29485179452733758475515297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19656786301822505650343531 29485179452733758475515297)
        ·
          refine ⟨22113884589550318856636473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29485179452733758475515297 22113884589550318856636473)
          ·
            refine ⟨16585413442162739142477355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22113884589550318856636473 16585413442162739142477355)
            ·
              refine ⟨24878120163244108713716033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16585413442162739142477355 24878120163244108713716033)
              ·
                refine ⟨18658590122433081535287025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24878120163244108713716033 18658590122433081535287025)
                ·
                  refine ⟨13993942591824811151465269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18658590122433081535287025 13993942591824811151465269)
                  ·
                    refine ⟨1311932117983576045449869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13993942591824811151465269 1311932117983576045449869)
                    ·
                      rfl

theorem cell23_7664936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_7664936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664936 prefixEnd_7664936 := by exact prefixLift 7664936
  have htrace : WordTrace (prefixWord ++ tailWord_7664936) baseStart_7664936 baseEnd_7664936 := by
    simpa [prefixWord, tailWord_7664936, baseEnd_7664936] using wordTrace_append hprefix tailTrace_7664936
  have hstable : (prefixWord ++ tailWord_7664936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664936).length < 2 ^ (prefixWord ++ tailWord_7664936).sum := by decide
  have hdescent : baseEnd_7664936 < baseStart_7664936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664939 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 5, 6, 2]
def baseStart_7664939 : Nat := 118140960795 + 7664939 * 2 ^ 59
def prefixEnd_7664939 : Nat := 4983230072969 + 3 ^ 40 * 7664939 * 2
def baseEnd_7664939 : Nat := 3935797894392691624612093

theorem tailTrace_7664939 : CollatzResearch.WordTrace tailWord_7664939 prefixEnd_7664939 3935797894392691624612093 := by
  unfold tailWord_7664939
  simp only [CollatzResearch.WordTrace]
  refine ⟨279563292378242545206133871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186375528252161696804089247 279563292378242545206133871)
  ·
    refine ⟨419344938567363817809200807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279563292378242545206133871 419344938567363817809200807)
    ·
      refine ⟨629017407851045726713801211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419344938567363817809200807 629017407851045726713801211)
      ·
        refine ⟨943526111776568590070701817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629017407851045726713801211 943526111776568590070701817)
        ·
          refine ⟨707644583832426442553026363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 943526111776568590070701817 707644583832426442553026363)
          ·
            refine ⟨1061466875748639663829539545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707644583832426442553026363 1061466875748639663829539545)
            ·
              refine ⟨796100156811479747872154659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1061466875748639663829539545 796100156811479747872154659)
              ·
                refine ⟨1194150235217219621808231989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796100156811479747872154659 1194150235217219621808231989)
                ·
                  refine ⟨111951584551614339544521749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1194150235217219621808231989 111951584551614339544521749)
                  ·
                    refine ⟨5247730525856922166149457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111951584551614339544521749 5247730525856922166149457)
                    ·
                      refine ⟨3935797894392691624612093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5247730525856922166149457 3935797894392691624612093)
                      ·
                        rfl

theorem cell23_7664939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 6, 2].length) (baseStart_7664939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664939 prefixEnd_7664939 := by exact prefixLift 7664939
  have htrace : WordTrace (prefixWord ++ tailWord_7664939) baseStart_7664939 baseEnd_7664939 := by
    simpa [prefixWord, tailWord_7664939, baseEnd_7664939] using wordTrace_append hprefix tailTrace_7664939
  have hstable : (prefixWord ++ tailWord_7664939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664939).length < 2 ^ (prefixWord ++ tailWord_7664939).sum := by decide
  have hdescent : baseEnd_7664939 < baseStart_7664939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664976 : List Nat := [2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 3]
def baseStart_7664976 : Nat := 118140960795 + 7664976 * 2 ^ 59
def prefixEnd_7664976 : Nat := 4983230072969 + 3 ^ 40 * 7664976 * 2
def baseEnd_7664976 : Nat := 3935816893176907979849423

theorem tailTrace_7664976 : CollatzResearch.WordTrace tailWord_7664976 prefixEnd_7664976 3935816893176907979849423 := by
  unfold tailWord_7664976
  simp only [CollatzResearch.WordTrace]
  refine ⟨139782320939554250262615391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186376427919405667016820521 139782320939554250262615391)
  ·
    refine ⟨209673481409331375393923087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139782320939554250262615391 209673481409331375393923087)
    ·
      refine ⟨314510222113997063090884631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209673481409331375393923087 314510222113997063090884631)
      ·
        refine ⟨471765333170995594636326947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314510222113997063090884631 471765333170995594636326947)
        ·
          refine ⟨707647999756493391954490421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471765333170995594636326947 707647999756493391954490421)
          ·
            refine ⟨66341999977171255495733477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 707647999756493391954490421 66341999977171255495733477)
            ·
              refine ⟨12439124995719610405450027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66341999977171255495733477 12439124995719610405450027)
              ·
                refine ⟨18658687493579415608175041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12439124995719610405450027 18658687493579415608175041)
                ·
                  refine ⟨13994015620184561706131281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18658687493579415608175041 13994015620184561706131281)
                  ·
                    refine ⟨10495511715138421279598461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13994015620184561706131281 10495511715138421279598461)
                    ·
                      refine ⟨3935816893176907979849423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10495511715138421279598461 3935816893176907979849423)
                      ·
                        rfl

theorem cell23_7664976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 3].length) (baseStart_7664976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664976 prefixEnd_7664976 := by exact prefixLift 7664976
  have htrace : WordTrace (prefixWord ++ tailWord_7664976) baseStart_7664976 baseEnd_7664976 := by
    simpa [prefixWord, tailWord_7664976, baseEnd_7664976] using wordTrace_append hprefix tailTrace_7664976
  have hstable : (prefixWord ++ tailWord_7664976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664976).length < 2 ^ (prefixWord ++ tailWord_7664976).sum := by decide
  have hdescent : baseEnd_7664976 < baseStart_7664976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664996 : List Nat := [2, 3, 1, 1, 3, 3, 2, 2, 6]
def baseStart_7664996 : Nat := 118140960795 + 7664996 * 2 ^ 59
def prefixEnd_7664996 : Nat := 4983230072969 + 3 ^ 40 * 7664996 * 2
def baseEnd_7664996 : Nat := 437314129198888655733259

theorem tailTrace_7664996 : CollatzResearch.WordTrace tailWord_7664996 prefixEnd_7664996 437314129198888655733259 := by
  unfold tailWord_7664996
  simp only [CollatzResearch.WordTrace]
  refine ⟨139782685669518021970479421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186376914226024029293972561 139782685669518021970479421)
  ·
    refine ⟨52418507126069258238929783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139782685669518021970479421 52418507126069258238929783)
    ·
      refine ⟨78627760689103887358394675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52418507126069258238929783 78627760689103887358394675)
      ·
        refine ⟨117941641033655831037592013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78627760689103887358394675 117941641033655831037592013)
        ·
          refine ⟨44228115387620936639097005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117941641033655831037592013 44228115387620936639097005)
          ·
            refine ⟨16585543270357851239661377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44228115387620936639097005 16585543270357851239661377)
            ·
              refine ⟨12439157452768388429746033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16585543270357851239661377 12439157452768388429746033)
              ·
                refine ⟨9329368089576291322309525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12439157452768388429746033 9329368089576291322309525)
                ·
                  refine ⟨437314129198888655733259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9329368089576291322309525 437314129198888655733259)
                  ·
                    rfl

theorem cell23_7664996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_7664996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664996 prefixEnd_7664996 := by exact prefixLift 7664996
  have htrace : WordTrace (prefixWord ++ tailWord_7664996) baseStart_7664996 baseEnd_7664996 := by
    simpa [prefixWord, tailWord_7664996, baseEnd_7664996] using wordTrace_append hprefix tailTrace_7664996
  have hstable : (prefixWord ++ tailWord_7664996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664996).length < 2 ^ (prefixWord ++ tailWord_7664996).sum := by decide
  have hdescent : baseEnd_7664996 < baseStart_7664996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665000 : List Nat := [2, 1, 4, 2, 3, 1, 1, 4, 1, 4]
def baseStart_7665000 : Nat := 118140960795 + 7665000 * 2 ^ 59
def prefixEnd_7665000 : Nat := 4983230072969 + 3 ^ 40 * 7665000 * 2
def baseEnd_7665000 : Nat := 1311943072237538628649771

theorem tailTrace_7665000 : CollatzResearch.WordTrace tailWord_7665000 prefixEnd_7665000 1311943072237538628649771 := by
  unfold tailWord_7665000
  simp only [CollatzResearch.WordTrace]
  refine ⟨139782758615510776312052227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186377011487347701749402969 139782758615510776312052227)
  ·
    refine ⟨209674137923266164468078341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139782758615510776312052227 209674137923266164468078341)
    ·
      refine ⟨39313900860612405837764689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209674137923266164468078341 39313900860612405837764689)
      ·
        refine ⟨29485425645459304378323517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39313900860612405837764689 29485425645459304378323517)
        ·
          refine ⟨11057034617047239141871319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29485425645459304378323517 11057034617047239141871319)
          ·
            refine ⟨16585551925570858712806979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11057034617047239141871319 16585551925570858712806979)
            ·
              refine ⟨24878327888356288069210469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16585551925570858712806979 24878327888356288069210469)
              ·
                refine ⟨4664686479066804012976963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24878327888356288069210469 4664686479066804012976963)
                ·
                  refine ⟨6997029718600206019465445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4664686479066804012976963 6997029718600206019465445)
                  ·
                    refine ⟨1311943072237538628649771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6997029718600206019465445 1311943072237538628649771)
                    ·
                      rfl

theorem cell23_7665000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_7665000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665000 prefixEnd_7665000 := by exact prefixLift 7665000
  have htrace : WordTrace (prefixWord ++ tailWord_7665000) baseStart_7665000 baseEnd_7665000 := by
    simpa [prefixWord, tailWord_7665000, baseEnd_7665000] using wordTrace_append hprefix tailTrace_7665000
  have hstable : (prefixWord ++ tailWord_7665000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665000).length < 2 ^ (prefixWord ++ tailWord_7665000).sum := by decide
  have hdescent : baseEnd_7665000 < baseStart_7665000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665009 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 3, 5]
def baseStart_7665009 : Nat := 118140960795 + 7665009 * 2 ^ 59
def prefixEnd_7665009 : Nat := 4983230072969 + 3 ^ 40 * 7665009 * 2
def baseEnd_7665009 : Nat := 1311944612679502116912257

theorem tailTrace_7665009 : CollatzResearch.WordTrace tailWord_7665009 prefixEnd_7665009 1311944612679502116912257 := by
  unfold tailWord_7665009
  simp only [CollatzResearch.WordTrace]
  refine ⟨279565845487988947161182081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186377230325325964774121387 279565845487988947161182081)
  ·
    refine ⟨209674384115991710370886561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279565845487988947161182081 209674384115991710370886561)
    ·
      refine ⟨157255788086993782778164921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209674384115991710370886561 157255788086993782778164921)
      ·
        refine ⟨117941841065245337083623691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157255788086993782778164921 117941841065245337083623691)
        ·
          refine ⟨176912761597868005625435537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117941841065245337083623691 176912761597868005625435537)
          ·
            refine ⟨132684571198401004219076653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176912761597868005625435537 132684571198401004219076653)
            ·
              refine ⟨49756714199400376582153745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132684571198401004219076653 49756714199400376582153745)
              ·
                refine ⟨37317535649550282436615309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49756714199400376582153745 37317535649550282436615309)
                ·
                  refine ⟨13994075868581355913730741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37317535649550282436615309 13994075868581355913730741)
                  ·
                    refine ⟨1311944612679502116912257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13994075868581355913730741 1311944612679502116912257)
                    ·
                      rfl

theorem cell23_7665009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_7665009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665009 prefixEnd_7665009 := by exact prefixLift 7665009
  have htrace : WordTrace (prefixWord ++ tailWord_7665009) baseStart_7665009 baseEnd_7665009 := by
    simpa [prefixWord, tailWord_7665009, baseEnd_7665009] using wordTrace_append hprefix tailTrace_7665009
  have hstable : (prefixWord ++ tailWord_7665009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665009).length < 2 ^ (prefixWord ++ tailWord_7665009).sum := by decide
  have hdescent : baseEnd_7665009 < baseStart_7665009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665033 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 1, 5, 2]
def baseStart_7665033 : Nat := 118140960795 + 7665033 * 2 ^ 59
def prefixEnd_7665033 : Nat := 4983230072969 + 3 ^ 40 * 7665033 * 2
def baseEnd_7665033 : Nat := 3935846161574214256836661

theorem tailTrace_7665033 : CollatzResearch.WordTrace tailWord_7665033 prefixEnd_7665033 3935846161574214256836661 := by
  unfold tailWord_7665033
  simp only [CollatzResearch.WordTrace]
  refine ⟨279566720839901999260055753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186377813893267999506703835 279566720839901999260055753)
  ·
    refine ⟨209675040629926499445041815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279566720839901999260055753 209675040629926499445041815)
    ·
      refine ⟨314512560944889749167562723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209675040629926499445041815 314512560944889749167562723)
      ·
        refine ⟨471768841417334623751344085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314512560944889749167562723 471768841417334623751344085)
        ·
          refine ⟨11057082220718780244172127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 471768841417334623751344085 11057082220718780244172127)
          ·
            refine ⟨16585623331078170366258191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11057082220718780244172127 16585623331078170366258191)
            ·
              refine ⟨24878434996617255549387287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16585623331078170366258191 24878434996617255549387287)
              ·
                refine ⟨37317652494925883324080931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24878434996617255549387287 37317652494925883324080931)
                ·
                  refine ⟨55976478742388824986121397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37317652494925883324080931 55976478742388824986121397)
                  ·
                    refine ⟨5247794882098952342448881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55976478742388824986121397 5247794882098952342448881)
                    ·
                      refine ⟨3935846161574214256836661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5247794882098952342448881 3935846161574214256836661)
                      ·
                        rfl

theorem cell23_7665033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 5, 2].length) (baseStart_7665033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665033 prefixEnd_7665033 := by exact prefixLift 7665033
  have htrace : WordTrace (prefixWord ++ tailWord_7665033) baseStart_7665033 baseEnd_7665033 := by
    simpa [prefixWord, tailWord_7665033, baseEnd_7665033] using wordTrace_append hprefix tailTrace_7665033
  have hstable : (prefixWord ++ tailWord_7665033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665033).length < 2 ^ (prefixWord ++ tailWord_7665033).sum := by decide
  have hdescent : baseEnd_7665033 < baseStart_7665033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665056 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 4, 4]
def baseStart_7665056 : Nat := 118140960795 + 7665056 * 2 ^ 59
def prefixEnd_7665056 : Nat := 4983230072969 + 3 ^ 40 * 7665056 * 2
def baseEnd_7665056 : Nat := 1311952657209755888949685

theorem tailTrace_7665056 : CollatzResearch.WordTrace tailWord_7665056 prefixEnd_7665056 1311952657209755888949685 := by
  unfold tailWord_7665056
  simp only [CollatzResearch.WordTrace]
  refine ⟨139783779859409337094071511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186378373145879116125428681 139783779859409337094071511)
  ·
    refine ⟨209675669789114005641107267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139783779859409337094071511 209675669789114005641107267)
    ·
      refine ⟨314513504683671008461660901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209675669789114005641107267 314513504683671008461660901)
      ·
        refine ⟨58971282128188314086561419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314513504683671008461660901 58971282128188314086561419)
        ·
          refine ⟨88456923192282471129842129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58971282128188314086561419 88456923192282471129842129)
          ·
            refine ⟨66342692394211853347381597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88456923192282471129842129 66342692394211853347381597)
            ·
              refine ⟨24878509647829445005268099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66342692394211853347381597 24878509647829445005268099)
              ·
                refine ⟨37317764471744167507902149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24878509647829445005268099 37317764471744167507902149)
                ·
                  refine ⟨6997080838452031407731653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37317764471744167507902149 6997080838452031407731653)
                  ·
                    refine ⟨1311952657209755888949685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6997080838452031407731653 1311952657209755888949685)
                    ·
                      rfl

theorem cell23_7665056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 4, 4].length) (baseStart_7665056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665056 prefixEnd_7665056 := by exact prefixLift 7665056
  have htrace : WordTrace (prefixWord ++ tailWord_7665056) baseStart_7665056 baseEnd_7665056 := by
    simpa [prefixWord, tailWord_7665056, baseEnd_7665056] using wordTrace_append hprefix tailTrace_7665056
  have hstable : (prefixWord ++ tailWord_7665056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665056).length < 2 ^ (prefixWord ++ tailWord_7665056).sum := by decide
  have hdescent : baseEnd_7665056 < baseStart_7665056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665059 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 6]
def baseStart_7665059 : Nat := 118140960795 + 7665059 * 2 ^ 59
def prefixEnd_7665059 : Nat := 4983230072969 + 3 ^ 40 * 7665059 * 2
def baseEnd_7665059 : Nat := 3935859512071231155111541

theorem tailTrace_7665059 : CollatzResearch.WordTrace tailWord_7665059 prefixEnd_7665059 3935859512071231155111541 := by
  unfold tailWord_7665059
  simp only [CollatzResearch.WordTrace]
  refine ⟨279567669137807805700502231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186378446091871870467001487 279567669137807805700502231)
  ·
    refine ⟨419351503706711708550753347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279567669137807805700502231 419351503706711708550753347)
    ·
      refine ⟨629027255560067562826130021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419351503706711708550753347 629027255560067562826130021)
      ·
        refine ⟨117942610417512668029899379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 629027255560067562826130021 117942610417512668029899379)
        ·
          refine ⟨176913915626269002044849069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117942610417512668029899379 176913915626269002044849069)
          ·
            refine ⟨66342718359850875766818401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176913915626269002044849069 66342718359850875766818401)
            ·
              refine ⟨49757038769888156825113801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66342718359850875766818401 49757038769888156825113801)
              ·
                refine ⟨37317779077416117618835351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49757038769888156825113801 37317779077416117618835351)
                ·
                  refine ⟨55976668616124176428253027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37317779077416117618835351 55976668616124176428253027)
                  ·
                    refine ⟨83965002924186264642379541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55976668616124176428253027 83965002924186264642379541)
                    ·
                      refine ⟨3935859512071231155111541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83965002924186264642379541 3935859512071231155111541)
                      ·
                        rfl

theorem cell23_7665059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_7665059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665059 prefixEnd_7665059 := by exact prefixLift 7665059
  have htrace : WordTrace (prefixWord ++ tailWord_7665059) baseStart_7665059 baseEnd_7665059 := by
    simpa [prefixWord, tailWord_7665059, baseEnd_7665059] using wordTrace_append hprefix tailTrace_7665059
  have hstable : (prefixWord ++ tailWord_7665059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665059).length < 2 ^ (prefixWord ++ tailWord_7665059).sum := by decide
  have hdescent : baseEnd_7665059 < baseStart_7665059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665096 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 3, 3, 3]
def baseStart_7665096 : Nat := 118140960795 + 7665096 * 2 ^ 59
def prefixEnd_7665096 : Nat := 4983230072969 + 3 ^ 40 * 7665096 * 2
def baseEnd_7665096 : Nat := 3935878510855447510348871

theorem tailTrace_7665096 : CollatzResearch.WordTrace tailWord_7665096 prefixEnd_7665096 3935878510855447510348871 := by
  unfold tailWord_7665096
  simp only [CollatzResearch.WordTrace]
  refine ⟨139784509319336880509799571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186379345759115840679732761 139784509319336880509799571)
  ·
    refine ⟨209676763979005320764699357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139784509319336880509799571 209676763979005320764699357)
    ·
      refine ⟨78628786492126995286762259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209676763979005320764699357 78628786492126995286762259)
      ·
        refine ⟨117943179738190492930143389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78628786492126995286762259 117943179738190492930143389)
        ·
          refine ⟨44228692401821434848803771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117943179738190492930143389 44228692401821434848803771)
          ·
            refine ⟨66343038602732152273205657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44228692401821434848803771 66343038602732152273205657)
            ·
              refine ⟨49757278952049114204904243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66343038602732152273205657 49757278952049114204904243)
              ·
                refine ⟨74635918428073671307356365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49757278952049114204904243 74635918428073671307356365)
                ·
                  refine ⟨27988469410527626740258637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74635918428073671307356365 27988469410527626740258637)
                  ·
                    refine ⟨10495676028947860027596989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27988469410527626740258637 10495676028947860027596989)
                    ·
                      refine ⟨3935878510855447510348871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10495676028947860027596989 3935878510855447510348871)
                      ·
                        rfl

theorem cell23_7665096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_7665096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665096 prefixEnd_7665096 := by exact prefixLift 7665096
  have htrace : WordTrace (prefixWord ++ tailWord_7665096) baseStart_7665096 baseEnd_7665096 := by
    simpa [prefixWord, tailWord_7665096, baseEnd_7665096] using wordTrace_append hprefix tailTrace_7665096
  have hstable : (prefixWord ++ tailWord_7665096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665096).length < 2 ^ (prefixWord ++ tailWord_7665096).sum := by decide
  have hdescent : baseEnd_7665096 < baseStart_7665096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665113 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 4, 1, 3]
def baseStart_7665113 : Nat := 118140960795 + 7665113 * 2 ^ 59
def prefixEnd_7665113 : Nat := 4983230072969 + 3 ^ 40 * 7665113 * 2
def baseEnd_7665113 : Nat := 3935887240026573943836293

theorem tailTrace_7665113 : CollatzResearch.WordTrace tailWord_7665113 prefixEnd_7665113 3935887240026573943836293 := by
  unfold tailWord_7665113
  simp only [CollatzResearch.WordTrace]
  refine ⟨279569638679612172922967993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186379759119741448615311995 279569638679612172922967993)
  ·
    refine ⟨209677229009709129692225995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279569638679612172922967993 209677229009709129692225995)
    ·
      refine ⟨314515843514563694538338993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209677229009709129692225995 314515843514563694538338993)
      ·
        refine ⟨235886882635922770903754245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314515843514563694538338993 235886882635922770903754245)
        ·
          refine ⟨44228790494235519544453921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235886882635922770903754245 44228790494235519544453921)
          ·
            refine ⟨33171592870676639658340441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44228790494235519544453921 33171592870676639658340441)
            ·
              refine ⟨24878694653007479743755331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33171592870676639658340441 24878694653007479743755331)
              ·
                refine ⟨37318041979511219615632997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24878694653007479743755331 37318041979511219615632997)
                ·
                  refine ⟨6997132871158353677931187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37318041979511219615632997 6997132871158353677931187)
                  ·
                    refine ⟨10495699306737530516896781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6997132871158353677931187 10495699306737530516896781)
                    ·
                      refine ⟨3935887240026573943836293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10495699306737530516896781 3935887240026573943836293)
                      ·
                        rfl

theorem cell23_7665113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 1, 3].length) (baseStart_7665113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665113 prefixEnd_7665113 := by exact prefixLift 7665113
  have htrace : WordTrace (prefixWord ++ tailWord_7665113) baseStart_7665113 baseEnd_7665113 := by
    simpa [prefixWord, tailWord_7665113, baseEnd_7665113] using wordTrace_append hprefix tailTrace_7665113
  have hstable : (prefixWord ++ tailWord_7665113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665113).length < 2 ^ (prefixWord ++ tailWord_7665113).sum := by decide
  have hdescent : baseEnd_7665113 < baseStart_7665113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665114 : List Nat := [3, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2]
def baseStart_7665114 : Nat := 118140960795 + 7665114 * 2 ^ 59
def prefixEnd_7665114 : Nat := 4983230072969 + 3 ^ 40 * 7665114 * 2
def baseEnd_7665114 : Nat := 3935887753507228439923789

theorem tailTrace_7665114 : CollatzResearch.WordTrace tailWord_7665114 prefixEnd_7665114 3935887753507228439923789 := by
  unfold tailWord_7665114
  simp only [CollatzResearch.WordTrace]
  refine ⟨69892418788152137523438599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186379783435072366729169597 69892418788152137523438599)
  ·
    refine ⟨104838628182228206285157899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69892418788152137523438599 104838628182228206285157899)
    ·
      refine ⟨157257942273342309427736849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104838628182228206285157899 157257942273342309427736849)
      ·
        refine ⟨117943456705006732070802637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157257942273342309427736849 117943456705006732070802637)
        ·
          refine ⟨44228796264377524526550989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117943456705006732070802637 44228796264377524526550989)
          ·
            refine ⟨16585798599141571697456621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44228796264377524526550989 16585798599141571697456621)
            ·
              refine ⟨6219674474678089386546233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16585798599141571697456621 6219674474678089386546233)
              ·
                refine ⟨4664755856008567039909675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6219674474678089386546233 4664755856008567039909675)
                ·
                  refine ⟨6997133784012850559864513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4664755856008567039909675 6997133784012850559864513)
                  ·
                    refine ⟨5247850338009637919898385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6997133784012850559864513 5247850338009637919898385)
                    ·
                      refine ⟨3935887753507228439923789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5247850338009637919898385 3935887753507228439923789)
                      ·
                        rfl

theorem cell23_7665114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2].length) (baseStart_7665114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665114 prefixEnd_7665114 := by exact prefixLift 7665114
  have htrace : WordTrace (prefixWord ++ tailWord_7665114) baseStart_7665114 baseEnd_7665114 := by
    simpa [prefixWord, tailWord_7665114, baseEnd_7665114] using wordTrace_append hprefix tailTrace_7665114
  have hstable : (prefixWord ++ tailWord_7665114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665114).length < 2 ^ (prefixWord ++ tailWord_7665114).sum := by decide
  have hdescent : baseEnd_7665114 < baseStart_7665114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665129 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 6, 6]
def baseStart_7665129 : Nat := 118140960795 + 7665129 * 2 ^ 59
def prefixEnd_7665129 : Nat := 4983230072969 + 3 ^ 40 * 7665129 * 2
def baseEnd_7665129 : Nat := 1311965151905681960412073

theorem tailTrace_7665129 : CollatzResearch.WordTrace tailWord_7665129 prefixEnd_7665129 1311965151905681960412073 := by
  unfold tailWord_7665129
  simp only [CollatzResearch.WordTrace]
  refine ⟨279570222247554207655550441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186380148165036138437033627 279570222247554207655550441)
  ·
    refine ⟨209677666685665655741662831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279570222247554207655550441 209677666685665655741662831)
    ·
      refine ⟨314516500028498483612494247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209677666685665655741662831 314516500028498483612494247)
      ·
        refine ⟨471774750042747725418741371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314516500028498483612494247 471774750042747725418741371)
        ·
          refine ⟨707662125064121588128112057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471774750042747725418741371 707662125064121588128112057)
          ·
            refine ⟨530746593798091191096084043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 707662125064121588128112057 530746593798091191096084043)
            ·
              refine ⟨796119890697136786644126065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530746593798091191096084043 796119890697136786644126065)
              ·
                refine ⟨597089918022852589983094549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796119890697136786644126065 597089918022852589983094549)
                ·
                  refine ⟨27988589907321215155457557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 597089918022852589983094549 27988589907321215155457557)
                  ·
                    refine ⟨1311965151905681960412073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27988589907321215155457557 1311965151905681960412073)
                    ·
                      rfl

theorem cell23_7665129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 6].length) (baseStart_7665129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665129 prefixEnd_7665129 := by exact prefixLift 7665129
  have htrace : WordTrace (prefixWord ++ tailWord_7665129) baseStart_7665129 baseEnd_7665129 := by
    simpa [prefixWord, tailWord_7665129, baseEnd_7665129] using wordTrace_append hprefix tailTrace_7665129
  have hstable : (prefixWord ++ tailWord_7665129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665129).length < 2 ^ (prefixWord ++ tailWord_7665129).sum := by decide
  have hdescent : baseEnd_7665129 < baseStart_7665129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665165 : List Nat := [1, 7, 1, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_7665165 : Nat := 118140960795 + 7665165 * 2 ^ 59
def prefixEnd_7665165 : Nat := 4983230072969 + 3 ^ 40 * 7665165 * 2
def baseEnd_7665165 : Nat := 3935913941020607740386055

theorem tailTrace_7665165 : CollatzResearch.WordTrace tailWord_7665165 prefixEnd_7665165 3935913941020607740386055 := by
  unfold tailWord_7665165
  simp only [CollatzResearch.WordTrace]
  refine ⟨279571535275423785803860949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186381023516949190535907299 279571535275423785803860949)
  ·
    refine ⟨6552457858017744979777991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 279571535275423785803860949 6552457858017744979777991)
    ·
      refine ⟨9828686787026617469666987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6552457858017744979777991 9828686787026617469666987)
      ·
        refine ⟨14743030180539926204500481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9828686787026617469666987 14743030180539926204500481)
        ·
          refine ⟨11057272635404944653375361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14743030180539926204500481 11057272635404944653375361)
          ·
            refine ⟨8292954476553708490031521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11057272635404944653375361 8292954476553708490031521)
            ·
              refine ⟨6219715857415281367523641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8292954476553708490031521 6219715857415281367523641)
              ·
                refine ⟨4664786893061461025642731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6219715857415281367523641 4664786893061461025642731)
                ·
                  refine ⟨6997180339592191538464097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4664786893061461025642731 6997180339592191538464097)
                  ·
                    refine ⟨5247885254694143653848073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6997180339592191538464097 5247885254694143653848073)
                    ·
                      refine ⟨3935913941020607740386055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5247885254694143653848073 3935913941020607740386055)
                      ·
                        rfl

theorem cell23_7665165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_7665165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665165 prefixEnd_7665165 := by exact prefixLift 7665165
  have htrace : WordTrace (prefixWord ++ tailWord_7665165) baseStart_7665165 baseEnd_7665165 := by
    simpa [prefixWord, tailWord_7665165, baseEnd_7665165] using wordTrace_append hprefix tailTrace_7665165
  have hstable : (prefixWord ++ tailWord_7665165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665165).length < 2 ^ (prefixWord ++ tailWord_7665165).sum := by decide
  have hdescent : baseEnd_7665165 < baseStart_7665165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665238 : List Nat := [5, 2, 2, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_7665238 : Nat := 118140960795 + 7665238 * 2 ^ 59
def prefixEnd_7665238 : Nat := 4983230072969 + 3 ^ 40 * 7665238 * 2
def baseEnd_7665238 : Nat := 3935951425108385954773219

theorem tailTrace_7665238 : CollatzResearch.WordTrace tailWord_7665238 prefixEnd_7665238 3935951425108385954773219 := by
  unfold tailWord_7665238
  simp only [CollatzResearch.WordTrace]
  refine ⟨17473387362759957454454273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186382798536106212847512245 17473387362759957454454273)
  ·
    refine ⟨13105040522069968090840705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17473387362759957454454273 13105040522069968090840705)
    ·
      refine ⟨9828780391552476068130529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13105040522069968090840705 9828780391552476068130529)
      ·
        refine ⟨7371585293664357051097897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9828780391552476068130529 7371585293664357051097897)
        ·
          refine ⟨5528688970248267788323423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7371585293664357051097897 5528688970248267788323423)
          ·
            refine ⟨8293033455372401682485135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5528688970248267788323423 8293033455372401682485135)
            ·
              refine ⟨12439550183058602523727703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8293033455372401682485135 12439550183058602523727703)
              ·
                refine ⟨18659325274587903785591555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12439550183058602523727703 18659325274587903785591555)
                ·
                  refine ⟨27988987911881855678387333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18659325274587903785591555 27988987911881855678387333)
                  ·
                    refine ⟨5247935233477847939697625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27988987911881855678387333 5247935233477847939697625)
                    ·
                      refine ⟨3935951425108385954773219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5247935233477847939697625 3935951425108385954773219)
                      ·
                        rfl

theorem cell23_7665238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_7665238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665238 prefixEnd_7665238 := by exact prefixLift 7665238
  have htrace : WordTrace (prefixWord ++ tailWord_7665238) baseStart_7665238 baseEnd_7665238 := by
    simpa [prefixWord, tailWord_7665238, baseEnd_7665238] using wordTrace_append hprefix tailTrace_7665238
  have hstable : (prefixWord ++ tailWord_7665238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665238).length < 2 ^ (prefixWord ++ tailWord_7665238).sum := by decide
  have hdescent : baseEnd_7665238 < baseStart_7665238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665263 : List Nat := [1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 3]
def baseStart_7665263 : Nat := 118140960795 + 7665263 * 2 ^ 59
def prefixEnd_7665263 : Nat := 4983230072969 + 3 ^ 40 * 7665263 * 2
def baseEnd_7665263 : Nat := 3935964262124748356960603

theorem tailTrace_7665263 : CollatzResearch.WordTrace tailWord_7665263 prefixEnd_7665263 3935964262124748356960603 := by
  unfold tailWord_7665263
  simp only [CollatzResearch.WordTrace]
  refine ⟨279575109629068748540928443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186383406419379165693952295 279575109629068748540928443)
  ·
    refine ⟨419362664443603122811392665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279575109629068748540928443 419362664443603122811392665)
    ·
      refine ⟨314521998332702342108544499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419362664443603122811392665 314521998332702342108544499)
      ·
        refine ⟨471782997499053513162816749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314521998332702342108544499 471782997499053513162816749)
        ·
          refine ⟨176918624062145067436056281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 471782997499053513162816749 176918624062145067436056281)
          ·
            refine ⟨132688968046608800577042211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176918624062145067436056281 132688968046608800577042211)
            ·
              refine ⟨199033452069913200865563317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132688968046608800577042211 199033452069913200865563317)
              ·
                refine ⟨18659386131554362581146561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199033452069913200865563317 18659386131554362581146561)
                ·
                  refine ⟨13994539598665771935859921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18659386131554362581146561 13994539598665771935859921)
                  ·
                    refine ⟨10495904698999328951894941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13994539598665771935859921 10495904698999328951894941)
                    ·
                      refine ⟨3935964262124748356960603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10495904698999328951894941 3935964262124748356960603)
                      ·
                        rfl

theorem cell23_7665263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 3].length) (baseStart_7665263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665263 prefixEnd_7665263 := by exact prefixLift 7665263
  have htrace : WordTrace (prefixWord ++ tailWord_7665263) baseStart_7665263 baseEnd_7665263 := by
    simpa [prefixWord, tailWord_7665263, baseEnd_7665263] using wordTrace_append hprefix tailTrace_7665263
  have hstable : (prefixWord ++ tailWord_7665263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665263).length < 2 ^ (prefixWord ++ tailWord_7665263).sum := by decide
  have hdescent : baseEnd_7665263 < baseStart_7665263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665314 : List Nat := [3, 3, 1, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_7665314 : Nat := 118140960795 + 7665314 * 2 ^ 59
def prefixEnd_7665314 : Nat := 4983230072969 + 3 ^ 40 * 7665314 * 2
def baseEnd_7665314 : Nat := 3935990449638127657422869

theorem tailTrace_7665314 : CollatzResearch.WordTrace tailWord_7665314 prefixEnd_7665314 3935990449638127657422869 := by
  unfold tailWord_7665314
  simp only [CollatzResearch.WordTrace]
  refine ⟨69894242437970996062758749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186384646501255989500689997 69894242437970996062758749)
  ·
    refine ⟨26210340914239123523534531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69894242437970996062758749 26210340914239123523534531)
    ·
      refine ⟨39315511371358685285301797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26210340914239123523534531 39315511371358685285301797)
      ·
        refine ⟨7371658382129753490994087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39315511371358685285301797 7371658382129753490994087)
        ·
          refine ⟨11057487573194630236491131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7371658382129753490994087 11057487573194630236491131)
          ·
            refine ⟨16586231359791945354736697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11057487573194630236491131 16586231359791945354736697)
            ·
              refine ⟨12439673519843959016052523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16586231359791945354736697 12439673519843959016052523)
              ·
                refine ⟨18659510279765938524078785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12439673519843959016052523 18659510279765938524078785)
                ·
                  refine ⟨13994632709824453893059089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18659510279765938524078785 13994632709824453893059089)
                  ·
                    refine ⟨10495974532368340419794317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13994632709824453893059089 10495974532368340419794317)
                    ·
                      refine ⟨3935990449638127657422869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10495974532368340419794317 3935990449638127657422869)
                      ·
                        rfl

theorem cell23_7665314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_7665314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665314 prefixEnd_7665314 := by exact prefixLift 7665314
  have htrace : WordTrace (prefixWord ++ tailWord_7665314) baseStart_7665314 baseEnd_7665314 := by
    simpa [prefixWord, tailWord_7665314, baseEnd_7665314] using wordTrace_append hprefix tailTrace_7665314
  have hstable : (prefixWord ++ tailWord_7665314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665314).length < 2 ^ (prefixWord ++ tailWord_7665314).sum := by decide
  have hdescent : baseEnd_7665314 < baseStart_7665314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665327 : List Nat := [1, 1, 2, 1, 2, 4, 2, 5, 1, 1, 3]
def baseStart_7665327 : Nat := 118140960795 + 7665327 * 2 ^ 59
def prefixEnd_7665327 : Nat := 4983230072969 + 3 ^ 40 * 7665327 * 2
def baseEnd_7665327 : Nat := 3935997124886636106560309

theorem tailTrace_7665327 : CollatzResearch.WordTrace tailWord_7665327 prefixEnd_7665327 3935997124886636106560309 := by
  unfold tailWord_7665327
  simp only [CollatzResearch.WordTrace]
  refine ⟨279577443900836887471258235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186384962600557924980838823 279577443900836887471258235)
  ·
    refine ⟨419366165851255331206887353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279577443900836887471258235 419366165851255331206887353)
    ·
      refine ⟨314524624388441498405165515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419366165851255331206887353 314524624388441498405165515)
      ·
        refine ⟨471786936582662247607748273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314524624388441498405165515 471786936582662247607748273)
        ·
          refine ⟨353840202436996685705811205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471786936582662247607748273 353840202436996685705811205)
          ·
            refine ⟨66345037956936878569839601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 353840202436996685705811205 66345037956936878569839601)
            ·
              refine ⟨49758778467702658927379701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66345037956936878569839601 49758778467702658927379701)
              ·
                refine ⟨4664885481347124274441847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49758778467702658927379701 4664885481347124274441847)
                ·
                  refine ⟨6997328222020686411662771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4664885481347124274441847 6997328222020686411662771)
                  ·
                    refine ⟨10495992333031029617494157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6997328222020686411662771 10495992333031029617494157)
                    ·
                      refine ⟨3935997124886636106560309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10495992333031029617494157 3935997124886636106560309)
                      ·
                        rfl

theorem cell23_7665327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 1, 1, 3].length) (baseStart_7665327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665327 prefixEnd_7665327 := by exact prefixLift 7665327
  have htrace : WordTrace (prefixWord ++ tailWord_7665327) baseStart_7665327 baseEnd_7665327 := by
    simpa [prefixWord, tailWord_7665327, baseEnd_7665327] using wordTrace_append hprefix tailTrace_7665327
  have hstable : (prefixWord ++ tailWord_7665327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665327).length < 2 ^ (prefixWord ++ tailWord_7665327).sum := by decide
  have hdescent : baseEnd_7665327 < baseStart_7665327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665367 : List Nat := [1, 1, 3, 2, 1, 3, 3, 2, 3, 2, 2]
def baseStart_7665367 : Nat := 118140960795 + 7665367 * 2 ^ 59
def prefixEnd_7665367 : Nat := 4983230072969 + 3 ^ 40 * 7665367 * 2
def baseEnd_7665367 : Nat := 3936017664112815950060125

theorem tailTrace_7665367 : CollatzResearch.WordTrace tailWord_7665367 prefixEnd_7665367 3936017664112815950060125 := by
  unfold tailWord_7665367
  simp only [CollatzResearch.WordTrace]
  refine ⟨279578902820691974302714355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186385935213794649535142903 279578902820691974302714355)
  ·
    refine ⟨419368354231037961454071533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279578902820691974302714355 419368354231037961454071533)
    ·
      refine ⟨157263132836639235545276825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419368354231037961454071533 157263132836639235545276825)
      ·
        refine ⟨117947349627479426658957619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157263132836639235545276825 117947349627479426658957619)
        ·
          refine ⟨176921024441219139988436429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117947349627479426658957619 176921024441219139988436429)
          ·
            refine ⟨66345384165457177495663661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176921024441219139988436429 66345384165457177495663661)
            ·
              refine ⟨24879519062046441560873873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66345384165457177495663661 24879519062046441560873873)
              ·
                refine ⟨18659639296534831170655405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24879519062046441560873873 18659639296534831170655405)
                ·
                  refine ⟨6997364736200561688995777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18659639296534831170655405 6997364736200561688995777)
                  ·
                    refine ⟨5248023552150421266746833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6997364736200561688995777 5248023552150421266746833)
                    ·
                      refine ⟨3936017664112815950060125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5248023552150421266746833 3936017664112815950060125)
                      ·
                        rfl

theorem cell23_7665367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_7665367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665367 prefixEnd_7665367 := by exact prefixLift 7665367
  have htrace : WordTrace (prefixWord ++ tailWord_7665367) baseStart_7665367 baseEnd_7665367 := by
    simpa [prefixWord, tailWord_7665367, baseEnd_7665367] using wordTrace_append hprefix tailTrace_7665367
  have hstable : (prefixWord ++ tailWord_7665367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665367).length < 2 ^ (prefixWord ++ tailWord_7665367).sum := by decide
  have hdescent : baseEnd_7665367 < baseStart_7665367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665370 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3]
def baseStart_7665370 : Nat := 118140960795 + 7665370 * 2 ^ 59
def prefixEnd_7665370 : Nat := 4983230072969 + 3 ^ 40 * 7665370 * 2
def baseEnd_7665370 : Nat := 3936019204554779438322611

theorem tailTrace_7665370 : CollatzResearch.WordTrace tailWord_7665370 prefixEnd_7665370 3936019204554779438322611 := by
  unfold tailWord_7665370
  simp only [CollatzResearch.WordTrace]
  refine ⟨69894753059920276453768391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186386008159787403876715709 69894753059920276453768391)
  ·
    refine ⟨104842129589880414680652587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69894753059920276453768391 104842129589880414680652587)
    ·
      refine ⟨157263194384820622020978881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104842129589880414680652587 157263194384820622020978881)
      ·
        refine ⟨117947395788615466515734161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157263194384820622020978881 117947395788615466515734161)
        ·
          refine ⟨88460546841461599886800621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117947395788615466515734161 88460546841461599886800621)
          ·
            refine ⟨33172705065548099957550233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88460546841461599886800621 33172705065548099957550233)
            ·
              refine ⟨24879528799161074968162675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33172705065548099957550233 24879528799161074968162675)
              ·
                refine ⟨37319293198741612452244013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24879528799161074968162675 37319293198741612452244013)
                ·
                  refine ⟨13994734949528104669591505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37319293198741612452244013 13994734949528104669591505)
                  ·
                    refine ⟨10496051212146078502193629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13994734949528104669591505 10496051212146078502193629)
                    ·
                      refine ⟨3936019204554779438322611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10496051212146078502193629 3936019204554779438322611)
                      ·
                        rfl

theorem cell23_7665370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_7665370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665370 prefixEnd_7665370 := by exact prefixLift 7665370
  have htrace : WordTrace (prefixWord ++ tailWord_7665370) baseStart_7665370 baseEnd_7665370 := by
    simpa [prefixWord, tailWord_7665370, baseEnd_7665370] using wordTrace_append hprefix tailTrace_7665370
  have hstable : (prefixWord ++ tailWord_7665370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665370).length < 2 ^ (prefixWord ++ tailWord_7665370).sum := by decide
  have hdescent : baseEnd_7665370 < baseStart_7665370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665384 : List Nat := [2, 1, 4, 1, 3, 3, 2, 1, 1, 1, 4]
def baseStart_7665384 : Nat := 118140960795 + 7665384 * 2 ^ 59
def prefixEnd_7665384 : Nat := 4983230072969 + 3 ^ 40 * 7665384 * 2
def baseEnd_7665384 : Nat := 3936026393283942383547547

theorem tailTrace_7665384 : CollatzResearch.WordTrace tailWord_7665384 prefixEnd_7665384 3936026393283942383547547 := by
  unfold tailWord_7665384
  simp only [CollatzResearch.WordTrace]
  refine ⟨139789761430815193103041603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186386348574420257470722137 139789761430815193103041603)
  ·
    refine ⟨209684642146222789654562405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139789761430815193103041603 209684642146222789654562405)
    ·
      refine ⟨39315870402416773060230451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209684642146222789654562405 39315870402416773060230451)
      ·
        refine ⟨58973805603625159590345677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39315870402416773060230451 58973805603625159590345677)
        ·
          refine ⟨22115177101359434846379629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58973805603625159590345677 22115177101359434846379629)
          ·
            refine ⟨8293191413009788067392361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22115177101359434846379629 8293191413009788067392361)
            ·
              refine ⟨6219893559757341050544271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8293191413009788067392361 6219893559757341050544271)
              ·
                refine ⟨9329840339636011575816407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6219893559757341050544271 9329840339636011575816407)
                ·
                  refine ⟨13994760509454017363724611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9329840339636011575816407 13994760509454017363724611)
                  ·
                    refine ⟨20992140764181026045586917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13994760509454017363724611 20992140764181026045586917)
                    ·
                      refine ⟨3936026393283942383547547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20992140764181026045586917 3936026393283942383547547)
                      ·
                        rfl

theorem cell23_7665384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_7665384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665384 prefixEnd_7665384 := by exact prefixLift 7665384
  have htrace : WordTrace (prefixWord ++ tailWord_7665384) baseStart_7665384 baseEnd_7665384 := by
    simpa [prefixWord, tailWord_7665384, baseEnd_7665384] using wordTrace_append hprefix tailTrace_7665384
  have hstable : (prefixWord ++ tailWord_7665384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665384).length < 2 ^ (prefixWord ++ tailWord_7665384).sum := by decide
  have hdescent : baseEnd_7665384 < baseStart_7665384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665387 : List Nat := [1, 1, 1, 1, 2, 4, 6, 1, 1, 2, 3]
def baseStart_7665387 : Nat := 118140960795 + 7665387 * 2 ^ 59
def prefixEnd_7665387 : Nat := 4983230072969 + 3 ^ 40 * 7665387 * 2
def baseEnd_7665387 : Nat := 3936027933725905871810033

theorem tailTrace_7665387 : CollatzResearch.WordTrace tailWord_7665387 prefixEnd_7665387 3936027933725905871810033 := by
  unfold tailWord_7665387
  simp only [CollatzResearch.WordTrace]
  refine ⟨279579632280619517718442415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186386421520413011812294943 279579632280619517718442415)
  ·
    refine ⟨419369448420929276577663623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279579632280619517718442415 419369448420929276577663623)
    ·
      refine ⟨629054172631393914866495435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419369448420929276577663623 629054172631393914866495435)
      ·
        refine ⟨943581258947090872299743153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629054172631393914866495435 943581258947090872299743153)
        ·
          refine ⟨707685944210318154224807365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 943581258947090872299743153 707685944210318154224807365)
          ·
            refine ⟨132691114539434653917151381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 707685944210318154224807365 132691114539434653917151381)
            ·
              refine ⟨6219895994035999402366471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132691114539434653917151381 6219895994035999402366471)
              ·
                refine ⟨9329843991053999103549707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6219895994035999402366471 9329843991053999103549707)
                ·
                  refine ⟨13994765986580998655324561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9329843991053999103549707 13994765986580998655324561)
                  ·
                    refine ⟨10496074489935748991493421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13994765986580998655324561 10496074489935748991493421)
                    ·
                      refine ⟨3936027933725905871810033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10496074489935748991493421 3936027933725905871810033)
                      ·
                        rfl

theorem cell23_7665387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 1, 2, 3].length) (baseStart_7665387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665387 prefixEnd_7665387 := by exact prefixLift 7665387
  have htrace : WordTrace (prefixWord ++ tailWord_7665387) baseStart_7665387 baseEnd_7665387 := by
    simpa [prefixWord, tailWord_7665387, baseEnd_7665387] using wordTrace_append hprefix tailTrace_7665387
  have hstable : (prefixWord ++ tailWord_7665387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665387).length < 2 ^ (prefixWord ++ tailWord_7665387).sum := by decide
  have hdescent : baseEnd_7665387 < baseStart_7665387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665443 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 5]
def baseStart_7665443 : Nat := 118140960795 + 7665443 * 2 ^ 59
def prefixEnd_7665443 : Nat := 4983230072969 + 3 ^ 40 * 7665443 * 2
def baseEnd_7665443 : Nat := 3936056688642557652709775

theorem tailTrace_7665443 : CollatzResearch.WordTrace tailWord_7665443 prefixEnd_7665443 3936056688642557652709775 := by
  unfold tailWord_7665443
  simp only [CollatzResearch.WordTrace]
  refine ⟨279581674768416639282480983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186387783178944426188320655 279581674768416639282480983)
  ·
    refine ⟨419372512152624958923721475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279581674768416639282480983 419372512152624958923721475)
    ·
      refine ⟨629058768228937438385582213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419372512152624958923721475 629058768228937438385582213)
      ·
        refine ⟨117948519042925769697296665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 629058768228937438385582213 117948519042925769697296665)
        ·
          refine ⟨88461389282194327272972499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117948519042925769697296665 88461389282194327272972499)
          ·
            refine ⟨132692083923291490909458749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88461389282194327272972499 132692083923291490909458749)
            ·
              refine ⟨49759531471234309091047031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132692083923291490909458749 49759531471234309091047031)
              ·
                refine ⟨74639297206851463636570547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49759531471234309091047031 74639297206851463636570547)
                ·
                  refine ⟨111958945810277195454855821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74639297206851463636570547 111958945810277195454855821)
                  ·
                    refine ⟨41984604678853948295570933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111958945810277195454855821 41984604678853948295570933)
                    ·
                      refine ⟨3936056688642557652709775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41984604678853948295570933 3936056688642557652709775)
                      ·
                        rfl

theorem cell23_7665443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_7665443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665443 prefixEnd_7665443 := by exact prefixLift 7665443
  have htrace : WordTrace (prefixWord ++ tailWord_7665443) baseStart_7665443 baseEnd_7665443 := by
    simpa [prefixWord, tailWord_7665443, baseEnd_7665443] using wordTrace_append hprefix tailTrace_7665443
  have hstable : (prefixWord ++ tailWord_7665443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665443).length < 2 ^ (prefixWord ++ tailWord_7665443).sum := by decide
  have hdescent : baseEnd_7665443 < baseStart_7665443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665444 : List Nat := [2, 3, 1, 3, 2, 1, 2, 3, 1, 3, 2]
def baseStart_7665444 : Nat := 118140960795 + 7665444 * 2 ^ 59
def prefixEnd_7665444 : Nat := 4983230072969 + 3 ^ 40 * 7665444 * 2
def baseEnd_7665444 : Nat := 3936057202123212148797271

theorem tailTrace_7665444 : CollatzResearch.WordTrace tailWord_7665444 prefixEnd_7665444 3936057202123212148797271 := by
  unfold tailWord_7665444
  simp only [CollatzResearch.WordTrace]
  refine ⟨139790855620706508226633693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186387807494275344302178257 139790855620706508226633693)
  ·
    refine ⟨52421570857764940584987635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139790855620706508226633693 52421570857764940584987635)
    ·
      refine ⟨78632356286647410877481453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52421570857764940584987635 78632356286647410877481453)
      ·
        refine ⟨29487133607492779079055545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78632356286647410877481453 29487133607492779079055545)
        ·
          refine ⟨22115350205619584309291659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29487133607492779079055545 22115350205619584309291659)
          ·
            refine ⟨33173025308429376463937489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22115350205619584309291659 33173025308429376463937489)
            ·
              refine ⟨24879768981322032347953117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33173025308429376463937489 24879768981322032347953117)
              ·
                refine ⟨9329913367995762130482419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24879768981322032347953117 9329913367995762130482419)
                ·
                  refine ⟨13994870051993643195723629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9329913367995762130482419 13994870051993643195723629)
                  ·
                    refine ⟨5248076269497616198396361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13994870051993643195723629 5248076269497616198396361)
                    ·
                      refine ⟨3936057202123212148797271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5248076269497616198396361 3936057202123212148797271)
                      ·
                        rfl

theorem cell23_7665444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_7665444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665444 prefixEnd_7665444 := by exact prefixLift 7665444
  have htrace : WordTrace (prefixWord ++ tailWord_7665444) baseStart_7665444 baseEnd_7665444 := by
    simpa [prefixWord, tailWord_7665444, baseEnd_7665444] using wordTrace_append hprefix tailTrace_7665444
  have hstable : (prefixWord ++ tailWord_7665444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665444).length < 2 ^ (prefixWord ++ tailWord_7665444).sum := by decide
  have hdescent : baseEnd_7665444 < baseStart_7665444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665463 : List Nat := [1, 1, 3, 1, 2, 1, 2, 5, 7]
def baseStart_7665463 : Nat := 118140960795 + 7665463 * 2 ^ 59
def prefixEnd_7665463 : Nat := 4983230072969 + 3 ^ 40 * 7665463 * 2
def baseEnd_7665463 : Nat := 437340773139516397162187

theorem tailTrace_7665463 : CollatzResearch.WordTrace tailWord_7665463 prefixEnd_7665463 437340773139516397162187 := by
  unfold tailWord_7665463
  simp only [CollatzResearch.WordTrace]
  refine ⟨279582404228344182698209043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186388269485562788465472695 279582404228344182698209043)
  ·
    refine ⟨419373606342516274047313565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279582404228344182698209043 419373606342516274047313565)
    ·
      refine ⟨157265102378443602767742587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419373606342516274047313565 157265102378443602767742587)
      ·
        refine ⟨235897653567665404151613881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157265102378443602767742587 235897653567665404151613881)
        ·
          refine ⟨176923240175749053113710411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235897653567665404151613881 176923240175749053113710411)
          ·
            refine ⟨265384860263623579670565617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176923240175749053113710411 265384860263623579670565617)
            ·
              refine ⟨199038645197717684752924213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265384860263623579670565617 199038645197717684752924213)
              ·
                refine ⟨18659872987286032945586645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199038645197717684752924213 18659872987286032945586645)
                ·
                  refine ⟨437340773139516397162187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18659872987286032945586645 437340773139516397162187)
                  ·
                    rfl

theorem cell23_7665463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 7].length) (baseStart_7665463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665463 prefixEnd_7665463 := by exact prefixLift 7665463
  have htrace : WordTrace (prefixWord ++ tailWord_7665463) baseStart_7665463 baseEnd_7665463 := by
    simpa [prefixWord, tailWord_7665463, baseEnd_7665463] using wordTrace_append hprefix tailTrace_7665463
  have hstable : (prefixWord ++ tailWord_7665463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665463).length < 2 ^ (prefixWord ++ tailWord_7665463).sum := by decide
  have hdescent : baseEnd_7665463 < baseStart_7665463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665478 : List Nat := [6, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_7665478 : Nat := 118140960795 + 7665478 * 2 ^ 59
def prefixEnd_7665478 : Nat := 4983230072969 + 3 ^ 40 * 7665478 * 2
def baseEnd_7665478 : Nat := 3936074660465465015772115

theorem tailTrace_7665478 : CollatzResearch.WordTrace tailWord_7665478 prefixEnd_7665478 3936074660465465015772115 := by
  unfold tailWord_7665478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8736967228852807508125159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 186388634215526560173336725 8736967228852807508125159)
  ·
    refine ⟨13105450843279211262187739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8736967228852807508125159 13105450843279211262187739)
    ·
      refine ⟨19658176264918816893281609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13105450843279211262187739 19658176264918816893281609)
      ·
        refine ⟨14743632198689112669961207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19658176264918816893281609 14743632198689112669961207)
        ·
          refine ⟨22115448298033669004941811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14743632198689112669961207 22115448298033669004941811)
          ·
            refine ⟨33173172447050503507412717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22115448298033669004941811 33173172447050503507412717)
            ·
              refine ⟨12439939667643938815279769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33173172447050503507412717 12439939667643938815279769)
              ·
                refine ⟨9329954750732954111459827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12439939667643938815279769 9329954750732954111459827)
                ·
                  refine ⟨13994932126099431167189741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9329954750732954111459827 13994932126099431167189741)
                  ·
                    refine ⟨5248099547287286687696153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13994932126099431167189741 5248099547287286687696153)
                    ·
                      refine ⟨3936074660465465015772115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5248099547287286687696153 3936074660465465015772115)
                      ·
                        rfl

theorem cell23_7665478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_7665478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665478 prefixEnd_7665478 := by exact prefixLift 7665478
  have htrace : WordTrace (prefixWord ++ tailWord_7665478) baseStart_7665478 baseEnd_7665478 := by
    simpa [prefixWord, tailWord_7665478, baseEnd_7665478] using wordTrace_append hprefix tailTrace_7665478
  have hstable : (prefixWord ++ tailWord_7665478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665478).length < 2 ^ (prefixWord ++ tailWord_7665478).sum := by decide
  have hdescent : baseEnd_7665478 < baseStart_7665478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665517 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 2, 5, 2]
def baseStart_7665517 : Nat := 118140960795 + 7665517 * 2 ^ 59
def prefixEnd_7665517 : Nat := 4983230072969 + 3 ^ 40 * 7665517 * 2
def baseEnd_7665517 : Nat := 3936094686210990363184435

theorem tailTrace_7665517 : CollatzResearch.WordTrace tailWord_7665517 prefixEnd_7665517 3936094686210990363184435 := by
  unfold tailWord_7665517
  simp only [CollatzResearch.WordTrace]
  refine ⟨279584373770148549920674805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186389582513432366613783203 279584373770148549920674805)
  ·
    refine ⟨26211035040951426555063263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279584373770148549920674805 26211035040951426555063263)
    ·
      refine ⟨39316552561427139832594895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26211035040951426555063263 39316552561427139832594895)
      ·
        refine ⟨58974828842140709748892343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39316552561427139832594895 58974828842140709748892343)
        ·
          refine ⟨88462243263211064623338515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58974828842140709748892343 88462243263211064623338515)
          ·
            refine ⟨132693364894816596935007773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88462243263211064623338515 132693364894816596935007773)
            ·
              refine ⟨49760011835556223850627915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132693364894816596935007773 49760011835556223850627915)
              ·
                refine ⟨74640017753334335775941873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49760011835556223850627915 74640017753334335775941873)
                ·
                  refine ⟨55980013315000751831956405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74640017753334335775941873 55980013315000751831956405)
                  ·
                    refine ⟨5248126248281320484245913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55980013315000751831956405 5248126248281320484245913)
                    ·
                      refine ⟨3936094686210990363184435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5248126248281320484245913 3936094686210990363184435)
                      ·
                        rfl

theorem cell23_7665517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_7665517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665517 prefixEnd_7665517 := by exact prefixLift 7665517
  have htrace : WordTrace (prefixWord ++ tailWord_7665517) baseStart_7665517 baseEnd_7665517 := by
    simpa [prefixWord, tailWord_7665517, baseEnd_7665517] using wordTrace_append hprefix tailTrace_7665517
  have hstable : (prefixWord ++ tailWord_7665517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665517).length < 2 ^ (prefixWord ++ tailWord_7665517).sum := by decide
  have hdescent : baseEnd_7665517 < baseStart_7665517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665523 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 2, 8]
def baseStart_7665523 : Nat := 118140960795 + 7665523 * 2 ^ 59
def prefixEnd_7665523 : Nat := 4983230072969 + 3 ^ 40 * 7665523 * 2
def baseEnd_7665523 : Nat := 1312032589031639113236469

theorem tailTrace_7665523 : CollatzResearch.WordTrace tailWord_7665523 prefixEnd_7665523 1312032589031639113236469 := by
  unfold tailWord_7665523
  simp only [CollatzResearch.WordTrace]
  refine ⟨279584592608126812945393223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186389728405417875296928815 279584592608126812945393223)
  ·
    refine ⟨419376888912190219418089835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279584592608126812945393223 419376888912190219418089835)
    ·
      refine ⟨629065333368285329127134753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419376888912190219418089835 629065333368285329127134753)
      ·
        refine ⟨471799000026213996845351065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629065333368285329127134753 471799000026213996845351065)
        ·
          refine ⟨353849250019660497634013299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471799000026213996845351065 353849250019660497634013299)
          ·
            refine ⟨530773875029490746451019949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353849250019660497634013299 530773875029490746451019949)
            ·
              refine ⟨199040203136059029919132481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 530773875029490746451019949 199040203136059029919132481)
              ·
                refine ⟨149280152352044272439349361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199040203136059029919132481 149280152352044272439349361)
                ·
                  refine ⟨111960114264033204329512021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149280152352044272439349361 111960114264033204329512021)
                  ·
                    refine ⟨1312032589031639113236469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111960114264033204329512021 1312032589031639113236469)
                    ·
                      rfl

theorem cell23_7665523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 8].length) (baseStart_7665523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665523 prefixEnd_7665523 := by exact prefixLift 7665523
  have htrace : WordTrace (prefixWord ++ tailWord_7665523) baseStart_7665523 baseEnd_7665523 := by
    simpa [prefixWord, tailWord_7665523, baseEnd_7665523] using wordTrace_append hprefix tailTrace_7665523
  have hstable : (prefixWord ++ tailWord_7665523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665523).length < 2 ^ (prefixWord ++ tailWord_7665523).sum := by decide
  have hdescent : baseEnd_7665523 < baseStart_7665523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665530 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4]
def baseStart_7665530 : Nat := 118140960795 + 7665530 * 2 ^ 59
def prefixEnd_7665530 : Nat := 4983230072969 + 3 ^ 40 * 7665530 * 2
def baseEnd_7665530 : Nat := 3936101361459498812321875

theorem tailTrace_7665530 : CollatzResearch.WordTrace tailWord_7665530 prefixEnd_7665530 3936101361459498812321875 := by
  unfold tailWord_7665530
  simp only [CollatzResearch.WordTrace]
  refine ⟨69896211979775363285224511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186389898612734302093932029 69896211979775363285224511)
  ·
    refine ⟨104844317969663044927836767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69896211979775363285224511 104844317969663044927836767)
    ·
      refine ⟨157266476954494567391755151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104844317969663044927836767 157266476954494567391755151)
      ·
        refine ⟨235899715431741851087632727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157266476954494567391755151 235899715431741851087632727)
        ·
          refine ⟨353849573147612776631449091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235899715431741851087632727 353849573147612776631449091)
          ·
            refine ⟨530774359721419164947173637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353849573147612776631449091 530774359721419164947173637)
            ·
              refine ⟨99520192447766093427595057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 530774359721419164947173637 99520192447766093427595057)
              ·
                refine ⟨74640144335824570070696293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99520192447766093427595057 74640144335824570070696293)
                ·
                  refine ⟨13995027062967106888255555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74640144335824570070696293 13995027062967106888255555)
                  ·
                    refine ⟨20992540594450660332383333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13995027062967106888255555 20992540594450660332383333)
                    ·
                      refine ⟨3936101361459498812321875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20992540594450660332383333 3936101361459498812321875)
                      ·
                        rfl

theorem cell23_7665530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_7665530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665530 prefixEnd_7665530 := by exact prefixLift 7665530
  have htrace : WordTrace (prefixWord ++ tailWord_7665530) baseStart_7665530 baseEnd_7665530 := by
    simpa [prefixWord, tailWord_7665530, baseEnd_7665530] using wordTrace_append hprefix tailTrace_7665530
  have hstable : (prefixWord ++ tailWord_7665530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665530).length < 2 ^ (prefixWord ++ tailWord_7665530).sum := by decide
  have hdescent : baseEnd_7665530 < baseStart_7665530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665544 : List Nat := [2, 1, 3, 3, 3, 2, 1, 1, 2, 5]
def baseStart_7665544 : Nat := 118140960795 + 7665544 * 2 ^ 59
def prefixEnd_7665544 : Nat := 4983230072969 + 3 ^ 40 * 7665544 * 2
def baseEnd_7665544 : Nat := 1312036183396220585848937

theorem tailTrace_7665544 : CollatzResearch.WordTrace tailWord_7665544 prefixEnd_7665544 1312036183396220585848937 := by
  unfold tailWord_7665544
  simp only [CollatzResearch.WordTrace]
  refine ⟨139792679270525366765953843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186390239027367155687938457 139792679270525366765953843)
  ·
    refine ⟨209689018905788050148930765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139792679270525366765953843 209689018905788050148930765)
    ·
      refine ⟨78633382089670518805849037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209689018905788050148930765 78633382089670518805849037)
      ·
        refine ⟨29487518283626444552193389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78633382089670518805849037 29487518283626444552193389)
        ·
          refine ⟨11057819356359916707072521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29487518283626444552193389 11057819356359916707072521)
          ·
            refine ⟨8293364517269937530304391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11057819356359916707072521 8293364517269937530304391)
            ·
              refine ⟨12440046775904906295456587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8293364517269937530304391 12440046775904906295456587)
              ·
                refine ⟨18660070163857359443184881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12440046775904906295456587 18660070163857359443184881)
                ·
                  refine ⟨13995052622893019582388661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18660070163857359443184881 13995052622893019582388661)
                  ·
                    refine ⟨1312036183396220585848937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13995052622893019582388661 1312036183396220585848937)
                    ·
                      rfl

theorem cell23_7665544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_7665544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665544 prefixEnd_7665544 := by exact prefixLift 7665544
  have htrace : WordTrace (prefixWord ++ tailWord_7665544) baseStart_7665544 baseEnd_7665544 := by
    simpa [prefixWord, tailWord_7665544, baseEnd_7665544] using wordTrace_append hprefix tailTrace_7665544
  have hstable : (prefixWord ++ tailWord_7665544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665544).length < 2 ^ (prefixWord ++ tailWord_7665544).sum := by decide
  have hdescent : baseEnd_7665544 < baseStart_7665544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665564 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 2, 4, 2]
def baseStart_7665564 : Nat := 118140960795 + 7665564 * 2 ^ 59
def prefixEnd_7665564 : Nat := 4983230072969 + 3 ^ 40 * 7665564 * 2
def baseEnd_7665564 : Nat := 3936118819801751679296719

theorem tailTrace_7665564 : CollatzResearch.WordTrace tailWord_7665564 prefixEnd_7665564 3936118819801751679296719 := by
  unfold tailWord_7665564
  simp only [CollatzResearch.WordTrace]
  refine ⟨139793044000489138473817873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186390725333985517965090497 139793044000489138473817873)
  ·
    refine ⟨104844783000366853855363405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139793044000489138473817873 104844783000366853855363405)
    ·
      refine ⟨39316793625137570195761277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104844783000366853855363405 39316793625137570195761277)
      ·
        refine ⟨14743797609426588823410479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39316793625137570195761277 14743797609426588823410479)
        ·
          refine ⟨22115696414139883235115719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14743797609426588823410479 22115696414139883235115719)
          ·
            refine ⟨33173544621209824852673579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22115696414139883235115719 33173544621209824852673579)
            ·
              refine ⟨49760316931814737279010369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33173544621209824852673579 49760316931814737279010369)
              ·
                refine ⟨37320237698861052959257777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49760316931814737279010369 37320237698861052959257777)
                ·
                  refine ⟨27990178274145789719443333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37320237698861052959257777 27990178274145789719443333)
                  ·
                    refine ⟨5248158426402335572395625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27990178274145789719443333 5248158426402335572395625)
                    ·
                      refine ⟨3936118819801751679296719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5248158426402335572395625 3936118819801751679296719)
                      ·
                        rfl

theorem cell23_7665564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_7665564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665564 prefixEnd_7665564 := by exact prefixLift 7665564
  have htrace : WordTrace (prefixWord ++ tailWord_7665564) baseStart_7665564 baseEnd_7665564 := by
    simpa [prefixWord, tailWord_7665564, baseEnd_7665564] using wordTrace_append hprefix tailTrace_7665564
  have hstable : (prefixWord ++ tailWord_7665564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665564).length < 2 ^ (prefixWord ++ tailWord_7665564).sum := by decide
  have hdescent : baseEnd_7665564 < baseStart_7665564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665580 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 3]
def baseStart_7665580 : Nat := 118140960795 + 7665580 * 2 ^ 59
def prefixEnd_7665580 : Nat := 4983230072969 + 3 ^ 40 * 7665580 * 2
def baseEnd_7665580 : Nat := 3936127035492223616696645

theorem tailTrace_7665580 : CollatzResearch.WordTrace tailWord_7665580 prefixEnd_7665580 3936127035492223616696645 := by
  unfold tailWord_7665580
  simp only [CollatzResearch.WordTrace]
  refine ⟨139793335784460155840109097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186391114379280207786812129 139793335784460155840109097)
  ·
    refine ⟨104845001838345116880081823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139793335784460155840109097 104845001838345116880081823)
    ·
      refine ⟨157267502757517675320122735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104845001838345116880081823 157267502757517675320122735)
      ·
        refine ⟨235901254136276512980184103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157267502757517675320122735 235901254136276512980184103)
        ·
          refine ⟨353851881204414769470276155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235901254136276512980184103 353851881204414769470276155)
          ·
            refine ⟨530777821806622154205414233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353851881204414769470276155 530777821806622154205414233)
            ·
              refine ⟨398083366354966615654060675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530777821806622154205414233 398083366354966615654060675)
              ·
                refine ⟨597125049532449923481091013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398083366354966615654060675 597125049532449923481091013)
                ·
                  refine ⟨111960946787334360652704565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 597125049532449923481091013 111960946787334360652704565)
                  ·
                    refine ⟨10496338761312596311191053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111960946787334360652704565 10496338761312596311191053)
                    ·
                      refine ⟨3936127035492223616696645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10496338761312596311191053 3936127035492223616696645)
                      ·
                        rfl

theorem cell23_7665580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_7665580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665580 prefixEnd_7665580 := by exact prefixLift 7665580
  have htrace : WordTrace (prefixWord ++ tailWord_7665580) baseStart_7665580 baseEnd_7665580 := by
    simpa [prefixWord, tailWord_7665580, baseEnd_7665580] using wordTrace_append hprefix tailTrace_7665580
  have hstable : (prefixWord ++ tailWord_7665580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665580).length < 2 ^ (prefixWord ++ tailWord_7665580).sum := by decide
  have hdescent : baseEnd_7665580 < baseStart_7665580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665587 : List Nat := [1, 1, 1, 2, 3, 1, 7, 1, 6]
def baseStart_7665587 : Nat := 118140960795 + 7665587 * 2 ^ 59
def prefixEnd_7665587 : Nat := 4983230072969 + 3 ^ 40 * 7665587 * 2
def baseEnd_7665587 : Nat := 437347847761867232145457

theorem tailTrace_7665587 : CollatzResearch.WordTrace tailWord_7665587 prefixEnd_7665587 437347847761867232145457 := by
  unfold tailWord_7665587
  simp only [CollatzResearch.WordTrace]
  refine ⟨279586926879894951875723015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186391284586596634583815343 279586926879894951875723015)
  ·
    refine ⟨419380390319842427813584523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279586926879894951875723015 419380390319842427813584523)
    ·
      refine ⟨629070585479763641720376785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419380390319842427813584523 629070585479763641720376785)
      ·
        refine ⟨471802939109822731290282589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629070585479763641720376785 471802939109822731290282589)
        ·
          refine ⟨176926102166183524233855971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 471802939109822731290282589 176926102166183524233855971)
          ·
            refine ⟨265389153249275286350783957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176926102166183524233855971 265389153249275286350783957)
            ·
              refine ⟨6220058279279889523846499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 265389153249275286350783957 6220058279279889523846499)
              ·
                refine ⟨9330087418919834285769749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6220058279279889523846499 9330087418919834285769749)
                ·
                  refine ⟨437347847761867232145457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9330087418919834285769749 437347847761867232145457)
                  ·
                    rfl

theorem cell23_7665587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 6].length) (baseStart_7665587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665587 prefixEnd_7665587 := by exact prefixLift 7665587
  have htrace : WordTrace (prefixWord ++ tailWord_7665587) baseStart_7665587 baseEnd_7665587 := by
    simpa [prefixWord, tailWord_7665587, baseEnd_7665587] using wordTrace_append hprefix tailTrace_7665587
  have hstable : (prefixWord ++ tailWord_7665587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665587).length < 2 ^ (prefixWord ++ tailWord_7665587).sum := by decide
  have hdescent : baseEnd_7665587 < baseStart_7665587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665624 : List Nat := [2, 1, 2, 2, 2, 2, 3, 2, 2, 3, 2]
def baseStart_7665624 : Nat := 118140960795 + 7665624 * 2 ^ 59
def prefixEnd_7665624 : Nat := 4983230072969 + 3 ^ 40 * 7665624 * 2
def baseEnd_7665624 : Nat := 3936149628641021444546443

theorem tailTrace_7665624 : CollatzResearch.WordTrace tailWord_7665624 prefixEnd_7665624 3936149628641021444546443 := by
  unfold tailWord_7665624
  simp only [CollatzResearch.WordTrace]
  refine ⟨139794138190380453597409963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186392184253840604796546617 139794138190380453597409963)
  ·
    refine ⟨209691207285570680396114945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139794138190380453597409963 209691207285570680396114945)
    ·
      refine ⟨157268405464178010297086209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209691207285570680396114945 157268405464178010297086209)
      ·
        refine ⟨117951304098133507722814657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157268405464178010297086209 117951304098133507722814657)
        ·
          refine ⟨88463478073600130792110993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117951304098133507722814657 88463478073600130792110993)
          ·
            refine ⟨66347608555200098094083245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88463478073600130792110993 66347608555200098094083245)
            ·
              refine ⟨24880353208200036785281217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66347608555200098094083245 24880353208200036785281217)
              ·
                refine ⟨18660264906150027588960913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24880353208200036785281217 18660264906150027588960913)
                ·
                  refine ⟨13995198679612520691720685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18660264906150027588960913 13995198679612520691720685)
                  ·
                    refine ⟨5248199504854695259395257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13995198679612520691720685 5248199504854695259395257)
                    ·
                      refine ⟨3936149628641021444546443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5248199504854695259395257 3936149628641021444546443)
                      ·
                        rfl

theorem cell23_7665624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_7665624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665624 prefixEnd_7665624 := by exact prefixLift 7665624
  have htrace : WordTrace (prefixWord ++ tailWord_7665624) baseStart_7665624 baseEnd_7665624 := by
    simpa [prefixWord, tailWord_7665624, baseEnd_7665624] using wordTrace_append hprefix tailTrace_7665624
  have hstable : (prefixWord ++ tailWord_7665624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665624).length < 2 ^ (prefixWord ++ tailWord_7665624).sum := by decide
  have hdescent : baseEnd_7665624 < baseStart_7665624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665631 : List Nat := [1, 1, 2, 3, 4, 3, 1, 1, 3, 1, 3]
def baseStart_7665631 : Nat := 118140960795 + 7665631 * 2 ^ 59
def prefixEnd_7665631 : Nat := 4983230072969 + 3 ^ 40 * 7665631 * 2
def baseEnd_7665631 : Nat := 3936153223005602917158911

theorem tailTrace_7665631 : CollatzResearch.WordTrace tailWord_7665631 prefixEnd_7665631 3936153223005602917158911 := by
  unfold tailWord_7665631
  simp only [CollatzResearch.WordTrace]
  refine ⟨279588531691735547390324747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186392354461157031593549831 279588531691735547390324747)
  ·
    refine ⟨419382797537603321085487121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279588531691735547390324747 419382797537603321085487121)
    ·
      refine ⟨314537098153202490814115341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419382797537603321085487121 314537098153202490814115341)
      ·
        refine ⟨117951411807450934055293253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314537098153202490814115341 117951411807450934055293253)
        ·
          refine ⟨22115889713897050135367485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117951411807450934055293253 22115889713897050135367485)
          ·
            refine ⟨8293458642711393800762807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22115889713897050135367485 8293458642711393800762807)
            ·
              refine ⟨12440187964067090701144211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8293458642711393800762807 12440187964067090701144211)
              ·
                refine ⟨18660281946100636051716317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12440187964067090701144211 18660281946100636051716317)
                ·
                  refine ⟨6997605729787738519393619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18660281946100636051716317 6997605729787738519393619)
                  ·
                    refine ⟨10496408594681607779090429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6997605729787738519393619 10496408594681607779090429)
                    ·
                      refine ⟨3936153223005602917158911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10496408594681607779090429 3936153223005602917158911)
                      ·
                        rfl

theorem cell23_7665631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_7665631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665631 prefixEnd_7665631 := by exact prefixLift 7665631
  have htrace : WordTrace (prefixWord ++ tailWord_7665631) baseStart_7665631 baseEnd_7665631 := by
    simpa [prefixWord, tailWord_7665631, baseEnd_7665631] using wordTrace_append hprefix tailTrace_7665631
  have hstable : (prefixWord ++ tailWord_7665631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665631).length < 2 ^ (prefixWord ++ tailWord_7665631).sum := by decide
  have hdescent : baseEnd_7665631 < baseStart_7665631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665660 : List Nat := [2, 2, 2, 1, 2, 2, 1, 11]
def baseStart_7665660 : Nat := 118140960795 + 7665660 * 2 ^ 59
def prefixEnd_7665660 : Nat := 4983230072969 + 3 ^ 40 * 7665660 * 2
def baseEnd_7665660 : Nat := 145784004220169751988751

theorem tailTrace_7665660 : CollatzResearch.WordTrace tailWord_7665660 prefixEnd_7665660 145784004220169751988751 := by
  unfold tailWord_7665660
  simp only [CollatzResearch.WordTrace]
  refine ⟨139794794704315242671565217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186393059605753656895420289 139794794704315242671565217)
  ·
    refine ⟨104846096028236432003673913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139794794704315242671565217 104846096028236432003673913)
    ·
      refine ⟨78634572021177324002755435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104846096028236432003673913 78634572021177324002755435)
      ·
        refine ⟨117951858031765986004133153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78634572021177324002755435 117951858031765986004133153)
        ·
          refine ⟨88463893523824489503099865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117951858031765986004133153 88463893523824489503099865)
          ·
            refine ⟨66347920142868367127324899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88463893523824489503099865 66347920142868367127324899)
            ·
              refine ⟨99521880214302550690987349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66347920142868367127324899 99521880214302550690987349)
              ·
                refine ⟨145784004220169751988751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 99521880214302550690987349 145784004220169751988751)
                ·
                  rfl

theorem cell23_7665660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 11].length) (baseStart_7665660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665660 prefixEnd_7665660 := by exact prefixLift 7665660
  have htrace : WordTrace (prefixWord ++ tailWord_7665660) baseStart_7665660 baseEnd_7665660 := by
    simpa [prefixWord, tailWord_7665660, baseEnd_7665660] using wordTrace_append hprefix tailTrace_7665660
  have hstable : (prefixWord ++ tailWord_7665660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665660).length < 2 ^ (prefixWord ++ tailWord_7665660).sum := by decide
  have hdescent : baseEnd_7665660 < baseStart_7665660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665668 : List Nat := [2, 3, 2, 4, 1, 1, 3, 1, 1, 5]
def baseStart_7665668 : Nat := 118140960795 + 7665668 * 2 ^ 59
def prefixEnd_7665668 : Nat := 4983230072969 + 3 ^ 40 * 7665668 * 2
def baseEnd_7665668 : Nat := 1312057407263273090798747

theorem tailTrace_7665668 : CollatzResearch.WordTrace tailWord_7665668 prefixEnd_7665668 1312057407263273090798747 := by
  unfold tailWord_7665668
  simp only [CollatzResearch.WordTrace]
  refine ⟨139794940596300751354710829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186393254128401001806281105 139794940596300751354710829)
  ·
    refine ⟨52423102723612781758016561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139794940596300751354710829 52423102723612781758016561)
    ·
      refine ⟨39317327042709586318512421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52423102723612781758016561 39317327042709586318512421)
      ·
        refine ⟨7371998820508047434721079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39317327042709586318512421 7371998820508047434721079)
        ·
          refine ⟨11057998230762071152081619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7371998820508047434721079 11057998230762071152081619)
          ·
            refine ⟨16586997346143106728122429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11057998230762071152081619 16586997346143106728122429)
            ·
              refine ⟨6220124004803665023045911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16586997346143106728122429 6220124004803665023045911)
              ·
                refine ⟨9330186007205497534568867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6220124004803665023045911 9330186007205497534568867)
                ·
                  refine ⟨13995279010808246301853301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9330186007205497534568867 13995279010808246301853301)
                  ·
                    refine ⟨1312057407263273090798747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13995279010808246301853301 1312057407263273090798747)
                    ·
                      rfl

theorem cell23_7665668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_7665668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665668 prefixEnd_7665668 := by exact prefixLift 7665668
  have htrace : WordTrace (prefixWord ++ tailWord_7665668) baseStart_7665668 baseEnd_7665668 := by
    simpa [prefixWord, tailWord_7665668, baseEnd_7665668] using wordTrace_append hprefix tailTrace_7665668
  have hstable : (prefixWord ++ tailWord_7665668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665668).length < 2 ^ (prefixWord ++ tailWord_7665668).sum := by decide
  have hdescent : baseEnd_7665668 < baseStart_7665668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665671 : List Nat := [1, 1, 4, 3, 1, 3, 3, 1, 1, 1, 4]
def baseStart_7665671 : Nat := 118140960795 + 7665671 * 2 ^ 59
def prefixEnd_7665671 : Nat := 4983230072969 + 3 ^ 40 * 7665671 * 2
def baseEnd_7665671 : Nat := 3936173762231782760658727

theorem tailTrace_7665671 : CollatzResearch.WordTrace tailWord_7665671 prefixEnd_7665671 3936173762231782760658727 := by
  unfold tailWord_7665671
  simp only [CollatzResearch.WordTrace]
  refine ⟨279589990611590634221780867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186393327074393756147853911 279589990611590634221780867)
  ·
    refine ⟨419384985917385951332671301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279589990611590634221780867 419384985917385951332671301)
    ·
      refine ⟨78634684859509865874875869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 419384985917385951332671301 78634684859509865874875869)
      ·
        refine ⟨29488006822316199703078451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78634684859509865874875869 29488006822316199703078451)
        ·
          refine ⟨44232010233474299554617677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29488006822316199703078451 44232010233474299554617677)
          ·
            refine ⟨16587003837552862332981629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44232010233474299554617677 16587003837552862332981629)
            ·
              refine ⟨6220126439082323374868111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16587003837552862332981629 6220126439082323374868111)
              ·
                refine ⟨9330189658623485062302167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6220126439082323374868111 9330189658623485062302167)
                ·
                  refine ⟨13995284487935227593453251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9330189658623485062302167 13995284487935227593453251)
                  ·
                    refine ⟨20992926731902841390179877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13995284487935227593453251 20992926731902841390179877)
                    ·
                      refine ⟨3936173762231782760658727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20992926731902841390179877 3936173762231782760658727)
                      ·
                        rfl

theorem cell23_7665671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_7665671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665671 prefixEnd_7665671 := by exact prefixLift 7665671
  have htrace : WordTrace (prefixWord ++ tailWord_7665671) baseStart_7665671 baseEnd_7665671 := by
    simpa [prefixWord, tailWord_7665671, baseEnd_7665671] using wordTrace_append hprefix tailTrace_7665671
  have hstable : (prefixWord ++ tailWord_7665671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665671).length < 2 ^ (prefixWord ++ tailWord_7665671).sum := by decide
  have hdescent : baseEnd_7665671 < baseStart_7665671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665688 : List Nat := [2, 1, 2, 3, 2, 1, 3, 4, 1, 2, 2]
def baseStart_7665688 : Nat := 118140960795 + 7665688 * 2 ^ 59
def prefixEnd_7665688 : Nat := 4983230072969 + 3 ^ 40 * 7665688 * 2
def baseEnd_7665688 : Nat := 3936182491402909194146149

theorem tailTrace_7665688 : CollatzResearch.WordTrace tailWord_7665688 prefixEnd_7665688 3936182491402909194146149 := by
  unfold tailWord_7665688
  simp only [CollatzResearch.WordTrace]
  refine ⟨139795305326264523062574859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186393740435019364083433145 139795305326264523062574859)
  ·
    refine ⟨209692957989396784593862289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139795305326264523062574859 209692957989396784593862289)
    ·
      refine ⟨157269718492047588445396717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209692957989396784593862289 157269718492047588445396717)
      ·
        refine ⟨58976144434517845667023769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157269718492047588445396717 58976144434517845667023769)
        ·
          refine ⟨44232108325888384250267827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58976144434517845667023769 44232108325888384250267827)
          ·
            refine ⟨66348162488832576375401741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44232108325888384250267827 66348162488832576375401741)
            ·
              refine ⟨24880560933312216140775653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66348162488832576375401741 24880560933312216140775653)
              ·
                refine ⟨4665105174996040526395435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24880560933312216140775653 4665105174996040526395435)
                ·
                  refine ⟨6997657762494060789593153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4665105174996040526395435 6997657762494060789593153)
                  ·
                    refine ⟨5248243321870545592194865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6997657762494060789593153 5248243321870545592194865)
                    ·
                      refine ⟨3936182491402909194146149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5248243321870545592194865 3936182491402909194146149)
                      ·
                        rfl

theorem cell23_7665688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_7665688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665688 prefixEnd_7665688 := by exact prefixLift 7665688
  have htrace : WordTrace (prefixWord ++ tailWord_7665688) baseStart_7665688 baseEnd_7665688 := by
    simpa [prefixWord, tailWord_7665688, baseEnd_7665688] using wordTrace_append hprefix tailTrace_7665688
  have hstable : (prefixWord ++ tailWord_7665688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665688).length < 2 ^ (prefixWord ++ tailWord_7665688).sum := by decide
  have hdescent : baseEnd_7665688 < baseStart_7665688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665767 : List Nat := [1, 1, 5, 1, 1, 2, 1, 4, 7]
def baseStart_7665767 : Nat := 118140960795 + 7665767 * 2 ^ 59
def prefixEnd_7665767 : Nat := 4983230072969 + 3 ^ 40 * 7665767 * 2
def baseEnd_7665767 : Nat := 437358117374957153895365

theorem tailTrace_7665767 : CollatzResearch.WordTrace tailWord_7665767 prefixEnd_7665767 437358117374957153895365 := by
  unfold tailWord_7665767
  simp only [CollatzResearch.WordTrace]
  refine ⟨279593492019242842617275555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186395661346161895078183703 279593492019242842617275555)
  ·
    refine ⟨419390238028864263925913333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279593492019242842617275555 419390238028864263925913333)
    ·
      refine ⟨39317834815206024743054375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 419390238028864263925913333 39317834815206024743054375)
      ·
        refine ⟨58976752222809037114581563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39317834815206024743054375 58976752222809037114581563)
        ·
          refine ⟨88465128334213555671872345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58976752222809037114581563 88465128334213555671872345)
          ·
            refine ⟨66348846250660166753904259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88465128334213555671872345 66348846250660166753904259)
            ·
              refine ⟨99523269375990250130856389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66348846250660166753904259 99523269375990250130856389)
              ·
                refine ⟨18660613007998171899535573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99523269375990250130856389 18660613007998171899535573)
                ·
                  refine ⟨437358117374957153895365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18660613007998171899535573 437358117374957153895365)
                  ·
                    rfl

theorem cell23_7665767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 7].length) (baseStart_7665767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665767 prefixEnd_7665767 := by exact prefixLift 7665767
  have htrace : WordTrace (prefixWord ++ tailWord_7665767) baseStart_7665767 baseEnd_7665767 := by
    simpa [prefixWord, tailWord_7665767, baseEnd_7665767] using wordTrace_append hprefix tailTrace_7665767
  have hstable : (prefixWord ++ tailWord_7665767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665767).length < 2 ^ (prefixWord ++ tailWord_7665767).sum := by decide
  have hdescent : baseEnd_7665767 < baseStart_7665767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665801 : List Nat := [1, 2, 1, 1, 4, 2, 5, 2, 5]
def baseStart_7665801 : Nat := 118140960795 + 7665801 * 2 ^ 59
def prefixEnd_7665801 : Nat := 4983230072969 + 3 ^ 40 * 7665801 * 2
def baseEnd_7665801 : Nat := 437360057190763028003681

theorem tailTrace_7665801 : CollatzResearch.WordTrace tailWord_7665801 prefixEnd_7665801 437360057190763028003681 := by
  unfold tailWord_7665801
  simp only [CollatzResearch.WordTrace]
  refine ⟨279594732101119666424013257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186396488067413110949342171 279594732101119666424013257)
  ·
    refine ⟨209696049075839749818009943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279594732101119666424013257 209696049075839749818009943)
    ·
      refine ⟨314544073613759624727014915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209696049075839749818009943 314544073613759624727014915)
      ·
        refine ⟨471816110420639437090522373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314544073613759624727014915 471816110420639437090522373)
        ·
          refine ⟨88465520703869894454472945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 471816110420639437090522373 88465520703869894454472945)
          ·
            refine ⟨66349140527902420840854709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88465520703869894454472945 66349140527902420840854709)
            ·
              refine ⟨6220231924490851953830129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66349140527902420840854709 6220231924490851953830129)
              ·
                refine ⟨4665173943368138965372597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6220231924490851953830129 4665173943368138965372597)
                ·
                  refine ⟨437360057190763028003681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4665173943368138965372597 437360057190763028003681)
                  ·
                    rfl

theorem cell23_7665801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 5].length) (baseStart_7665801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665801 prefixEnd_7665801 := by exact prefixLift 7665801
  have htrace : WordTrace (prefixWord ++ tailWord_7665801) baseStart_7665801 baseEnd_7665801 := by
    simpa [prefixWord, tailWord_7665801, baseEnd_7665801] using wordTrace_append hprefix tailTrace_7665801
  have hstable : (prefixWord ++ tailWord_7665801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665801).length < 2 ^ (prefixWord ++ tailWord_7665801).sum := by decide
  have hdescent : baseEnd_7665801 < baseStart_7665801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665812 : List Nat := [2, 4, 2, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_7665812 : Nat := 118140960795 + 7665812 * 2 ^ 59
def prefixEnd_7665812 : Nat := 4983230072969 + 3 ^ 40 * 7665812 * 2
def baseEnd_7665812 : Nat := 3936246163004066708995579

theorem tailTrace_7665812 : CollatzResearch.WordTrace tailWord_7665812 prefixEnd_7665812 3936246163004066708995579 := by
  unfold tailWord_7665812
  simp only [CollatzResearch.WordTrace]
  refine ⟨139797566652039907651331845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186396755536053210201775793 139797566652039907651331845)
  ·
    refine ⟨26212043747257482684624721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139797566652039907651331845 26212043747257482684624721)
    ·
      refine ⟨19659032810443112013468541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26212043747257482684624721 19659032810443112013468541)
      ·
        refine ⟨7372137303916167005050703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19659032810443112013468541 7372137303916167005050703)
        ·
          refine ⟨11058205955874250507576055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7372137303916167005050703 11058205955874250507576055)
          ·
            refine ⟨16587308933811375761364083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11058205955874250507576055 16587308933811375761364083)
            ·
              refine ⟨24880963400717063642046125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16587308933811375761364083 24880963400717063642046125)
              ·
                refine ⟨9330361275268898865767297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24880963400717063642046125 9330361275268898865767297)
                ·
                  refine ⟨6997770956451674149325473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9330361275268898865767297 6997770956451674149325473)
                  ·
                    refine ⟨5248328217338755611994105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6997770956451674149325473 5248328217338755611994105)
                    ·
                      refine ⟨3936246163004066708995579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5248328217338755611994105 3936246163004066708995579)
                      ·
                        rfl

theorem cell23_7665812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_7665812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665812 prefixEnd_7665812 := by exact prefixLift 7665812
  have htrace : WordTrace (prefixWord ++ tailWord_7665812) baseStart_7665812 baseEnd_7665812 := by
    simpa [prefixWord, tailWord_7665812, baseEnd_7665812] using wordTrace_append hprefix tailTrace_7665812
  have hstable : (prefixWord ++ tailWord_7665812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665812).length < 2 ^ (prefixWord ++ tailWord_7665812).sum := by decide
  have hdescent : baseEnd_7665812 < baseStart_7665812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665817 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 3, 3, 4]
def baseStart_7665817 : Nat := 118140960795 + 7665817 * 2 ^ 59
def prefixEnd_7665817 : Nat := 4983230072969 + 3 ^ 40 * 7665817 * 2
def baseEnd_7665817 : Nat := 3936248730407339189433055

theorem tailTrace_7665817 : CollatzResearch.WordTrace tailWord_7665817 prefixEnd_7665817 3936248730407339189433055 := by
  unfold tailWord_7665817
  simp only [CollatzResearch.WordTrace]
  refine ⟨279595315669061701156595705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186396877112707800771063803 279595315669061701156595705)
  ·
    refine ⟨209696486751796275867446779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279595315669061701156595705 209696486751796275867446779)
    ·
      refine ⟨314544730127694413801170169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209696486751796275867446779 314544730127694413801170169)
      ·
        refine ⟨235908547595770810350877627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314544730127694413801170169 235908547595770810350877627)
        ·
          refine ⟨353862821393656215526316441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235908547595770810350877627 353862821393656215526316441)
          ·
            refine ⟨265397116045242161644737331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353862821393656215526316441 265397116045242161644737331)
            ·
              refine ⟨398095674067863242467105997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265397116045242161644737331 398095674067863242467105997)
              ·
                refine ⟨149285877775448715925164749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398095674067863242467105997 149285877775448715925164749)
                ·
                  refine ⟨55982204165793268471936781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149285877775448715925164749 55982204165793268471936781)
                  ·
                    refine ⟨20993326562172475676976293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55982204165793268471936781 20993326562172475676976293)
                    ·
                      refine ⟨3936248730407339189433055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20993326562172475676976293 3936248730407339189433055)
                      ·
                        rfl

theorem cell23_7665817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_7665817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665817 prefixEnd_7665817 := by exact prefixLift 7665817
  have htrace : WordTrace (prefixWord ++ tailWord_7665817) baseStart_7665817 baseEnd_7665817 := by
    simpa [prefixWord, tailWord_7665817, baseEnd_7665817] using wordTrace_append hprefix tailTrace_7665817
  have hstable : (prefixWord ++ tailWord_7665817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665817).length < 2 ^ (prefixWord ++ tailWord_7665817).sum := by decide
  have hdescent : baseEnd_7665817 < baseStart_7665817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665858 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_7665858 : Nat := 118140960795 + 7665858 * 2 ^ 59
def prefixEnd_7665858 : Nat := 4983230072969 + 3 ^ 40 * 7665858 * 2
def baseEnd_7665858 : Nat := 3936269783114173529020367

theorem tailTrace_7665858 : CollatzResearch.WordTrace tailWord_7665858 prefixEnd_7665858 3936269783114173529020367 := by
  unfold tailWord_7665858
  simp only [CollatzResearch.WordTrace]
  refine ⟨69899202765478291289709557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186397874041275443439225485 69899202765478291289709557)
  ·
    refine ⟨6553050259263589808410271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69899202765478291289709557 6553050259263589808410271)
    ·
      refine ⟨9829575388895384712615407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6553050259263589808410271 9829575388895384712615407)
      ·
        refine ⟨14744363083343077068923111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9829575388895384712615407 14744363083343077068923111)
        ·
          refine ⟨22116544625014615603384667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14744363083343077068923111 22116544625014615603384667)
          ·
            refine ⟨33174816937521923405077001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22116544625014615603384667 33174816937521923405077001)
            ·
              refine ⟨24881112703141442553807751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33174816937521923405077001 24881112703141442553807751)
              ·
                refine ⟨37321669054712163830711627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24881112703141442553807751 37321669054712163830711627)
                ·
                  refine ⟨55982503582068245746067441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37321669054712163830711627 55982503582068245746067441)
                  ·
                    refine ⟨41986877686551184309550581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55982503582068245746067441 41986877686551184309550581)
                    ·
                      refine ⟨3936269783114173529020367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41986877686551184309550581 3936269783114173529020367)
                      ·
                        rfl

theorem cell23_7665858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_7665858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665858 prefixEnd_7665858 := by exact prefixLift 7665858
  have htrace : WordTrace (prefixWord ++ tailWord_7665858) baseStart_7665858 baseEnd_7665858 := by
    simpa [prefixWord, tailWord_7665858, baseEnd_7665858] using wordTrace_append hprefix tailTrace_7665858
  have hstable : (prefixWord ++ tailWord_7665858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665858).length < 2 ^ (prefixWord ++ tailWord_7665858).sum := by decide
  have hdescent : baseEnd_7665858 < baseStart_7665858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665878 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_7665878 : Nat := 118140960795 + 7665878 * 2 ^ 59
def prefixEnd_7665878 : Nat := 4983230072969 + 3 ^ 40 * 7665878 * 2
def baseEnd_7665878 : Nat := 1312093350909087816923425

theorem tailTrace_7665878 : CollatzResearch.WordTrace tailWord_7665878 prefixEnd_7665878 1312093350909087816923425 := by
  unfold tailWord_7665878
  simp only [CollatzResearch.WordTrace]
  refine ⟨17474846282615044285910393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186398360347893805716377525 17474846282615044285910393)
  ·
    refine ⟨13106134711961283214432795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17474846282615044285910393 13106134711961283214432795)
    ·
      refine ⟨19659202067941924821649193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13106134711961283214432795 19659202067941924821649193)
      ·
        refine ⟨14744401550956443616236895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19659202067941924821649193 14744401550956443616236895)
        ·
          refine ⟨22116602326434665424355343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14744401550956443616236895 22116602326434665424355343)
          ·
            refine ⟨33174903489651998136533015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22116602326434665424355343 33174903489651998136533015)
            ·
              refine ⟨49762355234477997204799523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33174903489651998136533015 49762355234477997204799523)
              ·
                refine ⟨74643532851716995807199285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49762355234477997204799523 74643532851716995807199285)
                ·
                  refine ⟨6997831204848468356924933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74643532851716995807199285 6997831204848468356924933)
                  ·
                    refine ⟨1312093350909087816923425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6997831204848468356924933 1312093350909087816923425)
                    ·
                      rfl

theorem cell23_7665878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_7665878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665878 prefixEnd_7665878 := by exact prefixLift 7665878
  have htrace : WordTrace (prefixWord ++ tailWord_7665878) baseStart_7665878 baseEnd_7665878 := by
    simpa [prefixWord, tailWord_7665878, baseEnd_7665878] using wordTrace_append hprefix tailTrace_7665878
  have hstable : (prefixWord ++ tailWord_7665878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665878).length < 2 ^ (prefixWord ++ tailWord_7665878).sum := by decide
  have hdescent : baseEnd_7665878 < baseStart_7665878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665895 : List Nat := [1, 1, 5, 3, 1, 2, 2, 3, 1, 4]
def baseStart_7665895 : Nat := 118140960795 + 7665895 * 2 ^ 59
def prefixEnd_7665895 : Nat := 4983230072969 + 3 ^ 40 * 7665895 * 2
def baseEnd_7665895 : Nat := 1312096260632796628085899

theorem tailTrace_7665895 : CollatzResearch.WordTrace tailWord_7665895 prefixEnd_7665895 1312096260632796628085899 := by
  unfold tailWord_7665895
  simp only [CollatzResearch.WordTrace]
  refine ⟨279598160562779120477935139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186398773708519413651956759 279598160562779120477935139)
  ·
    refine ⟨419397240844168680716902709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279598160562779120477935139 419397240844168680716902709)
    ·
      refine ⟨39318491329140813817209629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 419397240844168680716902709 39318491329140813817209629)
      ·
        refine ⟨14744434248427805181453611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39318491329140813817209629 14744434248427805181453611)
        ·
          refine ⟨22116651372641707772180417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14744434248427805181453611 22116651372641707772180417)
          ·
            refine ⟨16587488529481280829135313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22116651372641707772180417 16587488529481280829135313)
            ·
              refine ⟨12440616397110960621851485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16587488529481280829135313 12440616397110960621851485)
              ·
                refine ⟨4665231148916610233194307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12440616397110960621851485 4665231148916610233194307)
                ·
                  refine ⟨6997846723374915349791461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4665231148916610233194307 6997846723374915349791461)
                  ·
                    refine ⟨1312096260632796628085899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6997846723374915349791461 1312096260632796628085899)
                    ·
                      rfl

theorem cell23_7665895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_7665895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665895 prefixEnd_7665895 := by exact prefixLift 7665895
  have htrace : WordTrace (prefixWord ++ tailWord_7665895) baseStart_7665895 baseEnd_7665895 := by
    simpa [prefixWord, tailWord_7665895, baseEnd_7665895] using wordTrace_append hprefix tailTrace_7665895
  have hstable : (prefixWord ++ tailWord_7665895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665895).length < 2 ^ (prefixWord ++ tailWord_7665895).sum := by decide
  have hdescent : baseEnd_7665895 < baseStart_7665895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665897 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 7]
def baseStart_7665897 : Nat := 118140960795 + 7665897 * 2 ^ 59
def prefixEnd_7665897 : Nat := 4983230072969 + 3 ^ 40 * 7665897 * 2
def baseEnd_7665897 : Nat := 3936289808859698876432687

theorem tailTrace_7665897 : CollatzResearch.WordTrace tailWord_7665897 prefixEnd_7665897 3936289808859698876432687 := by
  unfold tailWord_7665897
  simp only [CollatzResearch.WordTrace]
  refine ⟨279598233508771874819507945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186398822339181249879671963 279598233508771874819507945)
  ·
    refine ⟨209698675131578906114630959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279598233508771874819507945 209698675131578906114630959)
    ·
      refine ⟨314548012697368359171946439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209698675131578906114630959 314548012697368359171946439)
      ·
        refine ⟨471822019046052538757919659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314548012697368359171946439 471822019046052538757919659)
        ·
          refine ⟨707733028569078808136879489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471822019046052538757919659 707733028569078808136879489)
          ·
            refine ⟨530799771426809106102659617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 707733028569078808136879489 530799771426809106102659617)
            ·
              refine ⟨398099828570106829576994713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530799771426809106102659617 398099828570106829576994713)
              ·
                refine ⟨298574871427580122182746035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398099828570106829576994713 298574871427580122182746035)
                ·
                  refine ⟨447862307141370183274119053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298574871427580122182746035 447862307141370183274119053)
                  ·
                    refine ⟨167948365178013818727794645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 447862307141370183274119053 167948365178013818727794645)
                    ·
                      refine ⟨3936289808859698876432687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167948365178013818727794645 3936289808859698876432687)
                      ·
                        rfl

theorem cell23_7665897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_7665897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665897 prefixEnd_7665897 := by exact prefixLift 7665897
  have htrace : WordTrace (prefixWord ++ tailWord_7665897) baseStart_7665897 baseEnd_7665897 := by
    simpa [prefixWord, tailWord_7665897, baseEnd_7665897] using wordTrace_append hprefix tailTrace_7665897
  have hstable : (prefixWord ++ tailWord_7665897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665897).length < 2 ^ (prefixWord ++ tailWord_7665897).sum := by decide
  have hdescent : baseEnd_7665897 < baseStart_7665897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665941 : List Nat := [1, 3, 2, 1, 2, 1, 3, 4, 1, 1, 4]
def baseStart_7665941 : Nat := 118140960795 + 7665941 * 2 ^ 59
def prefixEnd_7665941 : Nat := 4983230072969 + 3 ^ 40 * 7665941 * 2
def baseEnd_7665941 : Nat := 3936312402008496704282485

theorem tailTrace_7665941 : CollatzResearch.WordTrace tailWord_7665941 prefixEnd_7665941 3936312402008496704282485 := by
  unfold tailWord_7665941
  simp only [CollatzResearch.WordTrace]
  refine ⟨279599838320612470334109677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186399892213741646889406451 279599838320612470334109677)
  ·
    refine ⟨104849939370229676375291129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279599838320612470334109677 104849939370229676375291129)
    ·
      refine ⟨78637454527672257281468347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104849939370229676375291129 78637454527672257281468347)
      ·
        refine ⟨117956181791508385922202521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78637454527672257281468347 117956181791508385922202521)
        ·
          refine ⟨88467136343631289441651891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117956181791508385922202521 88467136343631289441651891)
          ·
            refine ⟨132700704515446934162477837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88467136343631289441651891 132700704515446934162477837)
            ·
              refine ⟨49762764193292600310929189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132700704515446934162477837 49762764193292600310929189)
              ·
                refine ⟨9330518286242362558299223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49762764193292600310929189 9330518286242362558299223)
                ·
                  refine ⟨13995777429363543837448835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9330518286242362558299223 13995777429363543837448835)
                  ·
                    refine ⟨20993666144045315756173253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13995777429363543837448835 20993666144045315756173253)
                    ·
                      refine ⟨3936312402008496704282485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20993666144045315756173253 3936312402008496704282485)
                      ·
                        rfl

theorem cell23_7665941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_7665941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665941 prefixEnd_7665941 := by exact prefixLift 7665941
  have htrace : WordTrace (prefixWord ++ tailWord_7665941) baseStart_7665941 baseEnd_7665941 := by
    simpa [prefixWord, tailWord_7665941, baseEnd_7665941] using wordTrace_append hprefix tailTrace_7665941
  have hstable : (prefixWord ++ tailWord_7665941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665941).length < 2 ^ (prefixWord ++ tailWord_7665941).sum := by decide
  have hdescent : baseEnd_7665941 < baseStart_7665941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665944 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 3, 1, 5]
def baseStart_7665944 : Nat := 118140960795 + 7665944 * 2 ^ 59
def prefixEnd_7665944 : Nat := 4983230072969 + 3 ^ 40 * 7665944 * 2
def baseEnd_7665944 : Nat := 3936313942450460192544971

theorem tailTrace_7665944 : CollatzResearch.WordTrace tailWord_7665944 prefixEnd_7665944 3936313942450460192544971 := by
  unfold tailWord_7665944
  simp only [CollatzResearch.WordTrace]
  refine ⟨139799973869800800923234443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186399965159734401230979257 139799973869800800923234443)
  ·
    refine ⟨209699960804701201384851665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139799973869800800923234443 209699960804701201384851665)
    ·
      refine ⟨157274970603525901038638749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209699960804701201384851665 157274970603525901038638749)
      ·
        refine ⟨58978113976322212889489531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157274970603525901038638749 58978113976322212889489531)
        ·
          refine ⟨88467170964483319334234297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58978113976322212889489531 88467170964483319334234297)
          ·
            refine ⟨66350378223362489500675723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88467170964483319334234297 66350378223362489500675723)
            ·
              refine ⟨99525567335043734251013585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66350378223362489500675723 99525567335043734251013585)
              ·
                refine ⟨74644175501282800688260189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99525567335043734251013585 74644175501282800688260189)
                ·
                  refine ⟨27991565812981050258097571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74644175501282800688260189 27991565812981050258097571)
                  ·
                    refine ⟨41987348719471575387146357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27991565812981050258097571 41987348719471575387146357)
                    ·
                      refine ⟨3936313942450460192544971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41987348719471575387146357 3936313942450460192544971)
                      ·
                        rfl

theorem cell23_7665944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_7665944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665944 prefixEnd_7665944 := by exact prefixLift 7665944
  have htrace : WordTrace (prefixWord ++ tailWord_7665944) baseStart_7665944 baseEnd_7665944 := by
    simpa [prefixWord, tailWord_7665944, baseEnd_7665944] using wordTrace_append hprefix tailTrace_7665944
  have hstable : (prefixWord ++ tailWord_7665944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665944).length < 2 ^ (prefixWord ++ tailWord_7665944).sum := by decide
  have hdescent : baseEnd_7665944 < baseStart_7665944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665951 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 4, 4]
def baseStart_7665951 : Nat := 118140960795 + 7665951 * 2 ^ 59
def prefixEnd_7665951 : Nat := 4983230072969 + 3 ^ 40 * 7665951 * 2
def baseEnd_7665951 : Nat := 1312105845605013888385813

theorem tailTrace_7665951 : CollatzResearch.WordTrace tailWord_7665951 prefixEnd_7665951 1312105845605013888385813 := by
  unfold tailWord_7665951
  simp only [CollatzResearch.WordTrace]
  refine ⟨279600203050576242041973707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186400135367050828027982471 279600203050576242041973707)
  ·
    refine ⟨419400304575864363062960561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279600203050576242041973707 419400304575864363062960561)
    ·
      refine ⟨314550228431898272297220421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419400304575864363062960561 314550228431898272297220421)
      ·
        refine ⟨58978167830980926055728829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314550228431898272297220421 58978167830980926055728829)
        ·
          refine ⟨22116812936617847270898311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58978167830980926055728829 22116812936617847270898311)
          ·
            refine ⟨33175219404926770906347467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22116812936617847270898311 33175219404926770906347467)
            ·
              refine ⟨49762829107390156359521201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33175219404926770906347467 49762829107390156359521201)
              ·
                refine ⟨37322121830542617269640901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49762829107390156359521201 37322121830542617269640901)
                ·
                  refine ⟨6997897843226740738057669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37322121830542617269640901 6997897843226740738057669)
                  ·
                    refine ⟨1312105845605013888385813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6997897843226740738057669 1312105845605013888385813)
                    ·
                      rfl

theorem cell23_7665951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 4].length) (baseStart_7665951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665951 prefixEnd_7665951 := by exact prefixLift 7665951
  have htrace : WordTrace (prefixWord ++ tailWord_7665951) baseStart_7665951 baseEnd_7665951 := by
    simpa [prefixWord, tailWord_7665951, baseEnd_7665951] using wordTrace_append hprefix tailTrace_7665951
  have hstable : (prefixWord ++ tailWord_7665951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665951).length < 2 ^ (prefixWord ++ tailWord_7665951).sum := by decide
  have hdescent : baseEnd_7665951 < baseStart_7665951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665952 : List Nat := [2, 1, 1, 5, 2, 3, 1, 3, 1, 1, 3]
def baseStart_7665952 : Nat := 118140960795 + 7665952 * 2 ^ 59
def prefixEnd_7665952 : Nat := 4983230072969 + 3 ^ 40 * 7665952 * 2
def baseEnd_7665952 : Nat := 3936318050295696161244935

theorem tailTrace_7665952 : CollatzResearch.WordTrace tailWord_7665952 prefixEnd_7665952 3936318050295696161244935 := by
  unfold tailWord_7665952
  simp only [CollatzResearch.WordTrace]
  refine ⟨139800119761786309606380055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186400159682381746141840073 139800119761786309606380055)
  ·
    refine ⟨209700179642679464409570083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139800119761786309606380055 209700179642679464409570083)
    ·
      refine ⟨314550269464019196614355125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209700179642679464409570083 314550269464019196614355125)
      ·
        refine ⟨29489087762251799682595793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 314550269464019196614355125 29489087762251799682595793)
        ·
          refine ⟨22116815821688849761946845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29489087762251799682595793 22116815821688849761946845)
          ·
            refine ⟨8293805933133318660730067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22116815821688849761946845 8293805933133318660730067)
            ·
              refine ⟨12440708899699977991095101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8293805933133318660730067 12440708899699977991095101)
              ·
                refine ⟨4665265837387491746660663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12440708899699977991095101 4665265837387491746660663)
                ·
                  refine ⟨6997898756081237619990995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4665265837387491746660663 6997898756081237619990995)
                  ·
                    refine ⟨10496848134121856429986493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6997898756081237619990995 10496848134121856429986493)
                    ·
                      refine ⟨3936318050295696161244935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10496848134121856429986493 3936318050295696161244935)
                      ·
                        rfl

theorem cell23_7665952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_7665952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665952 prefixEnd_7665952 := by exact prefixLift 7665952
  have htrace : WordTrace (prefixWord ++ tailWord_7665952) baseStart_7665952 baseEnd_7665952 := by
    simpa [prefixWord, tailWord_7665952, baseEnd_7665952] using wordTrace_append hprefix tailTrace_7665952
  have hstable : (prefixWord ++ tailWord_7665952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665952).length < 2 ^ (prefixWord ++ tailWord_7665952).sum := by decide
  have hdescent : baseEnd_7665952 < baseStart_7665952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665975 : List Nat := [1, 1, 3, 1, 2, 1, 1, 8, 1, 2, 2]
def baseStart_7665975 : Nat := 118140960795 + 7665975 * 2 ^ 59
def prefixEnd_7665975 : Nat := 4983230072969 + 3 ^ 40 * 7665975 * 2
def baseEnd_7665975 : Nat := 3936329860350749571257329

theorem tailTrace_7665975 : CollatzResearch.WordTrace tailWord_7665975 prefixEnd_7665975 3936329860350749571257329 := by
  unfold tailWord_7665975
  simp only [CollatzResearch.WordTrace]
  refine ⟨279601078402489294140847379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186400718934992862760564919 279601078402489294140847379)
  ·
    refine ⟨419401617603733941211271069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279601078402489294140847379 419401617603733941211271069)
    ·
      refine ⟨157275606601400227954226651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419401617603733941211271069 157275606601400227954226651)
      ·
        refine ⟨235913409902100341931339977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157275606601400227954226651 235913409902100341931339977)
        ·
          refine ⟨176935057426575256448504983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235913409902100341931339977 176935057426575256448504983)
          ·
            refine ⟨265402586139862884672757475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176935057426575256448504983 265402586139862884672757475)
            ·
              refine ⟨398103879209794327009136213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265402586139862884672757475 398103879209794327009136213)
              ·
                refine ⟨4665279834489777269638315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 398103879209794327009136213 4665279834489777269638315)
                ·
                  refine ⟨6997919751734665904457473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4665279834489777269638315 6997919751734665904457473)
                  ·
                    refine ⟨5248439813800999428343105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6997919751734665904457473 5248439813800999428343105)
                    ·
                      refine ⟨3936329860350749571257329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5248439813800999428343105 3936329860350749571257329)
                      ·
                        rfl

theorem cell23_7665975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 1, 2, 2].length) (baseStart_7665975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665975 prefixEnd_7665975 := by exact prefixLift 7665975
  have htrace : WordTrace (prefixWord ++ tailWord_7665975) baseStart_7665975 baseEnd_7665975 := by
    simpa [prefixWord, tailWord_7665975, baseEnd_7665975] using wordTrace_append hprefix tailTrace_7665975
  have hstable : (prefixWord ++ tailWord_7665975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665975).length < 2 ^ (prefixWord ++ tailWord_7665975).sum := by decide
  have hdescent : baseEnd_7665975 < baseStart_7665975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665985 : List Nat := [1, 2, 5, 2, 2, 1, 1, 3, 2, 4]
def baseStart_7665985 : Nat := 118140960795 + 7665985 * 2 ^ 59
def prefixEnd_7665985 : Nat := 4983230072969 + 3 ^ 40 * 7665985 * 2
def baseEnd_7665985 : Nat := 1312111665052431510710761

theorem tailTrace_7665985 : CollatzResearch.WordTrace tailWord_7665985 prefixEnd_7665985 1312111665052431510710761 := by
  unfold tailWord_7665985
  simp only [CollatzResearch.WordTrace]
  refine ⟨279601443132453065848711409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186400962088302043899140939 279601443132453065848711409)
  ·
    refine ⟨209701082349339799386533557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279601443132453065848711409 209701082349339799386533557)
    ·
      refine ⟨19659476470250606192487521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209701082349339799386533557 19659476470250606192487521)
      ·
        refine ⟨14744607352687954644365641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19659476470250606192487521 14744607352687954644365641)
        ·
          refine ⟨11058455514515965983274231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14744607352687954644365641 11058455514515965983274231)
          ·
            refine ⟨16587683271773948974911347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11058455514515965983274231 16587683271773948974911347)
            ·
              refine ⟨24881524907660923462367021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16587683271773948974911347 24881524907660923462367021)
              ·
                refine ⟨9330571840372846298387633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24881524907660923462367021 9330571840372846298387633)
                ·
                  refine ⟨6997928880279634723790725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9330571840372846298387633 6997928880279634723790725)
                  ·
                    refine ⟨1312111665052431510710761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6997928880279634723790725 1312111665052431510710761)
                    ·
                      rfl

theorem cell23_7665985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_7665985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665985 prefixEnd_7665985 := by exact prefixLift 7665985
  have htrace : WordTrace (prefixWord ++ tailWord_7665985) baseStart_7665985 baseEnd_7665985 := by
    simpa [prefixWord, tailWord_7665985, baseEnd_7665985] using wordTrace_append hprefix tailTrace_7665985
  have hstable : (prefixWord ++ tailWord_7665985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665985).length < 2 ^ (prefixWord ++ tailWord_7665985).sum := by decide
  have hdescent : baseEnd_7665985 < baseStart_7665985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7665991 : List Nat := [1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 3]
def baseStart_7665991 : Nat := 118140960795 + 7665991 * 2 ^ 59
def prefixEnd_7665991 : Nat := 4983230072969 + 3 ^ 40 * 7665991 * 2
def baseEnd_7665991 : Nat := 3936338076041221508657255

theorem tailTrace_7665991 : CollatzResearch.WordTrace tailWord_7665991 prefixEnd_7665991 3936338076041221508657255 := by
  unfold tailWord_7665991
  simp only [CollatzResearch.WordTrace]
  refine ⟨279601661970431328873429827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186401107980287552582286551 279601661970431328873429827)
  ·
    refine ⟨419402492955646993310144741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279601661970431328873429827 419402492955646993310144741)
    ·
      refine ⟨78637967429183811245652139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 419402492955646993310144741 78637967429183811245652139)
      ·
        refine ⟨117956951143775716868478209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78637967429183811245652139 117956951143775716868478209)
        ·
          refine ⟨88467713357831787651358657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117956951143775716868478209 88467713357831787651358657)
          ·
            refine ⟨66350785018373840738518993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88467713357831787651358657 66350785018373840738518993)
            ·
              refine ⟨49763088763780380553889245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66350785018373840738518993 49763088763780380553889245)
              ·
                refine ⟨18661158286417642707708467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49763088763780380553889245 18661158286417642707708467)
                ·
                  refine ⟨27991737429626464061562701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18661158286417642707708467 27991737429626464061562701)
                  ·
                    refine ⟨10496901536109924023086013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27991737429626464061562701 10496901536109924023086013)
                    ·
                      refine ⟨3936338076041221508657255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10496901536109924023086013 3936338076041221508657255)
                      ·
                        rfl

theorem cell23_7665991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_7665991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7665991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7665991 prefixEnd_7665991 := by exact prefixLift 7665991
  have htrace : WordTrace (prefixWord ++ tailWord_7665991) baseStart_7665991 baseEnd_7665991 := by
    simpa [prefixWord, tailWord_7665991, baseEnd_7665991] using wordTrace_append hprefix tailTrace_7665991
  have hstable : (prefixWord ++ tailWord_7665991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7665991).length < 2 ^ (prefixWord ++ tailWord_7665991).sum := by decide
  have hdescent : baseEnd_7665991 < baseStart_7665991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7665991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666012 : List Nat := [2, 2, 4, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_7666012 : Nat := 118140960795 + 7666012 * 2 ^ 59
def prefixEnd_7666012 : Nat := 4983230072969 + 3 ^ 40 * 7666012 * 2
def baseEnd_7666012 : Nat := 3936348859134965926494659

theorem tailTrace_7666012 : CollatzResearch.WordTrace tailWord_7666012 prefixEnd_7666012 3936348859134965926494659 := by
  unfold tailWord_7666012
  simp only [CollatzResearch.WordTrace]
  refine ⟨139801213951677624729972145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186401618602236832973296193 139801213951677624729972145)
  ·
    refine ⟨104850910463758218547479109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139801213951677624729972145 104850910463758218547479109)
    ·
      refine ⟨19659545711954665977652333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104850910463758218547479109 19659545711954665977652333)
      ·
        refine ⟨7372329641982999741619625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19659545711954665977652333 7372329641982999741619625)
        ·
          refine ⟨5529247231487249806214719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7372329641982999741619625 5529247231487249806214719)
          ·
            refine ⟨8293870847230874709322079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5529247231487249806214719 8293870847230874709322079)
            ·
              refine ⟨12440806270846312063983119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8293870847230874709322079 12440806270846312063983119)
              ·
                refine ⟨18661209406269468095974679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12440806270846312063983119 18661209406269468095974679)
                ·
                  refine ⟨27991814109404202143962019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18661209406269468095974679 27991814109404202143962019)
                  ·
                    refine ⟨41987721164106303215943029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27991814109404202143962019 41987721164106303215943029)
                    ·
                      refine ⟨3936348859134965926494659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41987721164106303215943029 3936348859134965926494659)
                      ·
                        rfl

theorem cell23_7666012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_7666012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666012 prefixEnd_7666012 := by exact prefixLift 7666012
  have htrace : WordTrace (prefixWord ++ tailWord_7666012) baseStart_7666012 baseEnd_7666012 := by
    simpa [prefixWord, tailWord_7666012, baseEnd_7666012] using wordTrace_append hprefix tailTrace_7666012
  have hstable : (prefixWord ++ tailWord_7666012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666012).length < 2 ^ (prefixWord ++ tailWord_7666012).sum := by decide
  have hdescent : baseEnd_7666012 < baseStart_7666012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666026 : List Nat := [3, 1, 3, 3, 1, 3, 2, 2, 1, 2, 2]
def baseStart_7666026 : Nat := 118140960795 + 7666026 * 2 ^ 59
def prefixEnd_7666026 : Nat := 4983230072969 + 3 ^ 40 * 7666026 * 2
def baseEnd_7666026 : Nat := 3936356047864128871719595

theorem tailTrace_7666026 : CollatzResearch.WordTrace tailWord_7666026 prefixEnd_7666026 3936356047864128871719595 := by
  unfold tailWord_7666026
  simp only [CollatzResearch.WordTrace]
  refine ⟨69900734631326132462738483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186401959016869686567302621 69900734631326132462738483)
  ·
    refine ⟨104851101946989198694107725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69900734631326132462738483 104851101946989198694107725)
    ·
      refine ⟨39319163230120949510290397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104851101946989198694107725 39319163230120949510290397)
      ·
        refine ⟨14744686211295356066358899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39319163230120949510290397 14744686211295356066358899)
        ·
          refine ⟨22117029316943034099538349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14744686211295356066358899 22117029316943034099538349)
          ·
            refine ⟨8293885993853637787326881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22117029316943034099538349 8293885993853637787326881)
            ·
              refine ⟨6220414495390228340495161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8293885993853637787326881 6220414495390228340495161)
              ·
                refine ⟨4665310871542671255371371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6220414495390228340495161 4665310871542671255371371)
                ·
                  refine ⟨6997966307314006883057057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4665310871542671255371371 6997966307314006883057057)
                  ·
                    refine ⟨5248474730485505162292793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6997966307314006883057057 5248474730485505162292793)
                    ·
                      refine ⟨3936356047864128871719595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5248474730485505162292793 3936356047864128871719595)
                      ·
                        rfl

theorem cell23_7666026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_7666026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666026 prefixEnd_7666026 := by exact prefixLift 7666026
  have htrace : WordTrace (prefixWord ++ tailWord_7666026) baseStart_7666026 baseEnd_7666026 := by
    simpa [prefixWord, tailWord_7666026, baseEnd_7666026] using wordTrace_append hprefix tailTrace_7666026
  have hstable : (prefixWord ++ tailWord_7666026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666026).length < 2 ^ (prefixWord ++ tailWord_7666026).sum := by decide
  have hdescent : baseEnd_7666026 < baseStart_7666026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666048 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 8, 2, 2]
def baseStart_7666048 : Nat := 118140960795 + 7666048 * 2 ^ 59
def prefixEnd_7666048 : Nat := 4983230072969 + 3 ^ 40 * 7666048 * 2
def baseEnd_7666048 : Nat := 3936367344438527785644493

theorem tailTrace_7666048 : CollatzResearch.WordTrace tailWord_7666048 prefixEnd_7666048 3936367344438527785644493 := by
  unfold tailWord_7666048
  simp only [CollatzResearch.WordTrace]
  refine ⟨139801870465612413804127399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186402493954149885072169865 139801870465612413804127399)
  ·
    refine ⟨209702805698418620706191099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139801870465612413804127399 209702805698418620706191099)
    ·
      refine ⟨314554208547627931059286649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209702805698418620706191099 314554208547627931059286649)
      ·
        refine ⟨235915656410720948294464987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314554208547627931059286649 235915656410720948294464987)
        ·
          refine ⟨353873484616081422441697481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235915656410720948294464987 353873484616081422441697481)
          ·
            refine ⟨265405113462061066831273111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353873484616081422441697481 265405113462061066831273111)
            ·
              refine ⟨398107670193091600246909667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265405113462061066831273111 398107670193091600246909667)
              ·
                refine ⟨597161505289637400370364501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398107670193091600246909667 597161505289637400370364501)
                ·
                  refine ⟨6997986390112938285590209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 597161505289637400370364501 6997986390112938285590209)
                  ·
                    refine ⟨5248489792584703714192657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6997986390112938285590209 5248489792584703714192657)
                    ·
                      refine ⟨3936367344438527785644493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5248489792584703714192657 3936367344438527785644493)
                      ·
                        rfl

theorem cell23_7666048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 8, 2, 2].length) (baseStart_7666048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666048 prefixEnd_7666048 := by exact prefixLift 7666048
  have htrace : WordTrace (prefixWord ++ tailWord_7666048) baseStart_7666048 baseEnd_7666048 := by
    simpa [prefixWord, tailWord_7666048, baseEnd_7666048] using wordTrace_append hprefix tailTrace_7666048
  have hstable : (prefixWord ++ tailWord_7666048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666048).length < 2 ^ (prefixWord ++ tailWord_7666048).sum := by decide
  have hdescent : baseEnd_7666048 < baseStart_7666048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666088 : List Nat := [2, 1, 6, 1, 1, 1, 1, 3, 7]
def baseStart_7666088 : Nat := 118140960795 + 7666088 * 2 ^ 59
def prefixEnd_7666088 : Nat := 4983230072969 + 3 ^ 40 * 7666088 * 2
def baseEnd_7666088 : Nat := 437376431518300847682701

theorem tailTrace_7666088 : CollatzResearch.WordTrace tailWord_7666088 prefixEnd_7666088 437376431518300847682701 := by
  unfold tailWord_7666088
  simp only [CollatzResearch.WordTrace]
  refine ⟨139802599925539957219855459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186403466567386609626473945 139802599925539957219855459)
  ·
    refine ⟨209703899888309935829783189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139802599925539957219855459 209703899888309935829783189)
    ·
      refine ⟨9829870307264528242021087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 209703899888309935829783189 9829870307264528242021087)
      ·
        refine ⟨14744805460896792363031631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9829870307264528242021087 14744805460896792363031631)
        ·
          refine ⟨22117208191345188544547447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14744805460896792363031631 22117208191345188544547447)
          ·
            refine ⟨33175812287017782816821171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22117208191345188544547447 33175812287017782816821171)
            ·
              refine ⟨49763718430526674225231757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33175812287017782816821171 49763718430526674225231757)
              ·
                refine ⟨18661394411447502834461909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49763718430526674225231757 18661394411447502834461909)
                ·
                  refine ⟨437376431518300847682701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18661394411447502834461909 437376431518300847682701)
                  ·
                    rfl

theorem cell23_7666088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 7].length) (baseStart_7666088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666088 prefixEnd_7666088 := by exact prefixLift 7666088
  have htrace : WordTrace (prefixWord ++ tailWord_7666088) baseStart_7666088 baseEnd_7666088 := by
    simpa [prefixWord, tailWord_7666088, baseEnd_7666088] using wordTrace_append hprefix tailTrace_7666088
  have hstable : (prefixWord ++ tailWord_7666088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666088).length < 2 ^ (prefixWord ++ tailWord_7666088).sum := by decide
  have hdescent : baseEnd_7666088 < baseStart_7666088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666121 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 1, 3, 4]
def baseStart_7666121 : Nat := 118140960795 + 7666121 * 2 ^ 59
def prefixEnd_7666121 : Nat := 4983230072969 + 3 ^ 40 * 7666121 * 2
def baseEnd_7666121 : Nat := 3936404828526306000031657

theorem tailTrace_7666121 : CollatzResearch.WordTrace tailWord_7666121 prefixEnd_7666121 3936404828526306000031657 := by
  unfold tailWord_7666121
  simp only [CollatzResearch.WordTrace]
  refine ⟨279606403459960361075662217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186404268973306907383774811 279606403459960361075662217)
  ·
    refine ⟨209704802594970270806746663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279606403459960361075662217 209704802594970270806746663)
    ·
      refine ⟨314557203892455406210119995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209704802594970270806746663 314557203892455406210119995)
      ·
        refine ⟨471835805838683109315179993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314557203892455406210119995 471835805838683109315179993)
        ·
          refine ⟨353876854379012331986384995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471835805838683109315179993 353876854379012331986384995)
          ·
            refine ⟨530815281568518497979577493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353876854379012331986384995 530815281568518497979577493)
            ·
              refine ⟨24881966323524304592792695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 530815281568518497979577493 24881966323524304592792695)
              ·
                refine ⟨37322949485286456889189043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24881966323524304592792695 37322949485286456889189043)
                ·
                  refine ⟨55984424227929685333783565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37322949485286456889189043 55984424227929685333783565)
                  ·
                    refine ⟨20994159085473632000168837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55984424227929685333783565 20994159085473632000168837)
                    ·
                      refine ⟨3936404828526306000031657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20994159085473632000168837 3936404828526306000031657)
                      ·
                        rfl

theorem cell23_7666121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_7666121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666121 prefixEnd_7666121 := by exact prefixLift 7666121
  have htrace : WordTrace (prefixWord ++ tailWord_7666121) baseStart_7666121 baseEnd_7666121 := by
    simpa [prefixWord, tailWord_7666121, baseEnd_7666121] using wordTrace_append hprefix tailTrace_7666121
  have hstable : (prefixWord ++ tailWord_7666121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666121).length < 2 ^ (prefixWord ++ tailWord_7666121).sum := by decide
  have hdescent : baseEnd_7666121 < baseStart_7666121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666138 : List Nat := [3, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4]
def baseStart_7666138 : Nat := 118140960795 + 7666138 * 2 ^ 59
def prefixEnd_7666138 : Nat := 4983230072969 + 3 ^ 40 * 7666138 * 2
def baseEnd_7666138 : Nat := 3936413557697432433519079

theorem tailTrace_7666138 : CollatzResearch.WordTrace tailWord_7666138 prefixEnd_7666138 3936413557697432433519079 := by
  unfold tailWord_7666138
  simp only [CollatzResearch.WordTrace]
  refine ⟨69901755875224693244757767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186404682333932515319354045 69901755875224693244757767)
  ·
    refine ⟨104852633812837039867136651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69901755875224693244757767 104852633812837039867136651)
    ·
      refine ⟨157278950719255559800704977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104852633812837039867136651 157278950719255559800704977)
      ·
        refine ⟨117959213039441669850528733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157278950719255559800704977 117959213039441669850528733)
        ·
          refine ⟨44234704889790626193948275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117959213039441669850528733 44234704889790626193948275)
          ·
            refine ⟨66352057334685939290922413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44234704889790626193948275 66352057334685939290922413)
            ·
              refine ⟨24882021500507227234095905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66352057334685939290922413 24882021500507227234095905)
              ·
                refine ⟨18661516125380420425571929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24882021500507227234095905 18661516125380420425571929)
                ·
                  refine ⟨13996137094035315319178947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18661516125380420425571929 13996137094035315319178947)
                  ·
                    refine ⟨20994205641052972978768421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13996137094035315319178947 20994205641052972978768421)
                    ·
                      refine ⟨3936413557697432433519079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20994205641052972978768421 3936413557697432433519079)
                      ·
                        rfl

theorem cell23_7666138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_7666138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666138 prefixEnd_7666138 := by exact prefixLift 7666138
  have htrace : WordTrace (prefixWord ++ tailWord_7666138) baseStart_7666138 baseEnd_7666138 := by
    simpa [prefixWord, tailWord_7666138, baseEnd_7666138] using wordTrace_append hprefix tailTrace_7666138
  have hstable : (prefixWord ++ tailWord_7666138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666138).length < 2 ^ (prefixWord ++ tailWord_7666138).sum := by decide
  have hdescent : baseEnd_7666138 < baseStart_7666138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666191 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 5, 5]
def baseStart_7666191 : Nat := 118140960795 + 7666191 * 2 ^ 59
def prefixEnd_7666191 : Nat := 4983230072969 + 3 ^ 40 * 7666191 * 2
def baseEnd_7666191 : Nat := 1312146924057373575385445

theorem tailTrace_7666191 : CollatzResearch.WordTrace tailWord_7666191 prefixEnd_7666191 1312146924057373575385445 := by
  unfold tailWord_7666191
  simp only [CollatzResearch.WordTrace]
  refine ⟨279608956569706763030710427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186405971046471175353806951 279608956569706763030710427)
  ·
    refine ⟨419413434854560144546065641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279608956569706763030710427 419413434854560144546065641)
    ·
      refine ⟨314560076140920108409549231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419413434854560144546065641 314560076140920108409549231)
      ·
        refine ⟨471840114211380162614323847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314560076140920108409549231 471840114211380162614323847)
        ·
          refine ⟨707760171317070243921485771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471840114211380162614323847 707760171317070243921485771)
          ·
            refine ⟨1061640256975605365882228657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707760171317070243921485771 1061640256975605365882228657)
            ·
              refine ⟨796230192731704024411671493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1061640256975605365882228657 796230192731704024411671493)
              ·
                refine ⟨149293161137194504577188405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 796230192731704024411671493 149293161137194504577188405)
                ·
                  refine ⟨13996233856611984804111413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149293161137194504577188405 13996233856611984804111413)
                  ·
                    refine ⟨1312146924057373575385445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13996233856611984804111413 1312146924057373575385445)
                    ·
                      rfl

theorem cell23_7666191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 5].length) (baseStart_7666191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666191 prefixEnd_7666191 := by exact prefixLift 7666191
  have htrace : WordTrace (prefixWord ++ tailWord_7666191) baseStart_7666191 baseEnd_7666191 := by
    simpa [prefixWord, tailWord_7666191, baseEnd_7666191] using wordTrace_append hprefix tailTrace_7666191
  have hstable : (prefixWord ++ tailWord_7666191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666191).length < 2 ^ (prefixWord ++ tailWord_7666191).sum := by decide
  have hdescent : baseEnd_7666191 < baseStart_7666191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666199 : List Nat := [1, 1, 3, 6, 1, 1, 1, 4, 1, 4]
def baseStart_7666199 : Nat := 118140960795 + 7666199 * 2 ^ 59
def prefixEnd_7666199 : Nat := 4983230072969 + 3 ^ 40 * 7666199 * 2
def baseEnd_7666199 : Nat := 1312148293339118898285433

theorem tailTrace_7666199 : CollatzResearch.WordTrace tailWord_7666199 prefixEnd_7666199 1312148293339118898285433 := by
  unfold tailWord_7666199
  simp only [CollatzResearch.WordTrace]
  refine ⟨279609248353677780397001651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186406165569118520264667767 279609248353677780397001651)
  ·
    refine ⟨419413872530516670595502477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279609248353677780397001651 419413872530516670595502477)
    ·
      refine ⟨157280202198943751473313429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419413872530516670595502477 157280202198943751473313429)
      ·
        refine ⟨7372509478075488350311567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 157280202198943751473313429 7372509478075488350311567)
        ·
          refine ⟨11058764217113232525467351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7372509478075488350311567 11058764217113232525467351)
          ·
            refine ⟨16588146325669848788201027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11058764217113232525467351 16588146325669848788201027)
            ·
              refine ⟨24882219488504773182301541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16588146325669848788201027 24882219488504773182301541)
              ·
                refine ⟨4665416154094644971681539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24882219488504773182301541 4665416154094644971681539)
                ·
                  refine ⟨6998124231141967457522309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4665416154094644971681539 6998124231141967457522309)
                  ·
                    refine ⟨1312148293339118898285433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6998124231141967457522309 1312148293339118898285433)
                    ·
                      rfl

theorem cell23_7666199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 1, 4].length) (baseStart_7666199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666199 prefixEnd_7666199 := by exact prefixLift 7666199
  have htrace : WordTrace (prefixWord ++ tailWord_7666199) baseStart_7666199 baseEnd_7666199 := by
    simpa [prefixWord, tailWord_7666199, baseEnd_7666199] using wordTrace_append hprefix tailTrace_7666199
  have hstable : (prefixWord ++ tailWord_7666199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666199).length < 2 ^ (prefixWord ++ tailWord_7666199).sum := by decide
  have hdescent : baseEnd_7666199 < baseStart_7666199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666245 : List Nat := [1, 3, 1, 1, 1, 6, 1, 3, 1, 1, 4]
def baseStart_7666245 : Nat := 118140960795 + 7666245 * 2 ^ 59
def prefixEnd_7666245 : Nat := 4983230072969 + 3 ^ 40 * 7666245 * 2
def baseEnd_7666245 : Nat := 3936468500127463514881087

theorem tailTrace_7666245 : CollatzResearch.WordTrace tailWord_7666245 prefixEnd_7666245 3936468500127463514881087 := by
  unfold tailWord_7666245
  simp only [CollatzResearch.WordTrace]
  refine ⟨279610926111511130253176189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186407284074340753502117459 279610926111511130253176189)
  ·
    refine ⟨104854097291816673844941071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279610926111511130253176189 104854097291816673844941071)
    ·
      refine ⟨157281145937725010767411607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104854097291816673844941071 157281145937725010767411607)
      ·
        refine ⟨235921718906587516151117411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157281145937725010767411607 235921718906587516151117411)
        ·
          refine ⟨353882578359881274226676117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235921718906587516151117411 353882578359881274226676117)
          ·
            refine ⟨16588245860619434729375443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 353882578359881274226676117 16588245860619434729375443)
            ·
              refine ⟨24882368790929152094063165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16588245860619434729375443 24882368790929152094063165)
              ·
                refine ⟨9330888296598432035273687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24882368790929152094063165 9330888296598432035273687)
                ·
                  refine ⟨13996332444897648052910531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9330888296598432035273687 13996332444897648052910531)
                  ·
                    refine ⟨20994498667346472079365797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13996332444897648052910531 20994498667346472079365797)
                    ·
                      refine ⟨3936468500127463514881087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20994498667346472079365797 3936468500127463514881087)
                      ·
                        rfl

theorem cell23_7666245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 1, 4].length) (baseStart_7666245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666245 prefixEnd_7666245 := by exact prefixLift 7666245
  have htrace : WordTrace (prefixWord ++ tailWord_7666245) baseStart_7666245 baseEnd_7666245 := by
    simpa [prefixWord, tailWord_7666245, baseEnd_7666245] using wordTrace_append hprefix tailTrace_7666245
  have hstable : (prefixWord ++ tailWord_7666245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666245).length < 2 ^ (prefixWord ++ tailWord_7666245).sum := by decide
  have hdescent : baseEnd_7666245 < baseStart_7666245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666255 : List Nat := [1, 1, 2, 1, 1, 2, 7, 2, 2, 4]
def baseStart_7666255 : Nat := 118140960795 + 7666255 * 2 ^ 59
def prefixEnd_7666255 : Nat := 4983230072969 + 3 ^ 40 * 7666255 * 2
def baseEnd_7666255 : Nat := 1312157878311336158585347

theorem tailTrace_7666255 : CollatzResearch.WordTrace tailWord_7666255 prefixEnd_7666255 1312157878311336158585347 := by
  unfold tailWord_7666255
  simp only [CollatzResearch.WordTrace]
  refine ⟨279611290841474901961040219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186407527227649934640693479 279611290841474901961040219)
  ·
    refine ⟨419416936262212352941560329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279611290841474901961040219 419416936262212352941560329)
    ·
      refine ⟨314562702196659264706170247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419416936262212352941560329 314562702196659264706170247)
      ·
        refine ⟨471844053294988897059255371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314562702196659264706170247 471844053294988897059255371)
        ·
          refine ⟨707766079942483345588883057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471844053294988897059255371 707766079942483345588883057)
          ·
            refine ⟨530824559956862509191662293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 707766079942483345588883057 530824559956862509191662293)
            ·
              refine ⟨12441200623988965059179585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 530824559956862509191662293 12441200623988965059179585)
              ·
                refine ⟨9330900467991723794384689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12441200623988965059179585 9330900467991723794384689)
                ·
                  refine ⟨6998175350993792845788517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9330900467991723794384689 6998175350993792845788517)
                  ·
                    refine ⟨1312157878311336158585347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6998175350993792845788517 1312157878311336158585347)
                    ·
                      rfl

theorem cell23_7666255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 4].length) (baseStart_7666255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666255 prefixEnd_7666255 := by exact prefixLift 7666255
  have htrace : WordTrace (prefixWord ++ tailWord_7666255) baseStart_7666255 baseEnd_7666255 := by
    simpa [prefixWord, tailWord_7666255, baseEnd_7666255] using wordTrace_append hprefix tailTrace_7666255
  have hstable : (prefixWord ++ tailWord_7666255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666255).length < 2 ^ (prefixWord ++ tailWord_7666255).sum := by decide
  have hdescent : baseEnd_7666255 < baseStart_7666255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666258 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_7666258 : Nat := 118140960795 + 7666258 * 2 ^ 59
def prefixEnd_7666258 : Nat := 4983230072969 + 3 ^ 40 * 7666258 * 2
def baseEnd_7666258 : Nat := 3936475175375971964018527

theorem tailTrace_7666258 : CollatzResearch.WordTrace tailWord_7666258 prefixEnd_7666258 3936475175375971964018527 := by
  unfold tailWord_7666258
  simp only [CollatzResearch.WordTrace]
  refine ⟨69902850065116008368349857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186407600173642688982266285 69902850065116008368349857)
  ·
    refine ⟨52427137548837006276262393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69902850065116008368349857 52427137548837006276262393)
    ·
      refine ⟨39320353161627754707196795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52427137548837006276262393 39320353161627754707196795)
      ·
        refine ⟨58980529742441632060795193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39320353161627754707196795 58980529742441632060795193)
        ·
          refine ⟨44235397306831224045596395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58980529742441632060795193 44235397306831224045596395)
          ·
            refine ⟨66353095960246836068394593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44235397306831224045596395 66353095960246836068394593)
            ·
              refine ⟨49764821970185127051295945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66353095960246836068394593 49764821970185127051295945)
              ·
                refine ⟨37323616477638845288471959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49764821970185127051295945 37323616477638845288471959)
                ·
                  refine ⟨55985424716458267932707939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37323616477638845288471959 55985424716458267932707939)
                  ·
                    refine ⟨83978137074687401899061909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55985424716458267932707939 83978137074687401899061909)
                    ·
                      refine ⟨3936475175375971964018527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83978137074687401899061909 3936475175375971964018527)
                      ·
                        rfl

theorem cell23_7666258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_7666258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666258 prefixEnd_7666258 := by exact prefixLift 7666258
  have htrace : WordTrace (prefixWord ++ tailWord_7666258) baseStart_7666258 baseEnd_7666258 := by
    simpa [prefixWord, tailWord_7666258, baseEnd_7666258] using wordTrace_append hprefix tailTrace_7666258
  have hstable : (prefixWord ++ tailWord_7666258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666258).length < 2 ^ (prefixWord ++ tailWord_7666258).sum := by decide
  have hdescent : baseEnd_7666258 < baseStart_7666258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666282 : List Nat := [3, 1, 3, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_7666282 : Nat := 118140960795 + 7666282 * 2 ^ 59
def prefixEnd_7666282 : Nat := 4983230072969 + 3 ^ 40 * 7666282 * 2
def baseEnd_7666282 : Nat := 3936487498911679870118417

theorem tailTrace_7666282 : CollatzResearch.WordTrace tailWord_7666282 prefixEnd_7666282 3936487498911679870118417 := by
  unfold tailWord_7666282
  simp only [CollatzResearch.WordTrace]
  refine ⟨69903068903094271393068275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186408183741584723714848733 69903068903094271393068275)
  ·
    refine ⟨104854603354641407089602413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69903068903094271393068275 104854603354641407089602413)
    ·
      refine ⟨39320476257990527658600905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104854603354641407089602413 39320476257990527658600905)
      ·
        refine ⟨29490357193492895743950679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39320476257990527658600905 29490357193492895743950679)
        ·
          refine ⟨44235535790239343615926019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29490357193492895743950679 44235535790239343615926019)
          ·
            refine ⟨66353303685359015423889029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44235535790239343615926019 66353303685359015423889029)
            ·
              refine ⟨12441244441004815391979193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66353303685359015423889029 12441244441004815391979193)
              ·
                refine ⟨9330933330753611543984395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12441244441004815391979193 9330933330753611543984395)
                ·
                  refine ⟨13996399996130417315976593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9330933330753611543984395 13996399996130417315976593)
                  ·
                    refine ⟨10497299997097812986982445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13996399996130417315976593 10497299997097812986982445)
                    ·
                      refine ⟨3936487498911679870118417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10497299997097812986982445 3936487498911679870118417)
                      ·
                        rfl

theorem cell23_7666282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_7666282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666282 prefixEnd_7666282 := by exact prefixLift 7666282
  have htrace : WordTrace (prefixWord ++ tailWord_7666282) baseStart_7666282 baseEnd_7666282 := by
    simpa [prefixWord, tailWord_7666282, baseEnd_7666282] using wordTrace_append hprefix tailTrace_7666282
  have hstable : (prefixWord ++ tailWord_7666282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666282).length < 2 ^ (prefixWord ++ tailWord_7666282).sum := by decide
  have hdescent : baseEnd_7666282 < baseStart_7666282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666285 : List Nat := [1, 5, 1, 1, 3, 1, 4, 7]
def baseStart_7666285 : Nat := 118140960795 + 7666285 * 2 ^ 59
def prefixEnd_7666285 : Nat := 4983230072969 + 3 ^ 40 * 7666285 * 2
def baseEnd_7666285 : Nat := 145795890346431235495589

theorem tailTrace_7666285 : CollatzResearch.WordTrace tailWord_7666285 prefixEnd_7666285 145795890346431235495589 := by
  unfold tailWord_7666285
  simp only [CollatzResearch.WordTrace]
  refine ⟨279612385031366217084632309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186408256687577478056421539 279612385031366217084632309)
  ·
    refine ⟨26213661096690582851684279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279612385031366217084632309 26213661096690582851684279)
    ·
      refine ⟨39320491645035874277526419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26213661096690582851684279 39320491645035874277526419)
      ·
        refine ⟨58980737467553811416289629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39320491645035874277526419 58980737467553811416289629)
        ·
          refine ⟨22117776550332679281108611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58980737467553811416289629 22117776550332679281108611)
          ·
            refine ⟨33176664825499018921662917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22117776550332679281108611 33176664825499018921662917)
            ·
              refine ⟨6220624654781066047811797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33176664825499018921662917 6220624654781066047811797)
              ·
                refine ⟨145795890346431235495589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6220624654781066047811797 145795890346431235495589)
                ·
                  rfl

theorem cell23_7666285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 7].length) (baseStart_7666285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666285 prefixEnd_7666285 := by exact prefixLift 7666285
  have htrace : WordTrace (prefixWord ++ tailWord_7666285) baseStart_7666285 baseEnd_7666285 := by
    simpa [prefixWord, tailWord_7666285, baseEnd_7666285] using wordTrace_append hprefix tailTrace_7666285
  have hstable : (prefixWord ++ tailWord_7666285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666285).length < 2 ^ (prefixWord ++ tailWord_7666285).sum := by decide
  have hdescent : baseEnd_7666285 < baseStart_7666285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666295 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 4, 1, 3]
def baseStart_7666295 : Nat := 118140960795 + 7666295 * 2 ^ 59
def prefixEnd_7666295 : Nat := 4983230072969 + 3 ^ 40 * 7666295 * 2
def baseEnd_7666295 : Nat := 3936494174160188319255857

theorem tailTrace_7666295 : CollatzResearch.WordTrace tailWord_7666295 prefixEnd_7666295 3936494174160188319255857 := by
  unfold tailWord_7666295
  simp only [CollatzResearch.WordTrace]
  refine ⟨279612749761329988792496339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186408499840886659194997559 279612749761329988792496339)
  ·
    refine ⟨419419124641994983188744509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279612749761329988792496339 419419124641994983188744509)
    ·
      refine ⟨157282171740748118695779191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419419124641994983188744509 157282171740748118695779191)
      ·
        refine ⟨235923257611122178043668787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157282171740748118695779191 235923257611122178043668787)
        ·
          refine ⟨353884886416683267065503181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235923257611122178043668787 353884886416683267065503181)
          ·
            refine ⟨132706832406256225149563693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353884886416683267065503181 132706832406256225149563693)
            ·
              refine ⟨49765062152346084431086385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132706832406256225149563693 49765062152346084431086385)
              ·
                refine ⟨37323796614259563323314789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49765062152346084431086385 37323796614259563323314789)
                ·
                  refine ⟨6998211865173668123121523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37323796614259563323314789 6998211865173668123121523)
                  ·
                    refine ⟨10497317797760502184682285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6998211865173668123121523 10497317797760502184682285)
                    ·
                      refine ⟨3936494174160188319255857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10497317797760502184682285 3936494174160188319255857)
                      ·
                        rfl

theorem cell23_7666295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 1, 3].length) (baseStart_7666295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666295 prefixEnd_7666295 := by exact prefixLift 7666295
  have htrace : WordTrace (prefixWord ++ tailWord_7666295) baseStart_7666295 baseEnd_7666295 := by
    simpa [prefixWord, tailWord_7666295, baseEnd_7666295] using wordTrace_append hprefix tailTrace_7666295
  have hstable : (prefixWord ++ tailWord_7666295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666295).length < 2 ^ (prefixWord ++ tailWord_7666295).sum := by decide
  have hdescent : baseEnd_7666295 < baseStart_7666295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666328 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 1, 8]
def baseStart_7666328 : Nat := 118140960795 + 7666328 * 2 ^ 59
def prefixEnd_7666328 : Nat := 4983230072969 + 3 ^ 40 * 7666328 * 2
def baseEnd_7666328 : Nat := 1312170373007262230047735

theorem tailTrace_7666328 : CollatzResearch.WordTrace tailWord_7666328 prefixEnd_7666328 1312170373007262230047735 := by
  unfold tailWord_7666328
  simp only [CollatzResearch.WordTrace]
  refine ⟨139806976685105217714223819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186409302246806956952298425 139806976685105217714223819)
  ·
    refine ⟨209710465027657826571335729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139806976685105217714223819 209710465027657826571335729)
    ·
      refine ⟨157282848770743369928501797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209710465027657826571335729 157282848770743369928501797)
      ·
        refine ⟨29490534144514381861594087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157282848770743369928501797 29490534144514381861594087)
        ·
          refine ⟨44235801216771572792391131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29490534144514381861594087 44235801216771572792391131)
          ·
            refine ⟨66353701825157359188586697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44235801216771572792391131 66353701825157359188586697)
            ·
              refine ⟨49765276368868019391440023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66353701825157359188586697 49765276368868019391440023)
              ·
                refine ⟨74647914553302029087160035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49765276368868019391440023 74647914553302029087160035)
                ·
                  refine ⟨111971871829953043630740053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74647914553302029087160035 111971871829953043630740053)
                  ·
                    refine ⟨1312170373007262230047735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111971871829953043630740053 1312170373007262230047735)
                    ·
                      rfl

theorem cell23_7666328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_7666328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666328 prefixEnd_7666328 := by exact prefixLift 7666328
  have htrace : WordTrace (prefixWord ++ tailWord_7666328) baseStart_7666328 baseEnd_7666328 := by
    simpa [prefixWord, tailWord_7666328, baseEnd_7666328] using wordTrace_append hprefix tailTrace_7666328
  have hstable : (prefixWord ++ tailWord_7666328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666328).length < 2 ^ (prefixWord ++ tailWord_7666328).sum := by decide
  have hdescent : baseEnd_7666328 < baseStart_7666328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666385 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 2, 3, 3]
def baseStart_7666385 : Nat := 118140960795 + 7666385 * 2 ^ 59
def prefixEnd_7666385 : Nat := 4983230072969 + 3 ^ 40 * 7666385 * 2
def baseEnd_7666385 : Nat := 3936540387419092967130443

theorem tailTrace_7666385 : CollatzResearch.WordTrace tailWord_7666385 prefixEnd_7666385 3936540387419092967130443 := by
  unfold tailWord_7666385
  simp only [CollatzResearch.WordTrace]
  refine ⟨279616032331003934163272609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186410688220669289442181739 279616032331003934163272609)
  ·
    refine ⟨209712024248252950622454457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279616032331003934163272609 209712024248252950622454457)
    ·
      refine ⟨157284018186189712966840843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209712024248252950622454457 157284018186189712966840843)
      ·
        refine ⟨235926027279284569450261265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157284018186189712966840843 235926027279284569450261265)
        ·
          refine ⟨176944520459463427087695949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235926027279284569450261265 176944520459463427087695949)
          ·
            refine ⟨66354195172298785157885981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176944520459463427087695949 66354195172298785157885981)
            ·
              refine ⟨24882823189612044434207243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66354195172298785157885981 24882823189612044434207243)
              ·
                refine ⟨37324234784418066651310865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24882823189612044434207243 37324234784418066651310865)
                ·
                  refine ⟨27993176088313549988483149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37324234784418066651310865 27993176088313549988483149)
                  ·
                    refine ⟨10497441033117581245681181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27993176088313549988483149 10497441033117581245681181)
                    ·
                      refine ⟨3936540387419092967130443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10497441033117581245681181 3936540387419092967130443)
                      ·
                        rfl

theorem cell23_7666385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_7666385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666385 prefixEnd_7666385 := by exact prefixLift 7666385
  have htrace : WordTrace (prefixWord ++ tailWord_7666385) baseStart_7666385 baseEnd_7666385 := by
    simpa [prefixWord, tailWord_7666385, baseEnd_7666385] using wordTrace_append hprefix tailTrace_7666385
  have hstable : (prefixWord ++ tailWord_7666385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666385).length < 2 ^ (prefixWord ++ tailWord_7666385).sum := by decide
  have hdescent : baseEnd_7666385 < baseStart_7666385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666405 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 1, 7]
def baseStart_7666405 : Nat := 118140960795 + 7666405 * 2 ^ 59
def prefixEnd_7666405 : Nat := 4983230072969 + 3 ^ 40 * 7666405 * 2
def baseEnd_7666405 : Nat := 1312183552344060962960117

theorem tailTrace_7666405 : CollatzResearch.WordTrace tailWord_7666405 prefixEnd_7666405 1312183552344060962960117 := by
  unfold tailWord_7666405
  simp only [CollatzResearch.WordTrace]
  refine ⟨279616761790931477579000669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186411174527287651719333779 279616761790931477579000669)
  ·
    refine ⟨104856285671599304092125251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279616761790931477579000669 104856285671599304092125251)
    ·
      refine ⟨157284428507398956138187877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104856285671599304092125251 157284428507398956138187877)
      ·
        refine ⟨29490830345137304275910227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157284428507398956138187877 29490830345137304275910227)
        ·
          refine ⟨44236245517705956413865341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29490830345137304275910227 44236245517705956413865341)
          ·
            refine ⟨16588592069139733655199503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44236245517705956413865341 16588592069139733655199503)
            ·
              refine ⟨24882888103709600482799255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16588592069139733655199503 24882888103709600482799255)
              ·
                refine ⟨37324332155564400724198883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24882888103709600482799255 37324332155564400724198883)
                ·
                  refine ⟨55986498233346601086298325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37324332155564400724198883 55986498233346601086298325)
                  ·
                    refine ⟨1312183552344060962960117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55986498233346601086298325 1312183552344060962960117)
                    ·
                      rfl

theorem cell23_7666405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_7666405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666405 prefixEnd_7666405 := by exact prefixLift 7666405
  have htrace : WordTrace (prefixWord ++ tailWord_7666405) baseStart_7666405 baseEnd_7666405 := by
    simpa [prefixWord, tailWord_7666405, baseEnd_7666405] using wordTrace_append hprefix tailTrace_7666405
  have hstable : (prefixWord ++ tailWord_7666405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666405).length < 2 ^ (prefixWord ++ tailWord_7666405).sum := by decide
  have hdescent : baseEnd_7666405 < baseStart_7666405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666425 : List Nat := [1, 2, 1, 3, 1, 1, 1, 6, 2, 1, 4]
def baseStart_7666425 : Nat := 118140960795 + 7666425 * 2 ^ 59
def prefixEnd_7666425 : Nat := 4983230072969 + 3 ^ 40 * 7666425 * 2
def baseEnd_7666425 : Nat := 3936560926645272810630259

theorem tailTrace_7666425 : CollatzResearch.WordTrace tailWord_7666425 prefixEnd_7666425 3936560926645272810630259 := by
  unfold tailWord_7666425
  simp only [CollatzResearch.WordTrace]
  refine ⟨279617491250859020994728729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186411660833906013996485819 279617491250859020994728729)
  ·
    refine ⟨209713118438144265746046547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279617491250859020994728729 209713118438144265746046547)
    ·
      refine ⟨314569677657216398619069821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209713118438144265746046547 314569677657216398619069821)
      ·
        refine ⟨117963629121456149482151183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314569677657216398619069821 117963629121456149482151183)
        ·
          refine ⟨176945443682184224223226775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117963629121456149482151183 176945443682184224223226775)
          ·
            refine ⟨265418165523276336334840163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176945443682184224223226775 265418165523276336334840163)
            ·
              refine ⟨398127248284914504502260245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265418165523276336334840163 398127248284914504502260245)
              ·
                refine ⟨18662214763355367398543449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 398127248284914504502260245 18662214763355367398543449)
                ·
                  refine ⟨13996661072516525548907587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18662214763355367398543449 13996661072516525548907587)
                  ·
                    refine ⟨20994991608774788323361381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13996661072516525548907587 20994991608774788323361381)
                    ·
                      refine ⟨3936560926645272810630259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20994991608774788323361381 3936560926645272810630259)
                      ·
                        rfl

theorem cell23_7666425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_7666425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666425 prefixEnd_7666425 := by exact prefixLift 7666425
  have htrace : WordTrace (prefixWord ++ tailWord_7666425) baseStart_7666425 baseEnd_7666425 := by
    simpa [prefixWord, tailWord_7666425, baseEnd_7666425] using wordTrace_append hprefix tailTrace_7666425
  have hstable : (prefixWord ++ tailWord_7666425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666425).length < 2 ^ (prefixWord ++ tailWord_7666425).sum := by decide
  have hdescent : baseEnd_7666425 < baseStart_7666425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666442 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 2, 4, 2]
def baseStart_7666442 : Nat := 118140960795 + 7666442 * 2 ^ 59
def prefixEnd_7666442 : Nat := 4983230072969 + 3 ^ 40 * 7666442 * 2
def baseEnd_7666442 : Nat := 3936569655816399244117681

theorem tailTrace_7666442 : CollatzResearch.WordTrace tailWord_7666442 prefixEnd_7666442 3936569655816399244117681 := by
  unfold tailWord_7666442
  simp only [CollatzResearch.WordTrace]
  refine ⟨69904527822949358224524395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186412074194531621932065053 69904527822949358224524395)
  ·
    refine ⟨104856791734424037336786593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69904527822949358224524395 104856791734424037336786593)
    ·
      refine ⟨78642593800818028002589945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104856791734424037336786593 78642593800818028002589945)
      ·
        refine ⟨58981945350613521001942459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78642593800818028002589945 58981945350613521001942459)
        ·
          refine ⟨88472918025920281502913689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58981945350613521001942459 88472918025920281502913689)
          ·
            refine ⟨66354688519440211127185267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88472918025920281502913689 66354688519440211127185267)
            ·
              refine ⟨99532032779160316690777901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66354688519440211127185267 99532032779160316690777901)
              ·
                refine ⟨37324512292185118759041713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99532032779160316690777901 37324512292185118759041713)
                ·
                  refine ⟨27993384219138839069281285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37324512292185118759041713 27993384219138839069281285)
                  ·
                    refine ⟨5248759541088532325490241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27993384219138839069281285 5248759541088532325490241)
                    ·
                      refine ⟨3936569655816399244117681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5248759541088532325490241 3936569655816399244117681)
                      ·
                        rfl

theorem cell23_7666442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_7666442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666442 prefixEnd_7666442 := by exact prefixLift 7666442
  have htrace : WordTrace (prefixWord ++ tailWord_7666442) baseStart_7666442 baseEnd_7666442 := by
    simpa [prefixWord, tailWord_7666442, baseEnd_7666442] using wordTrace_append hprefix tailTrace_7666442
  have hstable : (prefixWord ++ tailWord_7666442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666442).length < 2 ^ (prefixWord ++ tailWord_7666442).sum := by decide
  have hdescent : baseEnd_7666442 < baseStart_7666442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666512 : List Nat := [2, 1, 1, 1, 1, 4, 5, 2, 1, 5]
def baseStart_7666512 : Nat := 118140960795 + 7666512 * 2 ^ 59
def prefixEnd_7666512 : Nat := 4983230072969 + 3 ^ 40 * 7666512 * 2
def baseEnd_7666512 : Nat := 1312201866487404656747453

theorem tailTrace_7666512 : CollatzResearch.WordTrace tailWord_7666512 prefixEnd_7666512 1312201866487404656747453 := by
  unfold tailWord_7666512
  simp only [CollatzResearch.WordTrace]
  refine ⟨139810332200771917426572895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186413776267695889902097193 139810332200771917426572895)
  ·
    refine ⟨209715498301157876139859343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139810332200771917426572895 209715498301157876139859343)
    ·
      refine ⟨314573247451736814209789015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209715498301157876139859343 314573247451736814209789015)
      ·
        refine ⟨471859871177605221314683523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314573247451736814209789015 471859871177605221314683523)
        ·
          refine ⟨707789806766407831972025285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471859871177605221314683523 707789806766407831972025285)
          ·
            refine ⟨132710588768701468494754741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 707789806766407831972025285 132710588768701468494754741)
            ·
              refine ⟨12441617697065762671383257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132710588768701468494754741 12441617697065762671383257)
              ·
                refine ⟨9331213272799322003537443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12441617697065762671383257 9331213272799322003537443)
                ·
                  refine ⟨13996819909198983005306165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9331213272799322003537443 13996819909198983005306165)
                  ·
                    refine ⟨1312201866487404656747453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13996819909198983005306165 1312201866487404656747453)
                    ·
                      rfl

theorem cell23_7666512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 1, 5].length) (baseStart_7666512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666512 prefixEnd_7666512 := by exact prefixLift 7666512
  have htrace : WordTrace (prefixWord ++ tailWord_7666512) baseStart_7666512 baseEnd_7666512 := by
    simpa [prefixWord, tailWord_7666512, baseEnd_7666512] using wordTrace_append hprefix tailTrace_7666512
  have hstable : (prefixWord ++ tailWord_7666512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666512).length < 2 ^ (prefixWord ++ tailWord_7666512).sum := by decide
  have hdescent : baseEnd_7666512 < baseStart_7666512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666519 : List Nat := [1, 1, 3, 2, 4, 1, 1, 3, 2, 3, 2]
def baseStart_7666519 : Nat := 118140960795 + 7666519 * 2 ^ 59
def prefixEnd_7666519 : Nat := 4983230072969 + 3 ^ 40 * 7666519 * 2
def baseEnd_7666519 : Nat := 3936609193826795442854827

theorem tailTrace_7666519 : CollatzResearch.WordTrace tailWord_7666519 prefixEnd_7666519 3936609193826795442854827 := by
  unfold tailWord_7666519
  simp only [CollatzResearch.WordTrace]
  refine ⟨279620919712518475048650611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186413946475012316699100407 279620919712518475048650611)
  ·
    refine ⟨419431379568777712572975917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279620919712518475048650611 419431379568777712572975917)
    ·
      refine ⟨157286767338291642214865969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419431379568777712572975917 157286767338291642214865969)
      ·
        refine ⟨117965075503718731661149477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157286767338291642214865969 117965075503718731661149477)
        ·
          refine ⟨22118451656947262186465527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117965075503718731661149477 22118451656947262186465527)
          ·
            refine ⟨33177677485420893279698291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22118451656947262186465527 33177677485420893279698291)
            ·
              refine ⟨49766516228131339919547437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33177677485420893279698291 49766516228131339919547437)
              ·
                refine ⟨18662443585549252469830289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49766516228131339919547437 18662443585549252469830289)
                ·
                  refine ⟨13996832689161939352372717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18662443585549252469830289 13996832689161939352372717)
                  ·
                    refine ⟨5248812258435727257139769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13996832689161939352372717 5248812258435727257139769)
                    ·
                      refine ⟨3936609193826795442854827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5248812258435727257139769 3936609193826795442854827)
                      ·
                        rfl

theorem cell23_7666519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_7666519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666519 prefixEnd_7666519 := by exact prefixLift 7666519
  have htrace : WordTrace (prefixWord ++ tailWord_7666519) baseStart_7666519 baseEnd_7666519 := by
    simpa [prefixWord, tailWord_7666519, baseEnd_7666519] using wordTrace_append hprefix tailTrace_7666519
  have hstable : (prefixWord ++ tailWord_7666519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666519).length < 2 ^ (prefixWord ++ tailWord_7666519).sum := by decide
  have hdescent : baseEnd_7666519 < baseStart_7666519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666555 : List Nat := [1, 1, 1, 1, 1, 5, 5, 8]
def baseStart_7666555 : Nat := 118140960795 + 7666555 * 2 ^ 59
def prefixEnd_7666555 : Nat := 4983230072969 + 3 ^ 40 * 7666555 * 2
def baseEnd_7666555 : Nat := 145801025152976196370543

theorem tailTrace_7666555 : CollatzResearch.WordTrace tailWord_7666555 prefixEnd_7666555 145801025152976196370543 := by
  unfold tailWord_7666555
  simp only [CollatzResearch.WordTrace]
  refine ⟨279622232740388053196961119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186414821826925368797974079 279622232740388053196961119)
  ·
    refine ⟨419433349110582079795441679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279622232740388053196961119 419433349110582079795441679)
    ·
      refine ⟨629150023665873119693162519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419433349110582079795441679 629150023665873119693162519)
      ·
        refine ⟨943725035498809679539743779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629150023665873119693162519 943725035498809679539743779)
        ·
          refine ⟨1415587553248214519309615669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943725035498809679539743779 1415587553248214519309615669)
          ·
            refine ⟨132711333117020111185276469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1415587553248214519309615669 132711333117020111185276469)
            ·
              refine ⟨12441687479720635423619669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132711333117020111185276469 12441687479720635423619669)
              ·
                refine ⟨145801025152976196370543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12441687479720635423619669 145801025152976196370543)
                ·
                  rfl

theorem cell23_7666555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 8].length) (baseStart_7666555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666555 prefixEnd_7666555 := by exact prefixLift 7666555
  have htrace : WordTrace (prefixWord ++ tailWord_7666555) baseStart_7666555 baseEnd_7666555 := by
    simpa [prefixWord, tailWord_7666555, baseEnd_7666555] using wordTrace_append hprefix tailTrace_7666555
  have hstable : (prefixWord ++ tailWord_7666555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666555).length < 2 ^ (prefixWord ++ tailWord_7666555).sum := by decide
  have hdescent : baseEnd_7666555 < baseStart_7666555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666583 : List Nat := [1, 1, 3, 3, 1, 2, 4, 3, 1, 2, 2]
def baseStart_7666583 : Nat := 118140960795 + 7666583 * 2 ^ 59
def prefixEnd_7666583 : Nat := 4983230072969 + 3 ^ 40 * 7666583 * 2
def baseEnd_7666583 : Nat := 3936642056588683192454533

theorem tailTrace_7666583 : CollatzResearch.WordTrace tailWord_7666583 prefixEnd_7666583 3936642056588683192454533 := by
  unfold tailWord_7666583
  simp only [CollatzResearch.WordTrace]
  refine ⟨279623253984286613978980403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186415502656191075985986935 279623253984286613978980403)
  ·
    refine ⟨419434880976429920968470605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279623253984286613978980403 419434880976429920968470605)
    ·
      refine ⟨157288080366161220363176477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419434880976429920968470605 157288080366161220363176477)
      ·
        refine ⟨58983030137310457636191179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157288080366161220363176477 58983030137310457636191179)
        ·
          refine ⟨88474545205965686454286769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58983030137310457636191179 88474545205965686454286769)
          ·
            refine ⟨66355908904474264840715077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88474545205965686454286769 66355908904474264840715077)
            ·
              refine ⟨12441732919588924657634077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66355908904474264840715077 12441732919588924657634077)
              ·
                refine ⟨4665649844845846746612779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12441732919588924657634077 4665649844845846746612779)
                ·
                  refine ⟨6998474767268770119919169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4665649844845846746612779 6998474767268770119919169)
                  ·
                    refine ⟨5248856075451577589939377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6998474767268770119919169 5248856075451577589939377)
                    ·
                      refine ⟨3936642056588683192454533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5248856075451577589939377 3936642056588683192454533)
                      ·
                        rfl

theorem cell23_7666583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_7666583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666583 prefixEnd_7666583 := by exact prefixLift 7666583
  have htrace : WordTrace (prefixWord ++ tailWord_7666583) baseStart_7666583 baseEnd_7666583 := by
    simpa [prefixWord, tailWord_7666583, baseEnd_7666583] using wordTrace_append hprefix tailTrace_7666583
  have hstable : (prefixWord ++ tailWord_7666583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666583).length < 2 ^ (prefixWord ++ tailWord_7666583).sum := by decide
  have hdescent : baseEnd_7666583 < baseStart_7666583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666586 : List Nat := [3, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3]
def baseStart_7666586 : Nat := 118140960795 + 7666586 * 2 ^ 59
def prefixEnd_7666586 : Nat := 4983230072969 + 3 ^ 40 * 7666586 * 2
def baseEnd_7666586 : Nat := 3936643597030646680717019

theorem tailTrace_7666586 : CollatzResearch.WordTrace tailWord_7666586 prefixEnd_7666586 3936643597030646680717019 := by
  unfold tailWord_7666586
  simp only [CollatzResearch.WordTrace]
  refine ⟨69905840850818936372834903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186415575602183830327559741 69905840850818936372834903)
  ·
    refine ⟨104858761276228404559252355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69905840850818936372834903 104858761276228404559252355)
    ·
      refine ⟨157288141914342606838878533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104858761276228404559252355 157288141914342606838878533)
      ·
        refine ⟨29491526608939238782289725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157288141914342606838878533 29491526608939238782289725)
        ·
          refine ⟨11059322478352214543358647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29491526608939238782289725 11059322478352214543358647)
          ·
            refine ⟨16588983717528321815037971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11059322478352214543358647 16588983717528321815037971)
            ·
              refine ⟨24883475576292482722556957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16588983717528321815037971 24883475576292482722556957)
              ·
                refine ⟨9331303341109681020958859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24883475576292482722556957 9331303341109681020958859)
                ·
                  refine ⟨13996955011664521531438289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9331303341109681020958859 13996955011664521531438289)
                  ·
                    refine ⟨10497716258748391148578717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13996955011664521531438289 10497716258748391148578717)
                    ·
                      refine ⟨3936643597030646680717019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10497716258748391148578717 3936643597030646680717019)
                      ·
                        rfl

theorem cell23_7666586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_7666586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666586 prefixEnd_7666586 := by exact prefixLift 7666586
  have htrace : WordTrace (prefixWord ++ tailWord_7666586) baseStart_7666586 baseEnd_7666586 := by
    simpa [prefixWord, tailWord_7666586, baseEnd_7666586] using wordTrace_append hprefix tailTrace_7666586
  have hstable : (prefixWord ++ tailWord_7666586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666586).length < 2 ^ (prefixWord ++ tailWord_7666586).sum := by decide
  have hdescent : baseEnd_7666586 < baseStart_7666586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666672 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 3]
def baseStart_7666672 : Nat := 118140960795 + 7666672 * 2 ^ 59
def prefixEnd_7666672 : Nat := 4983230072969 + 3 ^ 40 * 7666672 * 2
def baseEnd_7666672 : Nat := 3936687756366933344241623

theorem tailTrace_7666672 : CollatzResearch.WordTrace tailWord_7666672 prefixEnd_7666672 3936687756366933344241623 := by
  unfold tailWord_7666672
  simp only [CollatzResearch.WordTrace]
  refine ⟨139813250040482091089485135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186417666720642788119313513 139813250040482091089485135)
  ·
    refine ⟨209719875060723136634227703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139813250040482091089485135 209719875060723136634227703)
    ·
      refine ⟨314579812591084704951341555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209719875060723136634227703 314579812591084704951341555)
      ·
        refine ⟨471869718886627057427012333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314579812591084704951341555 471869718886627057427012333)
        ·
          refine ⟨176951144582485146535129625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 471869718886627057427012333 176951144582485146535129625)
          ·
            refine ⟨132713358436863859901347219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176951144582485146535129625 132713358436863859901347219)
            ·
              refine ⟨199070037655295789852020829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132713358436863859901347219 199070037655295789852020829)
              ·
                refine ⟨74651264120735921194507811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199070037655295789852020829 74651264120735921194507811)
                ·
                  refine ⟨111976896181103881791761717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74651264120735921194507811 111976896181103881791761717)
                  ·
                    refine ⟨10497834016978488917977661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111976896181103881791761717 10497834016978488917977661)
                    ·
                      refine ⟨3936687756366933344241623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10497834016978488917977661 3936687756366933344241623)
                      ·
                        rfl

theorem cell23_7666672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 3].length) (baseStart_7666672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666672 prefixEnd_7666672 := by exact prefixLift 7666672
  have htrace : WordTrace (prefixWord ++ tailWord_7666672) baseStart_7666672 baseEnd_7666672 := by
    simpa [prefixWord, tailWord_7666672, baseEnd_7666672] using wordTrace_append hprefix tailTrace_7666672
  have hstable : (prefixWord ++ tailWord_7666672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666672).length < 2 ^ (prefixWord ++ tailWord_7666672).sum := by decide
  have hdescent : baseEnd_7666672 < baseStart_7666672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666673 : List Nat := [1, 2, 2, 2, 4, 2, 1, 3, 2, 2, 2]
def baseStart_7666673 : Nat := 118140960795 + 7666673 * 2 ^ 59
def prefixEnd_7666673 : Nat := 4983230072969 + 3 ^ 40 * 7666673 * 2
def baseEnd_7666673 : Nat := 3936688269847587840329119

theorem tailTrace_7666673 : CollatzResearch.WordTrace tailWord_7666673 prefixEnd_7666673 3936688269847587840329119 := by
  unfold tailWord_7666673
  simp only [CollatzResearch.WordTrace]
  refine ⟨279626536553960559349756673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186417691035973706233171115 279626536553960559349756673)
  ·
    refine ⟨209719902415470419512317505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279626536553960559349756673 209719902415470419512317505)
    ·
      refine ⟨157289926811602814634238129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209719902415470419512317505 157289926811602814634238129)
      ·
        refine ⟨117967445108702110975678597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157289926811602814634238129 117967445108702110975678597)
        ·
          refine ⟨22118895957881645807939737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117967445108702110975678597 22118895957881645807939737)
          ·
            refine ⟨16589171968411234355954803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22118895957881645807939737 16589171968411234355954803)
            ·
              refine ⟨24883757952616851533932205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16589171968411234355954803 24883757952616851533932205)
              ·
                refine ⟨9331409232231319325224577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24883757952616851533932205 9331409232231319325224577)
                ·
                  refine ⟨6998556924173489493918433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9331409232231319325224577 6998556924173489493918433)
                  ·
                    refine ⟨5248917693130117120438825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6998556924173489493918433 5248917693130117120438825)
                    ·
                      refine ⟨3936688269847587840329119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5248917693130117120438825 3936688269847587840329119)
                      ·
                        rfl

theorem cell23_7666673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_7666673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666673 prefixEnd_7666673 := by exact prefixLift 7666673
  have htrace : WordTrace (prefixWord ++ tailWord_7666673) baseStart_7666673 baseEnd_7666673 := by
    simpa [prefixWord, tailWord_7666673, baseEnd_7666673] using wordTrace_append hprefix tailTrace_7666673
  have hstable : (prefixWord ++ tailWord_7666673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666673).length < 2 ^ (prefixWord ++ tailWord_7666673).sum := by decide
  have hdescent : baseEnd_7666673 < baseStart_7666673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666677 : List Nat := [1, 3, 5, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_7666677 : Nat := 118140960795 + 7666677 * 2 ^ 59
def prefixEnd_7666677 : Nat := 4983230072969 + 3 ^ 40 * 7666677 * 2
def baseEnd_7666677 : Nat := 3936690323770205824679101

theorem tailTrace_7666677 : CollatzResearch.WordTrace tailWord_7666677 prefixEnd_7666677 3936690323770205824679101 := by
  unfold tailWord_7666677
  simp only [CollatzResearch.WordTrace]
  refine ⟨279626682445946068032902285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186417788297297378688601523 279626682445946068032902285)
  ·
    refine ⟨104860005917229775512338357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279626682445946068032902285 104860005917229775512338357)
    ·
      refine ⟨9830625554740291454281721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104860005917229775512338357 9830625554740291454281721)
      ·
        refine ⟨7372969166055218590711291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9830625554740291454281721 7372969166055218590711291)
        ·
          refine ⟨11059453749082827886066937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7372969166055218590711291 11059453749082827886066937)
          ·
            refine ⟨8294590311812120914550203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11059453749082827886066937 8294590311812120914550203)
            ·
              refine ⟨12441885467718181371825305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8294590311812120914550203 12441885467718181371825305)
              ·
                refine ⟨9331414100788636028868979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12441885467718181371825305 9331414100788636028868979)
                ·
                  refine ⟨13997121151182954043303469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9331414100788636028868979 13997121151182954043303469)
                  ·
                    refine ⟨5248920431693607766238801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13997121151182954043303469 5248920431693607766238801)
                    ·
                      refine ⟨3936690323770205824679101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5248920431693607766238801 3936690323770205824679101)
                      ·
                        rfl

theorem cell23_7666677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_7666677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666677 prefixEnd_7666677 := by exact prefixLift 7666677
  have htrace : WordTrace (prefixWord ++ tailWord_7666677) baseStart_7666677 baseEnd_7666677 := by
    simpa [prefixWord, tailWord_7666677, baseEnd_7666677] using wordTrace_append hprefix tailTrace_7666677
  have hstable : (prefixWord ++ tailWord_7666677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666677).length < 2 ^ (prefixWord ++ tailWord_7666677).sum := by decide
  have hdescent : baseEnd_7666677 < baseStart_7666677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666690 : List Nat := [3, 4, 1, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_7666690 : Nat := 118140960795 + 7666690 * 2 ^ 59
def prefixEnd_7666690 : Nat := 4983230072969 + 3 ^ 40 * 7666690 * 2
def baseEnd_7666690 : Nat := 3936696999018714273816541

theorem tailTrace_7666690 : CollatzResearch.WordTrace tailWord_7666690 prefixEnd_7666690 3936696999018714273816541 := by
  unfold tailWord_7666690
  simp only [CollatzResearch.WordTrace]
  refine ⟨69906789148724742813281381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186418104396599314168750349 69906789148724742813281381)
  ·
    refine ⟨13107522965385889277490259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69906789148724742813281381 13107522965385889277490259)
    ·
      refine ⟨19661284448078833916235389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13107522965385889277490259 19661284448078833916235389)
      ·
        refine ⟨7372981668029562718588271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19661284448078833916235389 7372981668029562718588271)
        ·
          refine ⟨11059472502044344077882407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7372981668029562718588271 11059472502044344077882407)
          ·
            refine ⟨16589208753066516116823611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11059472502044344077882407 16589208753066516116823611)
            ·
              refine ⟨24883813129599774175235417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16589208753066516116823611 24883813129599774175235417)
              ·
                refine ⟨18662859847199830631426563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24883813129599774175235417 18662859847199830631426563)
                ·
                  refine ⟨27994289770799745947139845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18662859847199830631426563 27994289770799745947139845)
                  ·
                    refine ⟨5248929332024952365088721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27994289770799745947139845 5248929332024952365088721)
                    ·
                      refine ⟨3936696999018714273816541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5248929332024952365088721 3936696999018714273816541)
                      ·
                        rfl

theorem cell23_7666690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_7666690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666690 prefixEnd_7666690 := by exact prefixLift 7666690
  have htrace : WordTrace (prefixWord ++ tailWord_7666690) baseStart_7666690 baseEnd_7666690 := by
    simpa [prefixWord, tailWord_7666690, baseEnd_7666690] using wordTrace_append hprefix tailTrace_7666690
  have hstable : (prefixWord ++ tailWord_7666690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666690).length < 2 ^ (prefixWord ++ tailWord_7666690).sum := by decide
  have hdescent : baseEnd_7666690 < baseStart_7666690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666709 : List Nat := [1, 3, 2, 1, 4, 1, 2, 2, 2, 5]
def baseStart_7666709 : Nat := 118140960795 + 7666709 * 2 ^ 59
def prefixEnd_7666709 : Nat := 4983230072969 + 3 ^ 40 * 7666709 * 2
def baseEnd_7666709 : Nat := 1312235585050383233159651

theorem tailTrace_7666709 : CollatzResearch.WordTrace tailWord_7666709 prefixEnd_7666709 1312235585050383233159651 := by
  unfold tailWord_7666709
  simp only [CollatzResearch.WordTrace]
  refine ⟨279627849581830137498067181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186418566387886758332044787 279627849581830137498067181)
  ·
    refine ⟨104860443593186301561775193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279627849581830137498067181 104860443593186301561775193)
    ·
      refine ⟨78645332694889726171331395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104860443593186301561775193 78645332694889726171331395)
      ·
        refine ⟨117967999042334589256997093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78645332694889726171331395 117967999042334589256997093)
        ·
          refine ⟨22118999820437735485686955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117967999042334589256997093 22118999820437735485686955)
          ·
            refine ⟨33178499730656603228530433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22118999820437735485686955 33178499730656603228530433)
            ·
              refine ⟨24883874797992452421397825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33178499730656603228530433 24883874797992452421397825)
              ·
                refine ⟨18662906098494339316048369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24883874797992452421397825 18662906098494339316048369)
                ·
                  refine ⟨13997179573870754487036277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18662906098494339316048369 13997179573870754487036277)
                  ·
                    refine ⟨1312235585050383233159651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13997179573870754487036277 1312235585050383233159651)
                    ·
                      rfl

theorem cell23_7666709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_7666709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666709 prefixEnd_7666709 := by exact prefixLift 7666709
  have htrace : WordTrace (prefixWord ++ tailWord_7666709) baseStart_7666709 baseEnd_7666709 := by
    simpa [prefixWord, tailWord_7666709, baseEnd_7666709] using wordTrace_append hprefix tailTrace_7666709
  have hstable : (prefixWord ++ tailWord_7666709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666709).length < 2 ^ (prefixWord ++ tailWord_7666709).sum := by decide
  have hdescent : baseEnd_7666709 < baseStart_7666709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666752 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 8]
def baseStart_7666752 : Nat := 118140960795 + 7666752 * 2 ^ 59
def prefixEnd_7666752 : Nat := 4983230072969 + 3 ^ 40 * 7666752 * 2
def baseEnd_7666752 : Nat := 437414314979921447915695

theorem tailTrace_7666752 : CollatzResearch.WordTrace tailWord_7666752 prefixEnd_7666752 437414314979921447915695 := by
  unfold tailWord_7666752
  simp only [CollatzResearch.WordTrace]
  refine ⟨139814708960337177920941255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186419611947116237227921673 139814708960337177920941255)
  ·
    refine ⟨209722063440505766881411883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139814708960337177920941255 209722063440505766881411883)
    ·
      refine ⟨314583095160758650322117825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209722063440505766881411883 314583095160758650322117825)
      ·
        refine ⟨235937321370568987741588369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314583095160758650322117825 235937321370568987741588369)
        ·
          refine ⟨176952991027926740806191277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235937321370568987741588369 176952991027926740806191277)
          ·
            refine ⟨66357371635472527802321729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176952991027926740806191277 66357371635472527802321729)
            ·
              refine ⟨49768028726604395851741297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66357371635472527802321729 49768028726604395851741297)
              ·
                refine ⟨37326021544953296888805973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49768028726604395851741297 37326021544953296888805973)
                ·
                  refine ⟨437414314979921447915695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37326021544953296888805973 437414314979921447915695)
                  ·
                    rfl

theorem cell23_7666752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 8].length) (baseStart_7666752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666752 prefixEnd_7666752 := by exact prefixLift 7666752
  have htrace : WordTrace (prefixWord ++ tailWord_7666752) baseStart_7666752 baseEnd_7666752 := by
    simpa [prefixWord, tailWord_7666752, baseEnd_7666752] using wordTrace_append hprefix tailTrace_7666752
  have hstable : (prefixWord ++ tailWord_7666752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666752).length < 2 ^ (prefixWord ++ tailWord_7666752).sum := by decide
  have hdescent : baseEnd_7666752 < baseStart_7666752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666769 : List Nat := [1, 2, 2, 1, 3, 1, 5, 2, 6]
def baseStart_7666769 : Nat := 118140960795 + 7666769 * 2 ^ 59
def prefixEnd_7666769 : Nat := 4983230072969 + 3 ^ 40 * 7666769 * 2
def baseEnd_7666769 : Nat := 437415284887824384969853

theorem tailTrace_7666769 : CollatzResearch.WordTrace tailWord_7666769 prefixEnd_7666769 437415284887824384969853 := by
  unfold tailWord_7666769
  simp only [CollatzResearch.WordTrace]
  refine ⟨279630037961612767745251361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186420025307741845163500907 279630037961612767745251361)
  ·
    refine ⟨209722528471209575808938521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279630037961612767745251361 209722528471209575808938521)
    ·
      refine ⟨157291896353407181856703891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209722528471209575808938521 157291896353407181856703891)
      ·
        refine ⟨235937844530110772785055837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157291896353407181856703891 235937844530110772785055837)
        ·
          refine ⟨88476691698791539794395939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235937844530110772785055837 88476691698791539794395939)
          ·
            refine ⟨132715037548187309691593909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88476691698791539794395939 132715037548187309691593909)
            ·
              refine ⟨12442034770142560283586929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132715037548187309691593909 12442034770142560283586929)
              ·
                refine ⟨9331526077606920212690197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12442034770142560283586929 9331526077606920212690197)
                ·
                  refine ⟨437415284887824384969853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9331526077606920212690197 437415284887824384969853)
                  ·
                    rfl

theorem cell23_7666769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 6].length) (baseStart_7666769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666769 prefixEnd_7666769 := by exact prefixLift 7666769
  have htrace : WordTrace (prefixWord ++ tailWord_7666769) baseStart_7666769 baseEnd_7666769 := by
    simpa [prefixWord, tailWord_7666769, baseEnd_7666769] using wordTrace_append hprefix tailTrace_7666769
  have hstable : (prefixWord ++ tailWord_7666769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666769).length < 2 ^ (prefixWord ++ tailWord_7666769).sum := by decide
  have hdescent : baseEnd_7666769 < baseStart_7666769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666796 : List Nat := [2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 3]
def baseStart_7666796 : Nat := 118140960795 + 7666796 * 2 ^ 59
def prefixEnd_7666796 : Nat := 4983230072969 + 3 ^ 40 * 7666796 * 2
def baseEnd_7666796 : Nat := 3936751427968090859091053

theorem tailTrace_7666796 : CollatzResearch.WordTrace tailWord_7666796 prefixEnd_7666796 3936751427968090859091053 := by
  unfold tailWord_7666796
  simp only [CollatzResearch.WordTrace]
  refine ⟨139815511366257475678242121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186420681821676634237656161 139815511366257475678242121)
  ·
    refine ⟨104861633524693106758681591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139815511366257475678242121 104861633524693106758681591)
    ·
      refine ⟨157292450287039660138022387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104861633524693106758681591 157292450287039660138022387)
      ·
        refine ⟨235938675430559490207033581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157292450287039660138022387 235938675430559490207033581)
        ·
          refine ⟨88477003286459808827637593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235938675430559490207033581 88477003286459808827637593)
          ·
            refine ⟨66357752464844856620728195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88477003286459808827637593 66357752464844856620728195)
            ·
              refine ⟨99536628697267284931092293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66357752464844856620728195 99536628697267284931092293)
              ·
                refine ⟨18663117880737615924579805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99536628697267284931092293 18663117880737615924579805)
                ·
                  refine ⟨6998669205276605971717427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18663117880737615924579805 6998669205276605971717427)
                  ·
                    refine ⟨10498003807914908957576141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6998669205276605971717427 10498003807914908957576141)
                    ·
                      refine ⟨3936751427968090859091053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10498003807914908957576141 3936751427968090859091053)
                      ·
                        rfl

theorem cell23_7666796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 3].length) (baseStart_7666796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666796 prefixEnd_7666796 := by exact prefixLift 7666796
  have htrace : WordTrace (prefixWord ++ tailWord_7666796) baseStart_7666796 baseEnd_7666796 := by
    simpa [prefixWord, tailWord_7666796, baseEnd_7666796] using wordTrace_append hprefix tailTrace_7666796
  have hstable : (prefixWord ++ tailWord_7666796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666796).length < 2 ^ (prefixWord ++ tailWord_7666796).sum := by decide
  have hdescent : baseEnd_7666796 < baseStart_7666796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666830 : List Nat := [4, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3]
def baseStart_7666830 : Nat := 118140960795 + 7666830 * 2 ^ 59
def prefixEnd_7666830 : Nat := 4983230072969 + 3 ^ 40 * 7666830 * 2
def baseEnd_7666830 : Nat := 3936768886310343726065897

theorem tailTrace_7666830 : CollatzResearch.WordTrace tailWord_7666830 prefixEnd_7666830 3936768886310343726065897 := by
  unfold tailWord_7666830
  simp only [CollatzResearch.WordTrace]
  refine ⟨34954032851798971895402743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186421508542927850108814629 34954032851798971895402743)
  ·
    refine ⟨52431049277698457843104115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34954032851798971895402743 52431049277698457843104115)
    ·
      refine ⟨78646573916547686764656173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52431049277698457843104115 78646573916547686764656173)
      ·
        refine ⟨29492465218705382536746065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78646573916547686764656173 29492465218705382536746065)
        ·
          refine ⟨22119348914029036902559549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29492465218705382536746065 22119348914029036902559549)
          ·
            refine ⟨8294755842760888838459831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22119348914029036902559549 8294755842760888838459831)
            ·
              refine ⟨12442133764141333257689747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8294755842760888838459831 12442133764141333257689747)
              ·
                refine ⟨18663200646211999886534621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12442133764141333257689747 18663200646211999886534621)
                ·
                  refine ⟨6998700242329499957450483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18663200646211999886534621 6998700242329499957450483)
                  ·
                    refine ⟨10498050363494249936175725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6998700242329499957450483 10498050363494249936175725)
                    ·
                      refine ⟨3936768886310343726065897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10498050363494249936175725 3936768886310343726065897)
                      ·
                        rfl

theorem cell23_7666830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_7666830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666830 prefixEnd_7666830 := by exact prefixLift 7666830
  have htrace : WordTrace (prefixWord ++ tailWord_7666830) baseStart_7666830 baseEnd_7666830 := by
    simpa [prefixWord, tailWord_7666830, baseEnd_7666830] using wordTrace_append hprefix tailTrace_7666830
  have hstable : (prefixWord ++ tailWord_7666830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666830).length < 2 ^ (prefixWord ++ tailWord_7666830).sum := by decide
  have hdescent : baseEnd_7666830 < baseStart_7666830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666849 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_7666849 : Nat := 118140960795 + 7666849 * 2 ^ 59
def prefixEnd_7666849 : Nat := 4983230072969 + 3 ^ 40 * 7666849 * 2
def baseEnd_7666849 : Nat := 3936778642442779151728309

theorem tailTrace_7666849 : CollatzResearch.WordTrace tailWord_7666849 prefixEnd_7666849 3936778642442779151728309 := by
  unfold tailWord_7666849
  simp only [CollatzResearch.WordTrace]
  refine ⟨279632955801322941408163601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186421970534215294272109067 279632955801322941408163601)
  ·
    refine ⟨209724716850992206056122701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279632955801322941408163601 209724716850992206056122701)
    ·
      refine ⟨78646768819122077271046013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209724716850992206056122701 78646768819122077271046013)
      ·
        refine ⟨29492538307170778976642255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78646768819122077271046013 29492538307170778976642255)
        ·
          refine ⟨44238807460756168464963383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29492538307170778976642255 44238807460756168464963383)
          ·
            refine ⟨66358211191134252697445075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44238807460756168464963383 66358211191134252697445075)
            ·
              refine ⟨99537316786701379046167613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66358211191134252697445075 99537316786701379046167613)
              ·
                refine ⟨37326493795013017142312855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99537316786701379046167613 37326493795013017142312855)
                ·
                  refine ⟨55989740692519525713469283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37326493795013017142312855 55989740692519525713469283)
                  ·
                    refine ⟨83984611038779288570203925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55989740692519525713469283 83984611038779288570203925)
                    ·
                      refine ⟨3936778642442779151728309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83984611038779288570203925 3936778642442779151728309)
                      ·
                        rfl

theorem cell23_7666849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_7666849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666849 prefixEnd_7666849 := by exact prefixLift 7666849
  have htrace : WordTrace (prefixWord ++ tailWord_7666849) baseStart_7666849 baseEnd_7666849 := by
    simpa [prefixWord, tailWord_7666849, baseEnd_7666849] using wordTrace_append hprefix tailTrace_7666849
  have hstable : (prefixWord ++ tailWord_7666849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666849).length < 2 ^ (prefixWord ++ tailWord_7666849).sum := by decide
  have hdescent : baseEnd_7666849 < baseStart_7666849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666850 : List Nat := [3, 3, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_7666850 : Nat := 118140960795 + 7666850 * 2 ^ 59
def prefixEnd_7666850 : Nat := 4983230072969 + 3 ^ 40 * 7666850 * 2
def baseEnd_7666850 : Nat := 1312259718641144549271935

theorem tailTrace_7666850 : CollatzResearch.WordTrace tailWord_7666850 prefixEnd_7666850 1312259718641144549271935 := by
  unfold tailWord_7666850
  simp only [CollatzResearch.WordTrace]
  refine ⟨69908248068579829644737501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186421994849546212385966669 69908248068579829644737501)
  ·
    refine ⟨26215593025717436116776563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69908248068579829644737501 26215593025717436116776563)
    ·
      refine ⟨39323389538576154175164845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26215593025717436116776563 39323389538576154175164845)
      ·
        refine ⟨14746271076966057815686817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39323389538576154175164845 14746271076966057815686817)
        ·
          refine ⟨11059703307724543361765113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14746271076966057815686817 11059703307724543361765113)
          ·
            refine ⟨8294777480793407521323835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11059703307724543361765113 8294777480793407521323835)
            ·
              refine ⟨12442166221190111281985753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8294777480793407521323835 12442166221190111281985753)
              ·
                refine ⟨9331624665892583461489315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12442166221190111281985753 9331624665892583461489315)
                ·
                  refine ⟨13997436998838875192233973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9331624665892583461489315 13997436998838875192233973)
                  ·
                    refine ⟨1312259718641144549271935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13997436998838875192233973 1312259718641144549271935)
                    ·
                      rfl

theorem cell23_7666850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_7666850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666850 prefixEnd_7666850 := by exact prefixLift 7666850
  have htrace : WordTrace (prefixWord ++ tailWord_7666850) baseStart_7666850 baseEnd_7666850 := by
    simpa [prefixWord, tailWord_7666850, baseEnd_7666850] using wordTrace_append hprefix tailTrace_7666850
  have hstable : (prefixWord ++ tailWord_7666850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666850).length < 2 ^ (prefixWord ++ tailWord_7666850).sum := by decide
  have hdescent : baseEnd_7666850 < baseStart_7666850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666853 : List Nat := [1, 3, 1, 2, 1, 6, 1, 2, 1, 1, 4]
def baseStart_7666853 : Nat := 118140960795 + 7666853 * 2 ^ 59
def prefixEnd_7666853 : Nat := 4983230072969 + 3 ^ 40 * 7666853 * 2
def baseEnd_7666853 : Nat := 3936780696365397136078291

theorem tailTrace_7666853 : CollatzResearch.WordTrace tailWord_7666853 prefixEnd_7666853 3936780696365397136078291 := by
  unfold tailWord_7666853
  simp only [CollatzResearch.WordTrace]
  refine ⟨279633101693308450091309213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186422067795538966727539475 279633101693308450091309213)
  ·
    refine ⟨104862413134990668784240955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279633101693308450091309213 104862413134990668784240955)
    ·
      refine ⟨157293619702486003176361433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104862413134990668784240955 157293619702486003176361433)
      ·
        refine ⟨117970214776864502382271075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157293619702486003176361433 117970214776864502382271075)
        ·
          refine ⟨176955322165296753573406613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117970214776864502382271075 176955322165296753573406613)
          ·
            refine ⟨8294780726498285323753435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 176955322165296753573406613 8294780726498285323753435)
            ·
              refine ⟨12442171089747427985630153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8294780726498285323753435 12442171089747427985630153)
              ·
                refine ⟨9331628317310570989222615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12442171089747427985630153 9331628317310570989222615)
                ·
                  refine ⟨13997442475965856483833923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9331628317310570989222615 13997442475965856483833923)
                  ·
                    refine ⟨20996163713948784725750885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13997442475965856483833923 20996163713948784725750885)
                    ·
                      refine ⟨3936780696365397136078291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20996163713948784725750885 3936780696365397136078291)
                      ·
                        rfl

theorem cell23_7666853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_7666853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666853 prefixEnd_7666853 := by exact prefixLift 7666853
  have htrace : WordTrace (prefixWord ++ tailWord_7666853) baseStart_7666853 baseEnd_7666853 := by
    simpa [prefixWord, tailWord_7666853, baseEnd_7666853] using wordTrace_append hprefix tailTrace_7666853
  have hstable : (prefixWord ++ tailWord_7666853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666853).length < 2 ^ (prefixWord ++ tailWord_7666853).sum := by decide
  have hdescent : baseEnd_7666853 < baseStart_7666853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666866 : List Nat := [3, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_7666866 : Nat := 118140960795 + 7666866 * 2 ^ 59
def prefixEnd_7666866 : Nat := 4983230072969 + 3 ^ 40 * 7666866 * 2
def baseEnd_7666866 : Nat := 3936787371613905585215731

theorem tailTrace_7666866 : CollatzResearch.WordTrace tailWord_7666866 prefixEnd_7666866 3936787371613905585215731 := by
  unfold tailWord_7666866
  simp only [CollatzResearch.WordTrace]
  refine ⟨69908393960565338327883113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186422383894840902207688301 69908393960565338327883113)
  ·
    refine ⟨52431295470424003745912335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69908393960565338327883113 52431295470424003745912335)
    ·
      refine ⟨78646943205636005618868503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52431295470424003745912335 78646943205636005618868503)
      ·
        refine ⟨117970414808454008428302755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78646943205636005618868503 117970414808454008428302755)
        ·
          refine ⟨176955622212681012642454133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117970414808454008428302755 176955622212681012642454133)
          ·
            refine ⟨16589589582438844935230075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176955622212681012642454133 16589589582438844935230075)
            ·
              refine ⟨24884384373658267402845113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16589589582438844935230075 24884384373658267402845113)
              ·
                refine ⟨18663288280243700552133835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24884384373658267402845113 18663288280243700552133835)
                ·
                  refine ⟨27994932420365550828200753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18663288280243700552133835 27994932420365550828200753)
                  ·
                    refine ⟨20996199315274163121150565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27994932420365550828200753 20996199315274163121150565)
                    ·
                      refine ⟨3936787371613905585215731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20996199315274163121150565 3936787371613905585215731)
                      ·
                        rfl

theorem cell23_7666866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_7666866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666866 prefixEnd_7666866 := by exact prefixLift 7666866
  have htrace : WordTrace (prefixWord ++ tailWord_7666866) baseStart_7666866 baseEnd_7666866 := by
    simpa [prefixWord, tailWord_7666866, baseEnd_7666866] using wordTrace_append hprefix tailTrace_7666866
  have hstable : (prefixWord ++ tailWord_7666866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666866).length < 2 ^ (prefixWord ++ tailWord_7666866).sum := by decide
  have hdescent : baseEnd_7666866 < baseStart_7666866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666900 : List Nat := [2, 4, 1, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_7666900 : Nat := 118140960795 + 7666900 * 2 ^ 59
def prefixEnd_7666900 : Nat := 4983230072969 + 3 ^ 40 * 7666900 * 2
def baseEnd_7666900 : Nat := 3936804829956158452190575

theorem tailTrace_7666900 : CollatzResearch.WordTrace tailWord_7666900 prefixEnd_7666900 3936804829956158452190575 := by
  unfold tailWord_7666900
  simp only [CollatzResearch.WordTrace]
  refine ⟨139817407962069088559135077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186423210616092118078846769 139817407962069088559135077)
  ·
    refine ⟨26215763992887954104837827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139817407962069088559135077 26215763992887954104837827)
    ·
      refine ⟨39323645989331931157256741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26215763992887954104837827 39323645989331931157256741)
      ·
        refine ⟨7373183622999737091985639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39323645989331931157256741 7373183622999737091985639)
        ·
          refine ⟨11059775434499605637978459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7373183622999737091985639 11059775434499605637978459)
          ·
            refine ⟨16589663151749408456967689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11059775434499605637978459 16589663151749408456967689)
            ·
              refine ⟨12442247363812056342725767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16589663151749408456967689 12442247363812056342725767)
              ·
                refine ⟨18663371045718084514088651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12442247363812056342725767 18663371045718084514088651)
                ·
                  refine ⟨27995056568577126771132977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18663371045718084514088651 27995056568577126771132977)
                  ·
                    refine ⟨20996292426432845078349733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27995056568577126771132977 20996292426432845078349733)
                    ·
                      refine ⟨3936804829956158452190575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20996292426432845078349733 3936804829956158452190575)
                      ·
                        rfl

theorem cell23_7666900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_7666900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666900 prefixEnd_7666900 := by exact prefixLift 7666900
  have htrace : WordTrace (prefixWord ++ tailWord_7666900) baseStart_7666900 baseEnd_7666900 := by
    simpa [prefixWord, tailWord_7666900, baseEnd_7666900] using wordTrace_append hprefix tailTrace_7666900
  have hstable : (prefixWord ++ tailWord_7666900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666900).length < 2 ^ (prefixWord ++ tailWord_7666900).sum := by decide
  have hdescent : baseEnd_7666900 < baseStart_7666900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666903 : List Nat := [1, 1, 3, 2, 1, 2, 4, 3, 2, 1, 3]
def baseStart_7666903 : Nat := 118140960795 + 7666903 * 2 ^ 59
def prefixEnd_7666903 : Nat := 4983230072969 + 3 ^ 40 * 7666903 * 2
def baseEnd_7666903 : Nat := 3936806370398121940453061

theorem tailTrace_7666903 : CollatzResearch.WordTrace tailWord_7666903 prefixEnd_7666903 3936806370398121940453061 := by
  unfold tailWord_7666903
  simp only [CollatzResearch.WordTrace]
  refine ⟨279634925343127308630629363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186423283562084872420419575 279634925343127308630629363)
  ·
    refine ⟨419452388014690962945944045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279634925343127308630629363 419452388014690962945944045)
    ·
      refine ⟨157294645505509111104729017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419452388014690962945944045 157294645505509111104729017)
      ·
        refine ⟨117970984129131833328546763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157294645505509111104729017 117970984129131833328546763)
        ·
          refine ⟨176956476193697749992820145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117970984129131833328546763 176956476193697749992820145)
          ·
            refine ⟨132717357145273312494615109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176956476193697749992820145 132717357145273312494615109)
            ·
              refine ⟨24884504464738746092740333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132717357145273312494615109 24884504464738746092740333)
              ·
                refine ⟨9331689174277029784777625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24884504464738746092740333 9331689174277029784777625)
                ·
                  refine ⟨6998766880707772338583219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9331689174277029784777625 6998766880707772338583219)
                  ·
                    refine ⟨10498150321061658507874829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6998766880707772338583219 10498150321061658507874829)
                    ·
                      refine ⟨3936806370398121940453061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10498150321061658507874829 3936806370398121940453061)
                      ·
                        rfl

theorem cell23_7666903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_7666903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666903 prefixEnd_7666903 := by exact prefixLift 7666903
  have htrace : WordTrace (prefixWord ++ tailWord_7666903) baseStart_7666903 baseEnd_7666903 := by
    simpa [prefixWord, tailWord_7666903, baseEnd_7666903] using wordTrace_append hprefix tailTrace_7666903
  have hstable : (prefixWord ++ tailWord_7666903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666903).length < 2 ^ (prefixWord ++ tailWord_7666903).sum := by decide
  have hdescent : baseEnd_7666903 < baseStart_7666903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666913 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 3, 3, 2]
def baseStart_7666913 : Nat := 118140960795 + 7666913 * 2 ^ 59
def prefixEnd_7666913 : Nat := 4983230072969 + 3 ^ 40 * 7666913 * 2
def baseEnd_7666913 : Nat := 3936811505204666901328015

theorem tailTrace_7666913 : CollatzResearch.WordTrace tailWord_7666913 prefixEnd_7666913 3936811505204666901328015 := by
  unfold tailWord_7666913
  simp only [CollatzResearch.WordTrace]
  refine ⟨279635290073091080338493393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186423526715394053558995595 279635290073091080338493393)
  ·
    refine ⟨209726467554818310253870045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279635290073091080338493393 209726467554818310253870045)
    ·
      refine ⟨78647425333056866345201267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209726467554818310253870045 78647425333056866345201267)
      ·
        refine ⟨117971137999585299517801901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78647425333056866345201267 117971137999585299517801901)
        ·
          refine ⟨44239176749844487319175713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117971137999585299517801901 44239176749844487319175713)
          ·
            refine ⟨33179382562383365489381785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44239176749844487319175713 33179382562383365489381785)
            ·
              refine ⟨24884536921787524117036339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33179382562383365489381785 24884536921787524117036339)
              ·
                refine ⟨37326805382681286175554509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24884536921787524117036339 37326805382681286175554509)
                ·
                  refine ⟨13997552018505482315832941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37326805382681286175554509 13997552018505482315832941)
                  ·
                    refine ⟨5249082006939555868437353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13997552018505482315832941 5249082006939555868437353)
                    ·
                      refine ⟨3936811505204666901328015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5249082006939555868437353 3936811505204666901328015)
                      ·
                        rfl

theorem cell23_7666913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_7666913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666913 prefixEnd_7666913 := by exact prefixLift 7666913
  have htrace : WordTrace (prefixWord ++ tailWord_7666913) baseStart_7666913 baseEnd_7666913 := by
    simpa [prefixWord, tailWord_7666913, baseEnd_7666913] using wordTrace_append hprefix tailTrace_7666913
  have hstable : (prefixWord ++ tailWord_7666913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666913).length < 2 ^ (prefixWord ++ tailWord_7666913).sum := by decide
  have hdescent : baseEnd_7666913 < baseStart_7666913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666929 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 1, 3, 5]
def baseStart_7666929 : Nat := 118140960795 + 7666929 * 2 ^ 59
def prefixEnd_7666929 : Nat := 4983230072969 + 3 ^ 40 * 7666929 * 2
def baseEnd_7666929 : Nat := 3936819720895138838727941

theorem tailTrace_7666929 : CollatzResearch.WordTrace tailWord_7666929 prefixEnd_7666929 3936819720895138838727941 := by
  unfold tailWord_7666929
  simp only [CollatzResearch.WordTrace]
  refine ⟨279635873641033115071075841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186423915760688743380717227 279635873641033115071075841)
  ·
    refine ⟨209726905230774836303306881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279635873641033115071075841 209726905230774836303306881)
    ·
      refine ⟨157295178923081127227480161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209726905230774836303306881 157295178923081127227480161)
      ·
        refine ⟨117971384192310845420610121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157295178923081127227480161 117971384192310845420610121)
        ·
          refine ⟨88478538144233134065457591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117971384192310845420610121 88478538144233134065457591)
          ·
            refine ⟨132717807216349701098186387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88478538144233134065457591 132717807216349701098186387)
            ·
              refine ⟨199076710824524551647279581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132717807216349701098186387 199076710824524551647279581)
              ·
                refine ⟨74653766559196706867729843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199076710824524551647279581 74653766559196706867729843)
                ·
                  refine ⟨111980649838795060301594765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74653766559196706867729843 111980649838795060301594765)
                  ·
                    refine ⟨41992743689548147613098037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111980649838795060301594765 41992743689548147613098037)
                    ·
                      refine ⟨3936819720895138838727941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41992743689548147613098037 3936819720895138838727941)
                      ·
                        rfl

theorem cell23_7666929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_7666929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666929 prefixEnd_7666929 := by exact prefixLift 7666929
  have htrace : WordTrace (prefixWord ++ tailWord_7666929) baseStart_7666929 baseEnd_7666929 := by
    simpa [prefixWord, tailWord_7666929, baseEnd_7666929] using wordTrace_append hprefix tailTrace_7666929
  have hstable : (prefixWord ++ tailWord_7666929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666929).length < 2 ^ (prefixWord ++ tailWord_7666929).sum := by decide
  have hdescent : baseEnd_7666929 < baseStart_7666929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666956 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 2, 2, 4]
def baseStart_7666956 : Nat := 118140960795 + 7666956 * 2 ^ 59
def prefixEnd_7666956 : Nat := 4983230072969 + 3 ^ 40 * 7666956 * 2
def baseEnd_7666956 : Nat := 3936833584872810233090317

theorem tailTrace_7666956 : CollatzResearch.WordTrace tailWord_7666956 prefixEnd_7666956 3936833584872810233090317 := by
  unfold tailWord_7666956
  simp only [CollatzResearch.WordTrace]
  refine ⟨139818429205967649341154361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186424572274623532454872481 139818429205967649341154361)
  ·
    refine ⟨104863821904475737005865771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139818429205967649341154361 104863821904475737005865771)
    ·
      refine ⟨157295732856713605508798657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104863821904475737005865771 157295732856713605508798657)
      ·
        refine ⟨117971799642535204131598993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157295732856713605508798657 117971799642535204131598993)
        ·
          refine ⟨88478849731901403098699245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117971799642535204131598993 88478849731901403098699245)
          ·
            refine ⟨33179568649463026162012217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88478849731901403098699245 33179568649463026162012217)
            ·
              refine ⟨24884676487097269621509163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33179568649463026162012217 24884676487097269621509163)
              ·
                refine ⟨37327014730645904432263745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24884676487097269621509163 37327014730645904432263745)
                ·
                  refine ⟨27995261047984428324197809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37327014730645904432263745 27995261047984428324197809)
                  ·
                    refine ⟨20996445785988321243148357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27995261047984428324197809 20996445785988321243148357)
                    ·
                      refine ⟨3936833584872810233090317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20996445785988321243148357 3936833584872810233090317)
                      ·
                        rfl

theorem cell23_7666956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_7666956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666956 prefixEnd_7666956 := by exact prefixLift 7666956
  have htrace : WordTrace (prefixWord ++ tailWord_7666956) baseStart_7666956 baseEnd_7666956 := by
    simpa [prefixWord, tailWord_7666956, baseEnd_7666956] using wordTrace_append hprefix tailTrace_7666956
  have hstable : (prefixWord ++ tailWord_7666956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666956).length < 2 ^ (prefixWord ++ tailWord_7666956).sum := by decide
  have hdescent : baseEnd_7666956 < baseStart_7666956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666999 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 8]
def baseStart_7666999 : Nat := 118140960795 + 7666999 * 2 ^ 59
def prefixEnd_7666999 : Nat := 4983230072969 + 3 ^ 40 * 7666999 * 2
def baseEnd_7666999 : Nat := 3936855664540953564852619

theorem tailTrace_7666999 : CollatzResearch.WordTrace tailWord_7666999 prefixEnd_7666999 3936855664540953564852619 := by
  unfold tailWord_7666999
  simp only [CollatzResearch.WordTrace]
  refine ⟨279638426750779517026124051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186425617833853011350749367 279638426750779517026124051)
  ·
    refine ⟨419457640126169275539186077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279638426750779517026124051 419457640126169275539186077)
    ·
      refine ⟨157296615047313478327194779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419457640126169275539186077 157296615047313478327194779)
      ·
        refine ⟨235944922570970217490792169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157296615047313478327194779 235944922570970217490792169)
        ·
          refine ⟨176958691928227663118094127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235944922570970217490792169 176958691928227663118094127)
          ·
            refine ⟨265438037892341494677141191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176958691928227663118094127 265438037892341494677141191)
            ·
              refine ⟨398157056838512242015711787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265438037892341494677141191 398157056838512242015711787)
              ·
                refine ⟨597235585257768363023567681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398157056838512242015711787 597235585257768363023567681)
                ·
                  refine ⟨447926688943326272267675761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597235585257768363023567681 447926688943326272267675761)
                  ·
                    refine ⟨335945016707494704200756821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 447926688943326272267675761 335945016707494704200756821)
                    ·
                      refine ⟨3936855664540953564852619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 335945016707494704200756821 3936855664540953564852619)
                      ·
                        rfl

theorem cell23_7666999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_7666999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7666999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7666999 prefixEnd_7666999 := by exact prefixLift 7666999
  have htrace : WordTrace (prefixWord ++ tailWord_7666999) baseStart_7666999 baseEnd_7666999 := by
    simpa [prefixWord, tailWord_7666999, baseEnd_7666999] using wordTrace_append hprefix tailTrace_7666999
  have hstable : (prefixWord ++ tailWord_7666999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666999).length < 2 ^ (prefixWord ++ tailWord_7666999).sum := by decide
  have hdescent : baseEnd_7666999 < baseStart_7666999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667016 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_7667016 : Nat := 118140960795 + 7667016 * 2 ^ 59
def prefixEnd_7667016 : Nat := 4983230072969 + 3 ^ 40 * 7667016 * 2
def baseEnd_7667016 : Nat := 3936864393712079998340041

theorem tailTrace_7667016 : CollatzResearch.WordTrace tailWord_7667016 prefixEnd_7667016 3936864393712079998340041 := by
  unfold tailWord_7667016
  simp only [CollatzResearch.WordTrace]
  refine ⟨139819523395858964464746451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186426031194478619286328601 139819523395858964464746451)
  ·
    refine ⟨209729285093788446697119677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139819523395858964464746451 209729285093788446697119677)
    ·
      refine ⟨78648481910170667511419879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209729285093788446697119677 78648481910170667511419879)
      ·
        refine ⟨117972722865256001267129819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78648481910170667511419879 117972722865256001267129819)
        ·
          refine ⟨176959084297884001900694729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117972722865256001267129819 176959084297884001900694729)
          ·
            refine ⟨132719313223413001425521047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176959084297884001900694729 132719313223413001425521047)
            ·
              refine ⟨199078969835119502138281571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132719313223413001425521047 199078969835119502138281571)
              ·
                refine ⟨298618454752679253207422357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199078969835119502138281571 298618454752679253207422357)
                ·
                  refine ⟨13997740066531839994097923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 298618454752679253207422357 13997740066531839994097923)
                  ·
                    refine ⟨20996610099797759991146885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13997740066531839994097923 20996610099797759991146885)
                    ·
                      refine ⟨3936864393712079998340041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20996610099797759991146885 3936864393712079998340041)
                      ·
                        rfl

theorem cell23_7667016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_7667016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667016 prefixEnd_7667016 := by exact prefixLift 7667016
  have htrace : WordTrace (prefixWord ++ tailWord_7667016) baseStart_7667016 baseEnd_7667016 := by
    simpa [prefixWord, tailWord_7667016, baseEnd_7667016] using wordTrace_append hprefix tailTrace_7667016
  have hstable : (prefixWord ++ tailWord_7667016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667016).length < 2 ^ (prefixWord ++ tailWord_7667016).sum := by decide
  have hdescent : baseEnd_7667016 < baseStart_7667016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667019 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 9]
def baseStart_7667019 : Nat := 118140960795 + 7667019 * 2 ^ 59
def prefixEnd_7667019 : Nat := 4983230072969 + 3 ^ 40 * 7667019 * 2
def baseEnd_7667019 : Nat := 3936865934154043486602527

theorem tailTrace_7667019 : CollatzResearch.WordTrace tailWord_7667019 prefixEnd_7667019 3936865934154043486602527 := by
  unfold tailWord_7667019
  simp only [CollatzResearch.WordTrace]
  refine ⟨279639156210707060441852111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186426104140471373627901407 279639156210707060441852111)
  ·
    refine ⟨419458734316060590662778167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279639156210707060441852111 419458734316060590662778167)
    ·
      refine ⟨629188101474090885994167251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419458734316060590662778167 629188101474090885994167251)
      ·
        refine ⟨943782152211136328991250877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629188101474090885994167251 943782152211136328991250877)
        ·
          refine ⟨353918307079176123371719079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 943782152211136328991250877 353918307079176123371719079)
          ·
            refine ⟨530877460618764185057578619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353918307079176123371719079 530877460618764185057578619)
            ·
              refine ⟨796316190928146277586367929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530877460618764185057578619 796316190928146277586367929)
              ·
                refine ⟨597237143196109708189775947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796316190928146277586367929 597237143196109708189775947)
                ·
                  refine ⟨895855714794164562284663921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 597237143196109708189775947 895855714794164562284663921)
                  ·
                    refine ⟨671891786095623421713497941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 895855714794164562284663921 671891786095623421713497941)
                    ·
                      refine ⟨3936865934154043486602527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 671891786095623421713497941 3936865934154043486602527)
                      ·
                        rfl

theorem cell23_7667019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 9].length) (baseStart_7667019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667019 prefixEnd_7667019 := by exact prefixLift 7667019
  have htrace : WordTrace (prefixWord ++ tailWord_7667019) baseStart_7667019 baseEnd_7667019 := by
    simpa [prefixWord, tailWord_7667019, baseEnd_7667019] using wordTrace_append hprefix tailTrace_7667019
  have hstable : (prefixWord ++ tailWord_7667019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667019).length < 2 ^ (prefixWord ++ tailWord_7667019).sum := by decide
  have hdescent : baseEnd_7667019 < baseStart_7667019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667116 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 3, 6]
def baseStart_7667116 : Nat := 118140960795 + 7667116 * 2 ^ 59
def prefixEnd_7667116 : Nat := 4983230072969 + 3 ^ 40 * 7667116 * 2
def baseEnd_7667116 : Nat := 1312305247259176535696527

theorem tailTrace_7667116 : CollatzResearch.WordTrace tailWord_7667116 prefixEnd_7667116 1312305247259176535696527 := by
  unfold tailWord_7667116
  simp only [CollatzResearch.WordTrace]
  refine ⟨139821347045677823004066601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186428462727570430672088801 139821347045677823004066601)
  ·
    refine ⟨104866010284258367253049951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139821347045677823004066601 104866010284258367253049951)
    ·
      refine ⟨157299015426387550879574927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104866010284258367253049951 157299015426387550879574927)
      ·
        refine ⟨235948523139581326319362391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157299015426387550879574927 235948523139581326319362391)
        ·
          refine ⟨353922784709371989479043587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235948523139581326319362391 353922784709371989479043587)
          ·
            refine ⟨530884177064057984218565381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353922784709371989479043587 530884177064057984218565381)
            ·
              refine ⟨99540783199510872040981009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 530884177064057984218565381 99540783199510872040981009)
              ·
                refine ⟨74655587399633154030735757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99540783199510872040981009 74655587399633154030735757)
                ·
                  refine ⟨27995845274862432761525909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74655587399633154030735757 27995845274862432761525909)
                  ·
                    refine ⟨1312305247259176535696527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27995845274862432761525909 1312305247259176535696527)
                    ·
                      rfl

theorem cell23_7667116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_7667116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667116 prefixEnd_7667116 := by exact prefixLift 7667116
  have htrace : WordTrace (prefixWord ++ tailWord_7667116) baseStart_7667116 baseEnd_7667116 := by
    simpa [prefixWord, tailWord_7667116, baseEnd_7667116] using wordTrace_append hprefix tailTrace_7667116
  have hstable : (prefixWord ++ tailWord_7667116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667116).length < 2 ^ (prefixWord ++ tailWord_7667116).sum := by decide
  have hdescent : baseEnd_7667116 < baseStart_7667116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667117 : List Nat := [1, 5, 2, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_7667117 : Nat := 118140960795 + 7667117 * 2 ^ 59
def prefixEnd_7667117 : Nat := 4983230072969 + 3 ^ 40 * 7667117 * 2
def baseEnd_7667117 : Nat := 3936916255258184103177077

theorem tailTrace_7667117 : CollatzResearch.WordTrace tailWord_7667117 prefixEnd_7667117 3936916255258184103177077 := by
  unfold tailWord_7667117
  simp only [CollatzResearch.WordTrace]
  refine ⟨279642730564352023178919605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186428487042901348785946403 279642730564352023178919605)
  ·
    refine ⟨26216505990408002173023713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279642730564352023178919605 26216505990408002173023713)
    ·
      refine ⟨19662379492806001629767785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26216505990408002173023713 19662379492806001629767785)
      ·
        refine ⟨14746784619604501222325839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19662379492806001629767785 14746784619604501222325839)
        ·
          refine ⟨22120176929406751833488759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14746784619604501222325839 22120176929406751833488759)
          ·
            refine ⟨33180265394110127750233139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22120176929406751833488759 33180265394110127750233139)
            ·
              refine ⟨49770398091165191625349709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33180265394110127750233139 49770398091165191625349709)
              ·
                refine ⟨18663899284186946859506141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49770398091165191625349709 18663899284186946859506141)
                ·
                  refine ⟨6998962231570105072314803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18663899284186946859506141 6998962231570105072314803)
                  ·
                    refine ⟨10498443347355157608472205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6998962231570105072314803 10498443347355157608472205)
                    ·
                      refine ⟨3936916255258184103177077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10498443347355157608472205 3936916255258184103177077)
                      ·
                        rfl

theorem cell23_7667117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_7667117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667117 prefixEnd_7667117 := by exact prefixLift 7667117
  have htrace : WordTrace (prefixWord ++ tailWord_7667117) baseStart_7667117 baseEnd_7667117 := by
    simpa [prefixWord, tailWord_7667117, baseEnd_7667117] using wordTrace_append hprefix tailTrace_7667117
  have hstable : (prefixWord ++ tailWord_7667117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667117).length < 2 ^ (prefixWord ++ tailWord_7667117).sum := by decide
  have hdescent : baseEnd_7667117 < baseStart_7667117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667160 : List Nat := [2, 1, 2, 2, 2, 1, 4, 3, 1, 2, 3]
def baseStart_7667160 : Nat := 118140960795 + 7667160 * 2 ^ 59
def prefixEnd_7667160 : Nat := 4983230072969 + 3 ^ 40 * 7667160 * 2
def baseEnd_7667160 : Nat := 3936938334926327434939379

theorem tailTrace_7667160 : CollatzResearch.WordTrace tailWord_7667160 prefixEnd_7667160 3936938334926327434939379 := by
  unfold tailWord_7667160
  simp only [CollatzResearch.WordTrace]
  refine ⟨139822149451598120761367467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186429532602130827681823289 139822149451598120761367467)
  ·
    refine ⟨209733224177397181142051201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139822149451598120761367467 209733224177397181142051201)
    ·
      refine ⟨157299918133047885856538401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209733224177397181142051201 157299918133047885856538401)
      ·
        refine ⟨117974938599785914392403801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157299918133047885856538401 117974938599785914392403801)
        ·
          refine ⟨88481203949839435794302851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117974938599785914392403801 88481203949839435794302851)
          ·
            refine ⟨132721805924759153691454277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88481203949839435794302851 132721805924759153691454277)
            ·
              refine ⟨24885338610892341317147677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132721805924759153691454277 24885338610892341317147677)
              ·
                refine ⟨9332001979084627993930379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24885338610892341317147677 9332001979084627993930379)
                ·
                  refine ⟨13998002968626941990895569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9332001979084627993930379 13998002968626941990895569)
                  ·
                    refine ⟨10498502226470206493171677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13998002968626941990895569 10498502226470206493171677)
                    ·
                      refine ⟨3936938334926327434939379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10498502226470206493171677 3936938334926327434939379)
                      ·
                        rfl

theorem cell23_7667160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_7667160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667160 prefixEnd_7667160 := by exact prefixLift 7667160
  have htrace : WordTrace (prefixWord ++ tailWord_7667160) baseStart_7667160 baseEnd_7667160 := by
    simpa [prefixWord, tailWord_7667160, baseEnd_7667160] using wordTrace_append hprefix tailTrace_7667160
  have hstable : (prefixWord ++ tailWord_7667160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667160).length < 2 ^ (prefixWord ++ tailWord_7667160).sum := by decide
  have hdescent : baseEnd_7667160 < baseStart_7667160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667224 : List Nat := [2, 1, 2, 3, 4, 1, 2, 2, 2, 1, 3]
def baseStart_7667224 : Nat := 118140960795 + 7667224 * 2 ^ 59
def prefixEnd_7667224 : Nat := 4983230072969 + 3 ^ 40 * 7667224 * 2
def baseEnd_7667224 : Nat := 3936971197688215184539085

theorem tailTrace_7667224 : CollatzResearch.WordTrace tailWord_7667224 prefixEnd_7667224 3936971197688215184539085 := by
  unfold tailWord_7667224
  simp only [CollatzResearch.WordTrace]
  refine ⟨139823316587482190226532363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186431088783309586968709817 139823316587482190226532363)
  ·
    refine ⟨209734974881223285339798545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139823316587482190226532363 209734974881223285339798545)
    ·
      refine ⟨157301231160917464004848909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209734974881223285339798545 157301231160917464004848909)
      ·
        refine ⟨58987961685344049001818341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157301231160917464004848909 58987961685344049001818341)
        ·
          refine ⟨11060242816002009187840939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58987961685344049001818341 11060242816002009187840939)
          ·
            refine ⟨16590364224003013781761409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11060242816002009187840939 16590364224003013781761409)
            ·
              refine ⟨12442773168002260336321057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16590364224003013781761409 12442773168002260336321057)
              ·
                refine ⟨9332079876001695252240793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12442773168002260336321057 9332079876001695252240793)
                ·
                  refine ⟨6999059907001271439180595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9332079876001695252240793 6999059907001271439180595)
                  ·
                    refine ⟨10498589860501907158770893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6999059907001271439180595 10498589860501907158770893)
                    ·
                      refine ⟨3936971197688215184539085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10498589860501907158770893 3936971197688215184539085)
                      ·
                        rfl

theorem cell23_7667224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_7667224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667224 prefixEnd_7667224 := by exact prefixLift 7667224
  have htrace : WordTrace (prefixWord ++ tailWord_7667224) baseStart_7667224 baseEnd_7667224 := by
    simpa [prefixWord, tailWord_7667224, baseEnd_7667224] using wordTrace_append hprefix tailTrace_7667224
  have hstable : (prefixWord ++ tailWord_7667224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667224).length < 2 ^ (prefixWord ++ tailWord_7667224).sum := by decide
  have hdescent : baseEnd_7667224 < baseStart_7667224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667253 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 9]
def baseStart_7667253 : Nat := 118140960795 + 7667253 * 2 ^ 59
def prefixEnd_7667253 : Nat := 4983230072969 + 3 ^ 40 * 7667253 * 2
def baseEnd_7667253 : Nat := 437442898736355063452939

theorem tailTrace_7667253 : CollatzResearch.WordTrace tailWord_7667253 prefixEnd_7667253 437442898736355063452939 := by
  unfold tailWord_7667253
  simp only [CollatzResearch.WordTrace]
  refine ⟨279647690891859318405870413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186431793927906212270580275 279647690891859318405870413)
  ·
    refine ⟨104867884084447244402201405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279647690891859318405870413 104867884084447244402201405)
    ·
      refine ⟨39325456531667716650825527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104867884084447244402201405 39325456531667716650825527)
      ·
        refine ⟨58988184797501574976238291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39325456531667716650825527 58988184797501574976238291)
        ·
          refine ⟨88482277196252362464357437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58988184797501574976238291 88482277196252362464357437)
          ·
            refine ⟨33180853948594635924134039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88482277196252362464357437 33180853948594635924134039)
            ·
              refine ⟨49771280922891953886201059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33180853948594635924134039 49771280922891953886201059)
              ·
                refine ⟨74656921384337930829301589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49771280922891953886201059 74656921384337930829301589)
                ·
                  refine ⟨437442898736355063452939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74656921384337930829301589 437442898736355063452939)
                  ·
                    rfl

theorem cell23_7667253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 9].length) (baseStart_7667253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667253 prefixEnd_7667253 := by exact prefixLift 7667253
  have htrace : WordTrace (prefixWord ++ tailWord_7667253) baseStart_7667253 baseEnd_7667253 := by
    simpa [prefixWord, tailWord_7667253, baseEnd_7667253] using wordTrace_append hprefix tailTrace_7667253
  have hstable : (prefixWord ++ tailWord_7667253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667253).length < 2 ^ (prefixWord ++ tailWord_7667253).sum := by decide
  have hdescent : baseEnd_7667253 < baseStart_7667253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667290 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2]
def baseStart_7667290 : Nat := 118140960795 + 7667290 * 2 ^ 59
def prefixEnd_7667290 : Nat := 4983230072969 + 3 ^ 40 * 7667290 * 2
def baseEnd_7667290 : Nat := 3937005087411411926313781

theorem tailTrace_7667290 : CollatzResearch.WordTrace tailWord_7667290 prefixEnd_7667290 3937005087411411926313781 := by
  unfold tailWord_7667290
  simp only [CollatzResearch.WordTrace]
  refine ⟨69912260098181318431241831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186432693595150182483311549 69912260098181318431241831)
  ·
    refine ⟨104868390147271977646862747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69912260098181318431241831 104868390147271977646862747)
    ·
      refine ⟨157302585220907966470294121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104868390147271977646862747 157302585220907966470294121)
      ·
        refine ⟨117976938915680974852720591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157302585220907966470294121 117976938915680974852720591)
        ·
          refine ⟨176965408373521462279080887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117976938915680974852720591 176965408373521462279080887)
          ·
            refine ⟨265448112560282193418621331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176965408373521462279080887 265448112560282193418621331)
            ·
              refine ⟨398172168840423290127931997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265448112560282193418621331 398172168840423290127931997)
              ·
                refine ⟨149314563315158733797974499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398172168840423290127931997 149314563315158733797974499)
                ·
                  refine ⟨223971844972738100696961749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149314563315158733797974499 223971844972738100696961749)
                  ·
                    refine ⟨5249340116548549235085041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 223971844972738100696961749 5249340116548549235085041)
                    ·
                      refine ⟨3937005087411411926313781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5249340116548549235085041 3937005087411411926313781)
                      ·
                        rfl

theorem cell23_7667290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_7667290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667290 prefixEnd_7667290 := by exact prefixLift 7667290
  have htrace : WordTrace (prefixWord ++ tailWord_7667290) baseStart_7667290 baseEnd_7667290 := by
    simpa [prefixWord, tailWord_7667290, baseEnd_7667290] using wordTrace_append hprefix tailTrace_7667290
  have hstable : (prefixWord ++ tailWord_7667290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667290).length < 2 ^ (prefixWord ++ tailWord_7667290).sum := by decide
  have hdescent : baseEnd_7667290 < baseStart_7667290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667431 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 1, 5, 2]
def baseStart_7667431 : Nat := 118140960795 + 7667431 * 2 ^ 59
def prefixEnd_7667431 : Nat := 4983230072969 + 3 ^ 40 * 7667431 * 2
def baseEnd_7667431 : Nat := 3937077488183695874650633

theorem tailTrace_7667431 : CollatzResearch.WordTrace tailWord_7667431 prefixEnd_7667431 3937077488183695874650633 := by
  unfold tailWord_7667431
  simp only [CollatzResearch.WordTrace]
  refine ⟨279654183085214454805850147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186436122056809636537233431 279654183085214454805850147)
  ·
    refine ⟨419481274627821682208775221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279654183085214454805850147 419481274627821682208775221)
    ·
      refine ⟨39326369496358282707072677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 419481274627821682208775221 39326369496358282707072677)
      ·
        refine ⟨7373694280567178007576127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39326369496358282707072677 7373694280567178007576127)
        ·
          refine ⟨11060541420850767011364191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7373694280567178007576127 11060541420850767011364191)
          ·
            refine ⟨16590812131276150517046287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11060541420850767011364191 16590812131276150517046287)
            ·
              refine ⟨24886218196914225775569431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16590812131276150517046287 24886218196914225775569431)
              ·
                refine ⟨37329327295371338663354147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24886218196914225775569431 37329327295371338663354147)
                ·
                  refine ⟨55993990943057007995031221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37329327295371338663354147 55993990943057007995031221)
                  ·
                    refine ⟨5249436650911594499534177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55993990943057007995031221 5249436650911594499534177)
                    ·
                      refine ⟨3937077488183695874650633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5249436650911594499534177 3937077488183695874650633)
                      ·
                        rfl

theorem cell23_7667431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_7667431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667431 prefixEnd_7667431 := by exact prefixLift 7667431
  have htrace : WordTrace (prefixWord ++ tailWord_7667431) baseStart_7667431 baseEnd_7667431 := by
    simpa [prefixWord, tailWord_7667431, baseEnd_7667431] using wordTrace_append hprefix tailTrace_7667431
  have hstable : (prefixWord ++ tailWord_7667431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667431).length < 2 ^ (prefixWord ++ tailWord_7667431).sum := by decide
  have hdescent : baseEnd_7667431 < baseStart_7667431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667437 : List Nat := [1, 5, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_7667437 : Nat := 118140960795 + 7667437 * 2 ^ 59
def prefixEnd_7667437 : Nat := 4983230072969 + 3 ^ 40 * 7667437 * 2
def baseEnd_7667437 : Nat := 1312360189689207617058535

theorem tailTrace_7667437 : CollatzResearch.WordTrace tailWord_7667437 prefixEnd_7667437 1312360189689207617058535 := by
  unfold tailWord_7667437
  simp only [CollatzResearch.WordTrace]
  refine ⟨279654401923192717830568565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186436267948795145220379043 279654401923192717830568565)
  ·
    refine ⟨26217600180299317296615803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279654401923192717830568565 26217600180299317296615803)
    ·
      refine ⟨39326400270448975944923705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26217600180299317296615803 39326400270448975944923705)
      ·
        refine ⟨29494800202836731958692779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39326400270448975944923705 29494800202836731958692779)
        ·
          refine ⟨44242200304255097938039169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29494800202836731958692779 44242200304255097938039169)
          ·
            refine ⟨33181650228191323453529377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44242200304255097938039169 33181650228191323453529377)
            ·
              refine ⟨24886237671143492590147033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33181650228191323453529377 24886237671143492590147033)
              ·
                refine ⟨18664678253357619442610275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24886237671143492590147033 18664678253357619442610275)
                ·
                  refine ⟨27997017380036429163915413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18664678253357619442610275 27997017380036429163915413)
                  ·
                    refine ⟨1312360189689207617058535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27997017380036429163915413 1312360189689207617058535)
                    ·
                      rfl

theorem cell23_7667437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_7667437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667437 prefixEnd_7667437 := by exact prefixLift 7667437
  have htrace : WordTrace (prefixWord ++ tailWord_7667437) baseStart_7667437 baseEnd_7667437 := by
    simpa [prefixWord, tailWord_7667437, baseEnd_7667437] using wordTrace_append hprefix tailTrace_7667437
  have hstable : (prefixWord ++ tailWord_7667437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667437).length < 2 ^ (prefixWord ++ tailWord_7667437).sum := by decide
  have hdescent : baseEnd_7667437 < baseStart_7667437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667440 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 4]
def baseStart_7667440 : Nat := 118140960795 + 7667440 * 2 ^ 59
def prefixEnd_7667440 : Nat := 4983230072969 + 3 ^ 40 * 7667440 * 2
def baseEnd_7667440 : Nat := 3937082109509586339438091

theorem tailTrace_7667440 : CollatzResearch.WordTrace tailWord_7667440 prefixEnd_7667440 3937082109509586339438091 := by
  unfold tailWord_7667440
  simp only [CollatzResearch.WordTrace]
  refine ⟨139827255671090924671463887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186436340894787899561951849 139827255671090924671463887)
  ·
    refine ⟨209740883506636387007195831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139827255671090924671463887 209740883506636387007195831)
    ·
      refine ⟨314611325259954580510793747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209740883506636387007195831 314611325259954580510793747)
      ·
        refine ⟨471916987889931870766190621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314611325259954580510793747 471916987889931870766190621)
        ·
          refine ⟨176968870458724451537321483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 471916987889931870766190621 176968870458724451537321483)
          ·
            refine ⟨265453305688086677305982225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176968870458724451537321483 265453305688086677305982225)
            ·
              refine ⟨199089979266065007979486669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265453305688086677305982225 199089979266065007979486669)
              ·
                refine ⟨74658742224774377992307501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199089979266065007979486669 74658742224774377992307501)
                ·
                  refine ⟨27997028334290391747115313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74658742224774377992307501 27997028334290391747115313)
                  ·
                    refine ⟨20997771250717793810336485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27997028334290391747115313 20997771250717793810336485)
                    ·
                      refine ⟨3937082109509586339438091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20997771250717793810336485 3937082109509586339438091)
                      ·
                        rfl

theorem cell23_7667440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_7667440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667440 prefixEnd_7667440 := by exact prefixLift 7667440
  have htrace : WordTrace (prefixWord ++ tailWord_7667440) baseStart_7667440 baseEnd_7667440 := by
    simpa [prefixWord, tailWord_7667440, baseEnd_7667440] using wordTrace_append hprefix tailTrace_7667440
  have hstable : (prefixWord ++ tailWord_7667440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667440).length < 2 ^ (prefixWord ++ tailWord_7667440).sum := by decide
  have hdescent : baseEnd_7667440 < baseStart_7667440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667462 : List Nat := [6, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_7667462 : Nat := 118140960795 + 7667462 * 2 ^ 59
def prefixEnd_7667462 : Nat := 4983230072969 + 3 ^ 40 * 7667462 * 2
def baseEnd_7667462 : Nat := 437454822898220583706999

theorem tailTrace_7667462 : CollatzResearch.WordTrace tailWord_7667462 prefixEnd_7667462 437454822898220583706999 := by
  unfold tailWord_7667462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8739228554628192096882145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 186436875832068098066819093 8739228554628192096882145)
  ·
    refine ⟨6554421415971144072661609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8739228554628192096882145 6554421415971144072661609)
    ·
      refine ⟨4915816061978358054496207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6554421415971144072661609 4915816061978358054496207)
      ·
        refine ⟨7373724092967537081744311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4915816061978358054496207 7373724092967537081744311)
        ·
          refine ⟨11060586139451305622616467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7373724092967537081744311 11060586139451305622616467)
          ·
            refine ⟨16590879209176958433924701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11060586139451305622616467 16590879209176958433924701)
            ·
              refine ⟨6221579703441359412721763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16590879209176958433924701 6221579703441359412721763)
              ·
                refine ⟨9332369555162039119082645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6221579703441359412721763 9332369555162039119082645)
                ·
                  refine ⟨437454822898220583706999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9332369555162039119082645 437454822898220583706999)
                  ·
                    rfl

theorem cell23_7667462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_7667462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667462 prefixEnd_7667462 := by exact prefixLift 7667462
  have htrace : WordTrace (prefixWord ++ tailWord_7667462) baseStart_7667462 baseEnd_7667462 := by
    simpa [prefixWord, tailWord_7667462, baseEnd_7667462] using wordTrace_append hprefix tailTrace_7667462
  have hstable : (prefixWord ++ tailWord_7667462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667462).length < 2 ^ (prefixWord ++ tailWord_7667462).sum := by decide
  have hdescent : baseEnd_7667462 < baseStart_7667462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667474 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_7667474 : Nat := 118140960795 + 7667474 * 2 ^ 59
def prefixEnd_7667474 : Nat := 4983230072969 + 3 ^ 40 * 7667474 * 2
def baseEnd_7667474 : Nat := 3937099567851839206412935

theorem tailTrace_7667474 : CollatzResearch.WordTrace tailWord_7667474 prefixEnd_7667474 3937099567851839206412935 := by
  unfold tailWord_7667474
  simp only [CollatzResearch.WordTrace]
  refine ⟨69913937856014668287416369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186437167616039115433110317 69913937856014668287416369)
  ·
    refine ⟨52435453392011001215562277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69913937856014668287416369 52435453392011001215562277)
    ·
      refine ⟨9831647511002062727917927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52435453392011001215562277 9831647511002062727917927)
      ·
        refine ⟨14747471266503094091876891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9831647511002062727917927 14747471266503094091876891)
        ·
          refine ⟨22121206899754641137815337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14747471266503094091876891 22121206899754641137815337)
          ·
            refine ⟨16590905174815980853361503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22121206899754641137815337 16590905174815980853361503)
            ·
              refine ⟨24886357762223971280042255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16590905174815980853361503 24886357762223971280042255)
              ·
                refine ⟨37329536643335956920063383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24886357762223971280042255 37329536643335956920063383)
                ·
                  refine ⟨55994304965003935380095075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37329536643335956920063383 55994304965003935380095075)
                  ·
                    refine ⟨83991457447505903070142613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55994304965003935380095075 83991457447505903070142613)
                    ·
                      refine ⟨3937099567851839206412935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83991457447505903070142613 3937099567851839206412935)
                      ·
                        rfl

theorem cell23_7667474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_7667474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667474 prefixEnd_7667474 := by exact prefixLift 7667474
  have htrace : WordTrace (prefixWord ++ tailWord_7667474) baseStart_7667474 baseEnd_7667474 := by
    simpa [prefixWord, tailWord_7667474, baseEnd_7667474] using wordTrace_append hprefix tailTrace_7667474
  have hstable : (prefixWord ++ tailWord_7667474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667474).length < 2 ^ (prefixWord ++ tailWord_7667474).sum := by decide
  have hdescent : baseEnd_7667474 < baseStart_7667474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667480 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 2, 7]
def baseStart_7667480 : Nat := 118140960795 + 7667480 * 2 ^ 59
def prefixEnd_7667480 : Nat := 4983230072969 + 3 ^ 40 * 7667480 * 2
def baseEnd_7667480 : Nat := 1312367549578588727645969

theorem tailTrace_7667480 : CollatzResearch.WordTrace tailWord_7667480 prefixEnd_7667480 1312367549578588727645969 := by
  unfold tailWord_7667480
  simp only [CollatzResearch.WordTrace]
  refine ⟨139827985131018468087191947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186437313508024624116255929 139827985131018468087191947)
  ·
    refine ⟨209741977696527702130787921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139827985131018468087191947 209741977696527702130787921)
    ·
      refine ⟨157306483272395776598090941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209741977696527702130787921 157306483272395776598090941)
      ·
        refine ⟨58989931227148416224284103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157306483272395776598090941 58989931227148416224284103)
        ·
          refine ⟨88484896840722624336426155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58989931227148416224284103 88484896840722624336426155)
          ·
            refine ⟨132727345261083936504639233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88484896840722624336426155 132727345261083936504639233)
            ·
              refine ⟨99545508945812952378479425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132727345261083936504639233 99545508945812952378479425)
              ·
                refine ⟨74659131709359714283859569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99545508945812952378479425 74659131709359714283859569)
                ·
                  refine ⟨55994348782019785712894677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74659131709359714283859569 55994348782019785712894677)
                  ·
                    refine ⟨1312367549578588727645969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55994348782019785712894677 1312367549578588727645969)
                    ·
                      rfl

theorem cell23_7667480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_7667480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667480 prefixEnd_7667480 := by exact prefixLift 7667480
  have htrace : WordTrace (prefixWord ++ tailWord_7667480) baseStart_7667480 baseEnd_7667480 := by
    simpa [prefixWord, tailWord_7667480, baseEnd_7667480] using wordTrace_append hprefix tailTrace_7667480
  have hstable : (prefixWord ++ tailWord_7667480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667480).length < 2 ^ (prefixWord ++ tailWord_7667480).sum := by decide
  have hdescent : baseEnd_7667480 < baseStart_7667480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667528 : List Nat := [2, 1, 3, 1, 1, 6, 2, 1, 2, 1, 3]
def baseStart_7667528 : Nat := 118140960795 + 7667528 * 2 ^ 59
def prefixEnd_7667528 : Nat := 4983230072969 + 3 ^ 40 * 7667528 * 2
def baseEnd_7667528 : Nat := 3937127295807181995137687

theorem tailTrace_7667528 : CollatzResearch.WordTrace tailWord_7667528 prefixEnd_7667528 3937127295807181995137687 := by
  unfold tailWord_7667528
  simp only [CollatzResearch.WordTrace]
  refine ⟨139828860482931520186065619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186438480643908693581420825 139828860482931520186065619)
  ·
    refine ⟨209743290724397280279098429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139828860482931520186065619 209743290724397280279098429)
    ·
      refine ⟨78653734021648980104661911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209743290724397280279098429 78653734021648980104661911)
      ·
        refine ⟨117980601032473470156992867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78653734021648980104661911 117980601032473470156992867)
        ·
          refine ⟨176970901548710205235489301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117980601032473470156992867 176970901548710205235489301)
          ·
            refine ⟨8295511010095790870413561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 176970901548710205235489301 8295511010095790870413561)
            ·
              refine ⟨6221633257571843152810171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8295511010095790870413561 6221633257571843152810171)
              ·
                refine ⟨9332449886357764729215257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6221633257571843152810171 9332449886357764729215257)
                ·
                  refine ⟨6999337414768323546911443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9332449886357764729215257 6999337414768323546911443)
                  ·
                    refine ⟨10499006122152485320367165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6999337414768323546911443 10499006122152485320367165)
                    ·
                      refine ⟨3937127295807181995137687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10499006122152485320367165 3937127295807181995137687)
                      ·
                        rfl

theorem cell23_7667528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_7667528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667528 prefixEnd_7667528 := by exact prefixLift 7667528
  have htrace : WordTrace (prefixWord ++ tailWord_7667528) baseStart_7667528 baseEnd_7667528 := by
    simpa [prefixWord, tailWord_7667528, baseEnd_7667528] using wordTrace_append hprefix tailTrace_7667528
  have hstable : (prefixWord ++ tailWord_7667528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667528).length < 2 ^ (prefixWord ++ tailWord_7667528).sum := by decide
  have hdescent : baseEnd_7667528 < baseStart_7667528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667537 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 2, 1, 5]
def baseStart_7667537 : Nat := 118140960795 + 7667537 * 2 ^ 59
def prefixEnd_7667537 : Nat := 4983230072969 + 3 ^ 40 * 7667537 * 2
def baseEnd_7667537 : Nat := 3937131917133072459925145

theorem tailTrace_7667537 : CollatzResearch.WordTrace tailWord_7667537 prefixEnd_7667537 3937131917133072459925145 := by
  unfold tailWord_7667537
  simp only [CollatzResearch.WordTrace]
  refine ⟨279658049222830434909208865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186438699481886956606139243 279658049222830434909208865)
  ·
    refine ⟨209743536917122826181906649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279658049222830434909208865 209743536917122826181906649)
    ·
      refine ⟨157307652687842119636429987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209743536917122826181906649 157307652687842119636429987)
      ·
        refine ⟨235961479031763179454644981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157307652687842119636429987 235961479031763179454644981)
        ·
          refine ⟨22121388659227798073872967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 235961479031763179454644981 22121388659227798073872967)
          ·
            refine ⟨33182082988841697110809451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22121388659227798073872967 33182082988841697110809451)
            ·
              refine ⟨49773124483262545666214177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33182082988841697110809451 49773124483262545666214177)
              ·
                refine ⟨37329843362446909249660633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49773124483262545666214177 37329843362446909249660633)
                ·
                  refine ⟨27997382521835181937245475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37329843362446909249660633 27997382521835181937245475)
                  ·
                    refine ⟨41996073782752772905868213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27997382521835181937245475 41996073782752772905868213)
                    ·
                      refine ⟨3937131917133072459925145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41996073782752772905868213 3937131917133072459925145)
                      ·
                        rfl

theorem cell23_7667537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_7667537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667537 prefixEnd_7667537 := by exact prefixLift 7667537
  have htrace : WordTrace (prefixWord ++ tailWord_7667537) baseStart_7667537 baseEnd_7667537 := by
    simpa [prefixWord, tailWord_7667537, baseEnd_7667537] using wordTrace_append hprefix tailTrace_7667537
  have hstable : (prefixWord ++ tailWord_7667537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667537).length < 2 ^ (prefixWord ++ tailWord_7667537).sum := by decide
  have hdescent : baseEnd_7667537 < baseStart_7667537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667538 : List Nat := [3, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2]
def baseStart_7667538 : Nat := 118140960795 + 7667538 * 2 ^ 59
def prefixEnd_7667538 : Nat := 4983230072969 + 3 ^ 40 * 7667538 * 2
def baseEnd_7667538 : Nat := 3937132430613726956012641

theorem tailTrace_7667538 : CollatzResearch.WordTrace tailWord_7667538 prefixEnd_7667538 3937132430613726956012641 := by
  unfold tailWord_7667538
  simp only [CollatzResearch.WordTrace]
  refine ⟨69914521423956703019998817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186438723797217874719996845 69914521423956703019998817)
  ·
    refine ⟨52435891067967527264999113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69914521423956703019998817 52435891067967527264999113)
    ·
      refine ⟨39326918300975645448749335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52435891067967527264999113 39326918300975645448749335)
      ·
        refine ⟨58990377451463468173124003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39326918300975645448749335 58990377451463468173124003)
        ·
          refine ⟨88485566177195202259686005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58990377451463468173124003 88485566177195202259686005)
          ·
            refine ⟨8295521829112050211845563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88485566177195202259686005 8295521829112050211845563)
            ·
              refine ⟨12443282743668075317768345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8295521829112050211845563 12443282743668075317768345)
              ·
                refine ⟨9332462057751056488326259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12443282743668075317768345 9332462057751056488326259)
                ·
                  refine ⟨13998693086626584732489389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9332462057751056488326259 13998693086626584732489389)
                  ·
                    refine ⟨5249509907484969274683521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13998693086626584732489389 5249509907484969274683521)
                    ·
                      refine ⟨3937132430613726956012641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5249509907484969274683521 3937132430613726956012641)
                      ·
                        rfl

theorem cell23_7667538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_7667538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667538 prefixEnd_7667538 := by exact prefixLift 7667538
  have htrace : WordTrace (prefixWord ++ tailWord_7667538) baseStart_7667538 baseEnd_7667538 := by
    simpa [prefixWord, tailWord_7667538, baseEnd_7667538] using wordTrace_append hprefix tailTrace_7667538
  have hstable : (prefixWord ++ tailWord_7667538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667538).length < 2 ^ (prefixWord ++ tailWord_7667538).sum := by decide
  have hdescent : baseEnd_7667538 < baseStart_7667538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667554 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_7667554 : Nat := 118140960795 + 7667554 * 2 ^ 59
def prefixEnd_7667554 : Nat := 4983230072969 + 3 ^ 40 * 7667554 * 2
def baseEnd_7667554 : Nat := 3937140646304198893412567

theorem tailTrace_7667554 : CollatzResearch.WordTrace tailWord_7667554 prefixEnd_7667554 3937140646304198893412567 := by
  unfold tailWord_7667554
  simp only [CollatzResearch.WordTrace]
  refine ⟨69914667315942211703144429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186439112842512564541718477 69914667315942211703144429)
  ·
    refine ⟨26218000243478329388679161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69914667315942211703144429 26218000243478329388679161)
    ·
      refine ⟨19663500182608747041509371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26218000243478329388679161 19663500182608747041509371)
      ·
        refine ⟨29495250273913120562264057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19663500182608747041509371 29495250273913120562264057)
        ·
          refine ⟨22121437705434840421698043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29495250273913120562264057 22121437705434840421698043)
          ·
            refine ⟨33182156558152260632547065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22121437705434840421698043 33182156558152260632547065)
            ·
              refine ⟨24886617418614195474410299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33182156558152260632547065 24886617418614195474410299)
              ·
                refine ⟨37329926127921293211615449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24886617418614195474410299 37329926127921293211615449)
                ·
                  refine ⟨27997444595940969908711587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37329926127921293211615449 27997444595940969908711587)
                  ·
                    refine ⟨41996166893911454863067381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27997444595940969908711587 41996166893911454863067381)
                    ·
                      refine ⟨3937140646304198893412567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41996166893911454863067381 3937140646304198893412567)
                      ·
                        rfl

theorem cell23_7667554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_7667554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667554 prefixEnd_7667554 := by exact prefixLift 7667554
  have htrace : WordTrace (prefixWord ++ tailWord_7667554) baseStart_7667554 baseEnd_7667554 := by
    simpa [prefixWord, tailWord_7667554, baseEnd_7667554] using wordTrace_append hprefix tailTrace_7667554
  have hstable : (prefixWord ++ tailWord_7667554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667554).length < 2 ^ (prefixWord ++ tailWord_7667554).sum := by decide
  have hdescent : baseEnd_7667554 < baseStart_7667554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667604 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_7667604 : Nat := 118140960795 + 7667604 * 2 ^ 59
def prefixEnd_7667604 : Nat := 4983230072969 + 3 ^ 40 * 7667604 * 2
def baseEnd_7667604 : Nat := 1312388773445641232595779

theorem tailTrace_7667604 : CollatzResearch.WordTrace tailWord_7667604 prefixEnd_7667604 1312388773445641232595779 := by
  unfold tailWord_7667604
  simp only [CollatzResearch.WordTrace]
  refine ⟨139830246456793852675948933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186440328609058470234598577 139830246456793852675948933)
  ·
    refine ⟨26218171210648847376740425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139830246456793852675948933 26218171210648847376740425)
    ·
      refine ⟨19663628407986635532555319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26218171210648847376740425 19663628407986635532555319)
      ·
        refine ⟨29495442611979953298832979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19663628407986635532555319 29495442611979953298832979)
        ·
          refine ⟨44243163917969929948249469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29495442611979953298832979 44243163917969929948249469)
          ·
            refine ⟨16591186469238723730593551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44243163917969929948249469 16591186469238723730593551)
            ·
              refine ⟨24886779703858085595890327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16591186469238723730593551 24886779703858085595890327)
              ·
                refine ⟨37330169555787128393835491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24886779703858085595890327 37330169555787128393835491)
                ·
                  refine ⟨55995254333680692590753237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37330169555787128393835491 55995254333680692590753237)
                  ·
                    refine ⟨1312388773445641232595779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55995254333680692590753237 1312388773445641232595779)
                    ·
                      rfl

theorem cell23_7667604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_7667604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667604 prefixEnd_7667604 := by exact prefixLift 7667604
  have htrace : WordTrace (prefixWord ++ tailWord_7667604) baseStart_7667604 baseEnd_7667604 := by
    simpa [prefixWord, tailWord_7667604, baseEnd_7667604] using wordTrace_append hprefix tailTrace_7667604
  have hstable : (prefixWord ++ tailWord_7667604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667604).length < 2 ^ (prefixWord ++ tailWord_7667604).sum := by decide
  have hdescent : baseEnd_7667604 < baseStart_7667604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667606 : List Nat := [5, 3, 1, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_7667606 : Nat := 118140960795 + 7667606 * 2 ^ 59
def prefixEnd_7667606 : Nat := 4983230072969 + 3 ^ 40 * 7667606 * 2
def baseEnd_7667606 : Nat := 3937167347298232689962329

theorem tailTrace_7667606 : CollatzResearch.WordTrace tailWord_7667606 prefixEnd_7667606 3937167347298232689962329 := by
  unfold tailWord_7667606
  simp only [CollatzResearch.WordTrace]
  refine ⟨17478785366223778730841917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186440377239720306462313781 17478785366223778730841917)
  ·
    refine ⟨6554544512333917024065719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17478785366223778730841917 6554544512333917024065719)
    ·
      refine ⟨9831816768500875536098579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6554544512333917024065719 9831816768500875536098579)
      ·
        refine ⟨14747725152751313304147869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9831816768500875536098579 14747725152751313304147869)
        ·
          refine ⟨5530396932281742489055451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14747725152751313304147869 5530396932281742489055451)
          ·
            refine ⟨8295595398422613733583177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5530396932281742489055451 8295595398422613733583177)
            ·
              refine ⟨6221696548816960300187383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8295595398422613733583177 6221696548816960300187383)
              ·
                refine ⟨9332544823225440450281075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6221696548816960300187383 9332544823225440450281075)
                ·
                  refine ⟨13998817234838160675421613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9332544823225440450281075 13998817234838160675421613)
                  ·
                    refine ⟨5249556463064310253283105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13998817234838160675421613 5249556463064310253283105)
                    ·
                      refine ⟨3937167347298232689962329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5249556463064310253283105 3937167347298232689962329)
                      ·
                        rfl

theorem cell23_7667606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_7667606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667606 prefixEnd_7667606 := by exact prefixLift 7667606
  have htrace : WordTrace (prefixWord ++ tailWord_7667606) baseStart_7667606 baseEnd_7667606 := by
    simpa [prefixWord, tailWord_7667606, baseEnd_7667606] using wordTrace_append hprefix tailTrace_7667606
  have hstable : (prefixWord ++ tailWord_7667606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667606).length < 2 ^ (prefixWord ++ tailWord_7667606).sum := by decide
  have hdescent : baseEnd_7667606 < baseStart_7667606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667608 : List Nat := [2, 1, 2, 6, 1, 1, 2, 3, 5]
def baseStart_7667608 : Nat := 118140960795 + 7667608 * 2 ^ 59
def prefixEnd_7667608 : Nat := 4983230072969 + 3 ^ 40 * 7667608 * 2
def baseEnd_7667608 : Nat := 437463152695504631348591

theorem tailTrace_7667608 : CollatzResearch.WordTrace tailWord_7667608 prefixEnd_7667608 437463152695504631348591 := by
  unfold tailWord_7667608
  simp only [CollatzResearch.WordTrace]
  refine ⟨139830319402786607017521739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186440425870382142690028985 139830319402786607017521739)
  ·
    refine ⟨209745479104179910526282609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139830319402786607017521739 209745479104179910526282609)
    ·
      refine ⟨157309109328134932894711957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209745479104179910526282609 157309109328134932894711957)
      ·
        refine ⟨7373864499756324979439623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 157309109328134932894711957 7373864499756324979439623)
        ·
          refine ⟨11060796749634487469159435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7373864499756324979439623 11060796749634487469159435)
          ·
            refine ⟨16591195124451731203739153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11060796749634487469159435 16591195124451731203739153)
            ·
              refine ⟨12443396343338798402804365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16591195124451731203739153 12443396343338798402804365)
              ·
                refine ⟨4666273628752049401051637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12443396343338798402804365 4666273628752049401051637)
                ·
                  refine ⟨437463152695504631348591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4666273628752049401051637 437463152695504631348591)
                  ·
                    rfl

theorem cell23_7667608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 5].length) (baseStart_7667608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667608 prefixEnd_7667608 := by exact prefixLift 7667608
  have htrace : WordTrace (prefixWord ++ tailWord_7667608) baseStart_7667608 baseEnd_7667608 := by
    simpa [prefixWord, tailWord_7667608, baseEnd_7667608] using wordTrace_append hprefix tailTrace_7667608
  have hstable : (prefixWord ++ tailWord_7667608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667608).length < 2 ^ (prefixWord ++ tailWord_7667608).sum := by decide
  have hdescent : baseEnd_7667608 < baseStart_7667608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667627 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 3]
def baseStart_7667627 : Nat := 118140960795 + 7667627 * 2 ^ 59
def prefixEnd_7667627 : Nat := 4983230072969 + 3 ^ 40 * 7667627 * 2
def baseEnd_7667627 : Nat := 3937178130391977107799731

theorem tailTrace_7667627 : CollatzResearch.WordTrace tailWord_7667627 prefixEnd_7667627 3937178130391977107799731 := by
  unfold tailWord_7667627
  simp only [CollatzResearch.WordTrace]
  refine ⟨279661331792504380279985135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186440887861669586853323423 279661331792504380279985135)
  ·
    refine ⟨419491997688756570419977703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279661331792504380279985135 419491997688756570419977703)
    ·
      refine ⟨629237996533134855629966555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419491997688756570419977703 629237996533134855629966555)
      ·
        refine ⟨943856994799702283444949833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629237996533134855629966555 943856994799702283444949833)
        ·
          refine ⟨707892746099776712583712375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 943856994799702283444949833 707892746099776712583712375)
          ·
            refine ⟨1061839119149665068875568563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707892746099776712583712375 1061839119149665068875568563)
            ·
              refine ⟨1592758678724497603313352845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061839119149665068875568563 1592758678724497603313352845)
              ·
                refine ⟨597284504521686601242507317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1592758678724497603313352845 597284504521686601242507317)
                ·
                  refine ⟨55995422298908118866485061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 597284504521686601242507317 55995422298908118866485061)
                  ·
                    refine ⟨10499141681045272287465949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55995422298908118866485061 10499141681045272287465949)
                    ·
                      refine ⟨3937178130391977107799731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10499141681045272287465949 3937178130391977107799731)
                      ·
                        rfl

theorem cell23_7667627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 3].length) (baseStart_7667627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667627 prefixEnd_7667627 := by exact prefixLift 7667627
  have htrace : WordTrace (prefixWord ++ tailWord_7667627) baseStart_7667627 baseEnd_7667627 := by
    simpa [prefixWord, tailWord_7667627, baseEnd_7667627] using wordTrace_append hprefix tailTrace_7667627
  have hstable : (prefixWord ++ tailWord_7667627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667627).length < 2 ^ (prefixWord ++ tailWord_7667627).sum := by decide
  have hdescent : baseEnd_7667627 < baseStart_7667627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667724 : List Nat := [2, 2, 1, 2, 3, 1, 3, 2, 1, 6]
def baseStart_7667724 : Nat := 118140960795 + 7667724 * 2 ^ 59
def prefixEnd_7667724 : Nat := 4983230072969 + 3 ^ 40 * 7667724 * 2
def baseEnd_7667724 : Nat := 1312409312671821076095595

theorem tailTrace_7667724 : CollatzResearch.WordTrace tailWord_7667724 prefixEnd_7667724 1312409312671821076095595 := by
  unfold tailWord_7667724
  simp only [CollatzResearch.WordTrace]
  refine ⟨139832434836576482923133113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186443246448768643897510817 139832434836576482923133113)
  ·
    refine ⟨104874326127432362192349835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139832434836576482923133113 104874326127432362192349835)
    ·
      refine ⟨157311489191148543288524753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104874326127432362192349835 157311489191148543288524753)
      ·
        refine ⟨117983616893361407466393565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157311489191148543288524753 117983616893361407466393565)
        ·
          refine ⟨44243856335010527799897587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117983616893361407466393565 44243856335010527799897587)
          ·
            refine ⟨66365784502515791699846381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44243856335010527799897587 66365784502515791699846381)
            ·
              refine ⟨24887169188443421887442393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66365784502515791699846381 24887169188443421887442393)
              ·
                refine ⟨18665376891332566415581795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24887169188443421887442393 18665376891332566415581795)
                ·
                  refine ⟨27998065336998849623372693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18665376891332566415581795 27998065336998849623372693)
                  ·
                    refine ⟨1312409312671821076095595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27998065336998849623372693 1312409312671821076095595)
                    ·
                      rfl

theorem cell23_7667724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_7667724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667724 prefixEnd_7667724 := by exact prefixLift 7667724
  have htrace : WordTrace (prefixWord ++ tailWord_7667724) baseStart_7667724 baseEnd_7667724 := by
    simpa [prefixWord, tailWord_7667724, baseEnd_7667724] using wordTrace_append hprefix tailTrace_7667724
  have hstable : (prefixWord ++ tailWord_7667724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667724).length < 2 ^ (prefixWord ++ tailWord_7667724).sum := by decide
  have hdescent : baseEnd_7667724 < baseStart_7667724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667758 : List Nat := [4, 1, 3, 1, 1, 2, 2, 3, 2, 4]
def baseStart_7667758 : Nat := 118140960795 + 7667758 * 2 ^ 59
def prefixEnd_7667758 : Nat := 4983230072969 + 3 ^ 40 * 7667758 * 2
def baseEnd_7667758 : Nat := 1312415132119238698420543

theorem tailTrace_7667758 : CollatzResearch.WordTrace tailWord_7667758 prefixEnd_7667758 1312415132119238698420543 := by
  unfold tailWord_7667758
  simp only [CollatzResearch.WordTrace]
  refine ⟨34958263719378723706625491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186444073170019859768669285 34958263719378723706625491)
  ·
    refine ⟨52437395579068085559938237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34958263719378723706625491 52437395579068085559938237)
    ·
      refine ⟨19664023342150532084976839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52437395579068085559938237 19664023342150532084976839)
      ·
        refine ⟨29496035013225798127465259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19664023342150532084976839 29496035013225798127465259)
        ·
          refine ⟨44244052519838697191197889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29496035013225798127465259 44244052519838697191197889)
          ·
            refine ⟨33183039389879022893398417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44244052519838697191197889 33183039389879022893398417)
            ·
              refine ⟨24887279542409267170048813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33183039389879022893398417 24887279542409267170048813)
              ·
                refine ⟨9332729828403475188768305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24887279542409267170048813 9332729828403475188768305)
                ·
                  refine ⟨6999547371302606391576229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9332729828403475188768305 6999547371302606391576229)
                  ·
                    refine ⟨1312415132119238698420543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6999547371302606391576229 1312415132119238698420543)
                    ·
                      rfl

theorem cell23_7667758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_7667758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667758 prefixEnd_7667758 := by exact prefixLift 7667758
  have htrace : WordTrace (prefixWord ++ tailWord_7667758) baseStart_7667758 baseEnd_7667758 := by
    simpa [prefixWord, tailWord_7667758, baseEnd_7667758] using wordTrace_append hprefix tailTrace_7667758
  have hstable : (prefixWord ++ tailWord_7667758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667758).length < 2 ^ (prefixWord ++ tailWord_7667758).sum := by decide
  have hdescent : baseEnd_7667758 < baseStart_7667758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667761 : List Nat := [1, 2, 2, 3, 1, 4, 2, 1, 1, 2, 4]
def baseStart_7667761 : Nat := 118140960795 + 7667761 * 2 ^ 59
def prefixEnd_7667761 : Nat := 4983230072969 + 3 ^ 40 * 7667761 * 2
def baseEnd_7667761 : Nat := 3937246936799679583524115

theorem tailTrace_7667761 : CollatzResearch.WordTrace tailWord_7667761 prefixEnd_7667761 3937246936799679583524115 := by
  unfold tailWord_7667761
  simp only [CollatzResearch.WordTrace]
  refine ⟨279666219174018921165363137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186444146116012614110242091 279666219174018921165363137)
  ·
    refine ⟨209749664380514190874022353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279666219174018921165363137 209749664380514190874022353)
    ·
      refine ⟨157312248285385643155516765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209749664380514190874022353 157312248285385643155516765)
      ·
        refine ⟨58992093107019616183318787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157312248285385643155516765 58992093107019616183318787)
        ·
          refine ⟨88488139660529424274978181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58992093107019616183318787 88488139660529424274978181)
          ·
            refine ⟨16591526186349267051558409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88488139660529424274978181 16591526186349267051558409)
            ·
              refine ⟨12443644639761950288668807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16591526186349267051558409 12443644639761950288668807)
              ·
                refine ⟨18665466959642925433003211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12443644639761950288668807 18665466959642925433003211)
                ·
                  refine ⟨27998200439464388149504817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18665466959642925433003211 27998200439464388149504817)
                  ·
                    refine ⟨20998650329598291112128613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27998200439464388149504817 20998650329598291112128613)
                    ·
                      refine ⟨3937246936799679583524115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20998650329598291112128613 3937246936799679583524115)
                      ·
                        rfl

theorem cell23_7667761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_7667761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667761 prefixEnd_7667761 := by exact prefixLift 7667761
  have htrace : WordTrace (prefixWord ++ tailWord_7667761) baseStart_7667761 baseEnd_7667761 := by
    simpa [prefixWord, tailWord_7667761, baseEnd_7667761] using wordTrace_append hprefix tailTrace_7667761
  have hstable : (prefixWord ++ tailWord_7667761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667761).length < 2 ^ (prefixWord ++ tailWord_7667761).sum := by decide
  have hdescent : baseEnd_7667761 < baseStart_7667761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667781 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 4, 1, 3]
def baseStart_7667781 : Nat := 118140960795 + 7667781 * 2 ^ 59
def prefixEnd_7667781 : Nat := 4983230072969 + 3 ^ 40 * 7667781 * 2
def baseEnd_7667781 : Nat := 3937257206412769505274023

theorem tailTrace_7667781 : CollatzResearch.WordTrace tailWord_7667781 prefixEnd_7667781 3937257206412769505274023 := by
  unfold tailWord_7667781
  simp only [CollatzResearch.WordTrace]
  refine ⟨279666948633946464581091197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186444632422630976387394131 279666948633946464581091197)
  ·
    refine ⟨104875105737729924217909199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279666948633946464581091197 104875105737729924217909199)
    ·
      refine ⟨157312658606594886326863799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104875105737729924217909199 157312658606594886326863799)
      ·
        refine ⟨235968987909892329490295699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157312658606594886326863799 235968987909892329490295699)
        ·
          refine ⟨353953481864838494235443549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235968987909892329490295699 353953481864838494235443549)
          ·
            refine ⟨132732555699314435338291331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353953481864838494235443549 132732555699314435338291331)
            ·
              refine ⟨199098833548971653007436997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132732555699314435338291331 199098833548971653007436997)
              ·
                refine ⟨37331031290432184938894437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199098833548971653007436997 37331031290432184938894437)
                ·
                  refine ⟨6999568366956034676042707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37331031290432184938894437 6999568366956034676042707)
                  ·
                    refine ⟨10499352550434052014064061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6999568366956034676042707 10499352550434052014064061)
                    ·
                      refine ⟨3937257206412769505274023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10499352550434052014064061 3937257206412769505274023)
                      ·
                        rfl

theorem cell23_7667781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 1, 3].length) (baseStart_7667781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667781 prefixEnd_7667781 := by exact prefixLift 7667781
  have htrace : WordTrace (prefixWord ++ tailWord_7667781) baseStart_7667781 baseEnd_7667781 := by
    simpa [prefixWord, tailWord_7667781, baseEnd_7667781] using wordTrace_append hprefix tailTrace_7667781
  have hstable : (prefixWord ++ tailWord_7667781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667781).length < 2 ^ (prefixWord ++ tailWord_7667781).sum := by decide
  have hdescent : baseEnd_7667781 < baseStart_7667781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667815 : List Nat := [1, 1, 5, 1, 1, 2, 5, 1, 2, 1, 3]
def baseStart_7667815 : Nat := 118140960795 + 7667815 * 2 ^ 59
def prefixEnd_7667815 : Nat := 4983230072969 + 3 ^ 40 * 7667815 * 2
def baseEnd_7667815 : Nat := 3937274664755022372248867

theorem tailTrace_7667815 : CollatzResearch.WordTrace tailWord_7667815 prefixEnd_7667815 3937274664755022372248867 := by
  unfold tailWord_7667815
  simp only [CollatzResearch.WordTrace]
  refine ⟨279668188715823288387828899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186445459143882192258552599 279668188715823288387828899)
  ·
    refine ⟨419502283073734932581743349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279668188715823288387828899 419502283073734932581743349)
    ·
      refine ⟨39328339038162649929538439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 419502283073734932581743349 39328339038162649929538439)
      ·
        refine ⟨58992508557243974894307659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39328339038162649929538439 58992508557243974894307659)
        ·
          refine ⟨88488762835865962341461489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58992508557243974894307659 88488762835865962341461489)
          ·
            refine ⟨66366572126899471756096117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88488762835865962341461489 66366572126899471756096117)
            ·
              refine ⟨6221866136896825477134011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66366572126899471756096117 6221866136896825477134011)
              ·
                refine ⟨9332799205345238215701017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6221866136896825477134011 9332799205345238215701017)
                ·
                  refine ⟨6999599404008928661775763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9332799205345238215701017 6999599404008928661775763)
                  ·
                    refine ⟨10499399106013392992663645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6999599404008928661775763 10499399106013392992663645)
                    ·
                      refine ⟨3937274664755022372248867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10499399106013392992663645 3937274664755022372248867)
                      ·
                        rfl

theorem cell23_7667815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_7667815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667815 prefixEnd_7667815 := by exact prefixLift 7667815
  have htrace : WordTrace (prefixWord ++ tailWord_7667815) baseStart_7667815 baseEnd_7667815 := by
    simpa [prefixWord, tailWord_7667815, baseEnd_7667815] using wordTrace_append hprefix tailTrace_7667815
  have hstable : (prefixWord ++ tailWord_7667815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667815).length < 2 ^ (prefixWord ++ tailWord_7667815).sum := by decide
  have hdescent : baseEnd_7667815 < baseStart_7667815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667872 : List Nat := [2, 1, 1, 4, 2, 2, 4, 1, 2, 2, 2]
def baseStart_7667872 : Nat := 118140960795 + 7667872 * 2 ^ 59
def prefixEnd_7667872 : Nat := 4983230072969 + 3 ^ 40 * 7667872 * 2
def baseEnd_7667872 : Nat := 3937303933152328649236105

theorem tailTrace_7667872 : CollatzResearch.WordTrace tailWord_7667872 prefixEnd_7667872 3937303933152328649236105 := by
  unfold tailWord_7667872
  simp only [CollatzResearch.WordTrace]
  refine ⟨139835133838308393561326935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186446845117744524748435913 139835133838308393561326935)
  ·
    refine ⟨209752700757462590341990403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139835133838308393561326935 209752700757462590341990403)
    ·
      refine ⟨314629051136193885512985605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209752700757462590341990403 314629051136193885512985605)
      ·
        refine ⟨58992947088036353533684801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314629051136193885512985605 58992947088036353533684801)
        ·
          refine ⟨44244710316027265150263601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58992947088036353533684801 44244710316027265150263601)
          ·
            refine ⟨33183532737020448862697701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44244710316027265150263601 33183532737020448862697701)
            ·
              refine ⟨6221912388191334161755819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33183532737020448862697701 6221912388191334161755819)
              ·
                refine ⟨9332868582287001242633729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6221912388191334161755819 9332868582287001242633729)
                ·
                  refine ⟨6999651436715250931975297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9332868582287001242633729 6999651436715250931975297)
                  ·
                    refine ⟨5249738577536438198981473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6999651436715250931975297 5249738577536438198981473)
                    ·
                      refine ⟨3937303933152328649236105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5249738577536438198981473 3937303933152328649236105)
                      ·
                        rfl

theorem cell23_7667872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_7667872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667872 prefixEnd_7667872 := by exact prefixLift 7667872
  have htrace : WordTrace (prefixWord ++ tailWord_7667872) baseStart_7667872 baseEnd_7667872 := by
    simpa [prefixWord, tailWord_7667872, baseEnd_7667872] using wordTrace_append hprefix tailTrace_7667872
  have hstable : (prefixWord ++ tailWord_7667872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667872).length < 2 ^ (prefixWord ++ tailWord_7667872).sum := by decide
  have hdescent : baseEnd_7667872 < baseStart_7667872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667906 : List Nat := [3, 5, 1, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_7667906 : Nat := 118140960795 + 7667906 * 2 ^ 59
def prefixEnd_7667906 : Nat := 4983230072969 + 3 ^ 40 * 7667906 * 2
def baseEnd_7667906 : Nat := 3937321391494581516210949

theorem tailTrace_7667906 : CollatzResearch.WordTrace tailWord_7667906 prefixEnd_7667906 3937321391494581516210949 := by
  unfold tailWord_7667906
  simp only [CollatzResearch.WordTrace]
  refine ⟨69917876939623402732347893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186447671838995740619594381 69917876939623402732347893)
  ·
    refine ⟨6554800963089694006157615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69917876939623402732347893 6554800963089694006157615)
    ·
      refine ⟨9832201444634541009236423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6554800963089694006157615 9832201444634541009236423)
      ·
        refine ⟨14748302166951811513854635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9832201444634541009236423 14748302166951811513854635)
        ·
          refine ⟨22122453250427717270781953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14748302166951811513854635 22122453250427717270781953)
          ·
            refine ⟨16591839937820787953086465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22122453250427717270781953 16591839937820787953086465)
            ·
              refine ⟨12443879953365590964814849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16591839937820787953086465 12443879953365590964814849)
              ·
                refine ⟨9332909965024193223611137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12443879953365590964814849 9332909965024193223611137)
                ·
                  refine ⟨6999682473768144917708353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9332909965024193223611137 6999682473768144917708353)
                  ·
                    refine ⟨5249761855326108688281265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6999682473768144917708353 5249761855326108688281265)
                    ·
                      refine ⟨3937321391494581516210949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5249761855326108688281265 3937321391494581516210949)
                      ·
                        rfl

theorem cell23_7667906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_7667906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667906 prefixEnd_7667906 := by exact prefixLift 7667906
  have htrace : WordTrace (prefixWord ++ tailWord_7667906) baseStart_7667906 baseEnd_7667906 := by
    simpa [prefixWord, tailWord_7667906, baseEnd_7667906] using wordTrace_append hprefix tailTrace_7667906
  have hstable : (prefixWord ++ tailWord_7667906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667906).length < 2 ^ (prefixWord ++ tailWord_7667906).sum := by decide
  have hdescent : baseEnd_7667906 < baseStart_7667906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667908 : List Nat := [2, 3, 3, 1, 2, 1, 2, 2, 2, 5]
def baseStart_7667908 : Nat := 118140960795 + 7667908 * 2 ^ 59
def prefixEnd_7667908 : Nat := 4983230072969 + 3 ^ 40 * 7667908 * 2
def baseEnd_7667908 : Nat := 1312440806151963502795313

theorem tailTrace_7667908 : CollatzResearch.WordTrace tailWord_7667908 prefixEnd_7667908 1312440806151963502795313 := by
  unfold tailWord_7667908
  simp only [CollatzResearch.WordTrace]
  refine ⟨139835790352243182635482189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186447720469657576847309585 139835790352243182635482189)
  ·
    refine ⟨52438421382091193488305821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139835790352243182635482189 52438421382091193488305821)
    ·
      refine ⟨19664408018284197558114683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52438421382091193488305821 19664408018284197558114683)
      ·
        refine ⟨29496612027426296337172025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19664408018284197558114683 29496612027426296337172025)
        ·
          refine ⟨22122459020569722252879019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29496612027426296337172025 22122459020569722252879019)
          ·
            refine ⟨33183688530854583379318529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22122459020569722252879019 33183688530854583379318529)
            ·
              refine ⟨24887766398140937534488897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33183688530854583379318529 24887766398140937534488897)
              ·
                refine ⟨18665824798605703150866673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24887766398140937534488897 18665824798605703150866673)
                ·
                  refine ⟨13999368598954277363150005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18665824798605703150866673 13999368598954277363150005)
                  ·
                    refine ⟨1312440806151963502795313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13999368598954277363150005 1312440806151963502795313)
                    ·
                      rfl

theorem cell23_7667908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_7667908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667908 prefixEnd_7667908 := by exact prefixLift 7667908
  have htrace : WordTrace (prefixWord ++ tailWord_7667908) baseStart_7667908 baseEnd_7667908 := by
    simpa [prefixWord, tailWord_7667908, baseEnd_7667908] using wordTrace_append hprefix tailTrace_7667908
  have hstable : (prefixWord ++ tailWord_7667908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667908).length < 2 ^ (prefixWord ++ tailWord_7667908).sum := by decide
  have hdescent : baseEnd_7667908 < baseStart_7667908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667928 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 1, 6, 2]
def baseStart_7667928 : Nat := 118140960795 + 7667928 * 2 ^ 59
def prefixEnd_7667928 : Nat := 4983230072969 + 3 ^ 40 * 7667928 * 2
def baseEnd_7667928 : Nat := 3937332688068980430135847

theorem tailTrace_7667928 : CollatzResearch.WordTrace tailWord_7667928 prefixEnd_7667928 3937332688068980430135847 := by
  unfold tailWord_7667928
  simp only [CollatzResearch.WordTrace]
  refine ⟨139836155082206954343346219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186448206776275939124461625 139836155082206954343346219)
  ·
    refine ⟨209754232623310431515019329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139836155082206954343346219 209754232623310431515019329)
    ·
      refine ⟨157315674467482823636264497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209754232623310431515019329 157315674467482823636264497)
      ·
        refine ⟨117986755850612117727198373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157315674467482823636264497 117986755850612117727198373)
        ·
          refine ⟨22122516721989772073849695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117986755850612117727198373 22122516721989772073849695)
          ·
            refine ⟨33183775082984658110774543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22122516721989772073849695 33183775082984658110774543)
            ·
              refine ⟨49775662624476987166161815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33183775082984658110774543 49775662624476987166161815)
              ·
                refine ⟨74663493936715480749242723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49775662624476987166161815 74663493936715480749242723)
                ·
                  refine ⟨111995240905073221123864085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74663493936715480749242723 111995240905073221123864085)
                  ·
                    refine ⟨5249776917425307240181129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111995240905073221123864085 5249776917425307240181129)
                    ·
                      refine ⟨3937332688068980430135847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5249776917425307240181129 3937332688068980430135847)
                      ·
                        rfl

theorem cell23_7667928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_7667928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667928 prefixEnd_7667928 := by exact prefixLift 7667928
  have htrace : WordTrace (prefixWord ++ tailWord_7667928) baseStart_7667928 baseEnd_7667928 := by
    simpa [prefixWord, tailWord_7667928, baseEnd_7667928] using wordTrace_append hprefix tailTrace_7667928
  have hstable : (prefixWord ++ tailWord_7667928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667928).length < 2 ^ (prefixWord ++ tailWord_7667928).sum := by decide
  have hdescent : baseEnd_7667928 < baseStart_7667928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667931 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 3]
def baseStart_7667931 : Nat := 118140960795 + 7667931 * 2 ^ 59
def prefixEnd_7667931 : Nat := 4983230072969 + 3 ^ 40 * 7667931 * 2
def baseEnd_7667931 : Nat := 3937334228510943918398333

theorem tailTrace_7667931 : CollatzResearch.WordTrace tailWord_7667931 prefixEnd_7667931 3937334228510943918398333 := by
  unfold tailWord_7667931
  simp only [CollatzResearch.WordTrace]
  refine ⟨279672419583403040199051647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186448279722268693466034431 279672419583403040199051647)
  ·
    refine ⟨419508629375104560298577471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279672419583403040199051647 419508629375104560298577471)
    ·
      refine ⟨629262944062656840447866207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419508629375104560298577471 629262944062656840447866207)
      ·
        refine ⟨943894416093985260671799311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629262944062656840447866207 943894416093985260671799311)
        ·
          refine ⟨1415841624140977891007698967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943894416093985260671799311 1415841624140977891007698967)
          ·
            refine ⟨2123762436211466836511548451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1415841624140977891007698967 2123762436211466836511548451)
            ·
              refine ⟨3185643654317200254767322677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2123762436211466836511548451 3185643654317200254767322677)
              ·
                refine ⟨298654092592237523884436501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3185643654317200254767322677 298654092592237523884436501)
                ·
                  refine ⟨13999410590261133932082961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 298654092592237523884436501 13999410590261133932082961)
                  ·
                    refine ⟨10499557942695850449062221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13999410590261133932082961 10499557942695850449062221)
                    ·
                      refine ⟨3937334228510943918398333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10499557942695850449062221 3937334228510943918398333)
                      ·
                        rfl

theorem cell23_7667931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 3].length) (baseStart_7667931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667931 prefixEnd_7667931 := by exact prefixLift 7667931
  have htrace : WordTrace (prefixWord ++ tailWord_7667931) baseStart_7667931 baseEnd_7667931 := by
    simpa [prefixWord, tailWord_7667931, baseEnd_7667931] using wordTrace_append hprefix tailTrace_7667931
  have hstable : (prefixWord ++ tailWord_7667931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667931).length < 2 ^ (prefixWord ++ tailWord_7667931).sum := by decide
  have hdescent : baseEnd_7667931 < baseStart_7667931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7667955 : List Nat := [1, 1, 1, 2, 2, 4, 4, 3, 1, 4]
def baseStart_7667955 : Nat := 118140960795 + 7667955 * 2 ^ 59
def prefixEnd_7667955 : Nat := 4983230072969 + 3 ^ 40 * 7667955 * 2
def baseEnd_7667955 : Nat := 1312448850682217274832741

theorem tailTrace_7667955 : CollatzResearch.WordTrace tailWord_7667955 prefixEnd_7667955 1312448850682217274832741 := by
  unfold tailWord_7667955
  simp only [CollatzResearch.WordTrace]
  refine ⟨279673294935316092297925319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186448863290210728198616879 279673294935316092297925319)
  ·
    refine ⟨419509942402974138446887979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279673294935316092297925319 419509942402974138446887979)
    ·
      refine ⟨629264913604461207670331969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419509942402974138446887979 629264913604461207670331969)
      ·
        refine ⟨471948685203345905752748977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629264913604461207670331969 471948685203345905752748977)
        ·
          refine ⟨353961513902509429314561733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471948685203345905752748977 353961513902509429314561733)
          ·
            refine ⟨66367783856720517996480325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 353961513902509429314561733 66367783856720517996480325)
            ·
              refine ⟨12443959473135097124340061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66367783856720517996480325 12443959473135097124340061)
              ·
                refine ⟨4666484802425661421627523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12443959473135097124340061 4666484802425661421627523)
                ·
                  refine ⟨6999727203638492132441285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4666484802425661421627523 6999727203638492132441285)
                  ·
                    refine ⟨1312448850682217274832741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6999727203638492132441285 1312448850682217274832741)
                    ·
                      rfl

theorem cell23_7667955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 1, 4].length) (baseStart_7667955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7667955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7667955 prefixEnd_7667955 := by exact prefixLift 7667955
  have htrace : WordTrace (prefixWord ++ tailWord_7667955) baseStart_7667955 baseEnd_7667955 := by
    simpa [prefixWord, tailWord_7667955, baseEnd_7667955] using wordTrace_append hprefix tailTrace_7667955
  have hstable : (prefixWord ++ tailWord_7667955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7667955).length < 2 ^ (prefixWord ++ tailWord_7667955).sum := by decide
  have hdescent : baseEnd_7667955 < baseStart_7667955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7667955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668012 : List Nat := [2, 2, 1, 1, 1, 3, 5, 3, 1, 1, 3]
def baseStart_7668012 : Nat := 118140960795 + 7668012 * 2 ^ 59
def prefixEnd_7668012 : Nat := 4983230072969 + 3 ^ 40 * 7668012 * 2
def baseEnd_7668012 : Nat := 3937375820443958101485461

theorem tailTrace_7668012 : CollatzResearch.WordTrace tailWord_7668012 prefixEnd_7668012 3937375820443958101485461 := by
  unfold tailWord_7668012
  simp only [CollatzResearch.WordTrace]
  refine ⟨139837686948054795516375145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186450249264073060688500193 139837686948054795516375145)
  ·
    refine ⟨104878265211041096637281359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139837686948054795516375145 104878265211041096637281359)
    ·
      refine ⟨157317397816561644955922039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104878265211041096637281359 157317397816561644955922039)
      ·
        refine ⟨235976096724842467433883059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157317397816561644955922039 235976096724842467433883059)
        ·
          refine ⟨353964145087263701150824589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235976096724842467433883059 353964145087263701150824589)
          ·
            refine ⟨132736554407723887931559221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353964145087263701150824589 132736554407723887931559221)
            ·
              refine ⟨12444051975724114493583677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132736554407723887931559221 12444051975724114493583677)
              ·
                refine ⟨4666519490896542935093879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12444051975724114493583677 4666519490896542935093879)
                ·
                  refine ⟨6999779236344814402640819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4666519490896542935093879 6999779236344814402640819)
                  ·
                    refine ⟨10499668854517221603961229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6999779236344814402640819 10499668854517221603961229)
                    ·
                      refine ⟨3937375820443958101485461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10499668854517221603961229 3937375820443958101485461)
                      ·
                        rfl

theorem cell23_7668012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 1, 1, 3].length) (baseStart_7668012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668012 prefixEnd_7668012 := by exact prefixLift 7668012
  have htrace : WordTrace (prefixWord ++ tailWord_7668012) baseStart_7668012 baseEnd_7668012 := by
    simpa [prefixWord, tailWord_7668012, baseEnd_7668012] using wordTrace_append hprefix tailTrace_7668012
  have hstable : (prefixWord ++ tailWord_7668012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668012).length < 2 ^ (prefixWord ++ tailWord_7668012).sum := by decide
  have hdescent : baseEnd_7668012 < baseStart_7668012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668028 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 4, 4]
def baseStart_7668028 : Nat := 118140960795 + 7668028 * 2 ^ 59
def prefixEnd_7668028 : Nat := 4983230072969 + 3 ^ 40 * 7668028 * 2
def baseEnd_7668028 : Nat := 1312461345378143346295129

theorem tailTrace_7668028 : CollatzResearch.WordTrace tailWord_7668028 prefixEnd_7668028 1312461345378143346295129 := by
  unfold tailWord_7668028
  simp only [CollatzResearch.WordTrace]
  refine ⟨139837978732025812882666369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186450638309367750510221825 139837978732025812882666369)
  ·
    refine ⟨104878484049019359661999777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139837978732025812882666369 104878484049019359661999777)
    ·
      refine ⟨78658863036764519746499833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104878484049019359661999777 78658863036764519746499833)
      ·
        refine ⟨58994147277573389809874875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78658863036764519746499833 58994147277573389809874875)
        ·
          refine ⟨88491220916360084714812313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58994147277573389809874875 88491220916360084714812313)
          ·
            refine ⟨66368415687270063536109235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88491220916360084714812313 66368415687270063536109235)
            ·
              refine ⟨99552623530905095304163853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66368415687270063536109235 99552623530905095304163853)
              ·
                refine ⟨37332233824089410739061445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99552623530905095304163853 37332233824089410739061445)
                ·
                  refine ⟨6999793842016764513574021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37332233824089410739061445 6999793842016764513574021)
                  ·
                    refine ⟨1312461345378143346295129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6999793842016764513574021 1312461345378143346295129)
                    ·
                      rfl

theorem cell23_7668028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_7668028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668028 prefixEnd_7668028 := by exact prefixLift 7668028
  have htrace : WordTrace (prefixWord ++ tailWord_7668028) baseStart_7668028 baseEnd_7668028 := by
    simpa [prefixWord, tailWord_7668028, baseEnd_7668028] using wordTrace_append hprefix tailTrace_7668028
  have hstable : (prefixWord ++ tailWord_7668028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668028).length < 2 ^ (prefixWord ++ tailWord_7668028).sum := by decide
  have hdescent : baseEnd_7668028 < baseStart_7668028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668031 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 6]
def baseStart_7668031 : Nat := 118140960795 + 7668031 * 2 ^ 59
def prefixEnd_7668031 : Nat := 4983230072969 + 3 ^ 40 * 7668031 * 2
def baseEnd_7668031 : Nat := 3937385576576393527147873

theorem tailTrace_7668031 : CollatzResearch.WordTrace tailWord_7668031 prefixEnd_7668031 3937385576576393527147873 := by
  unfold tailWord_7668031
  simp only [CollatzResearch.WordTrace]
  refine ⟨279676066883040757277691947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186450711255360504851794631 279676066883040757277691947)
  ·
    refine ⟨419514100324561135916537921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279676066883040757277691947 419514100324561135916537921)
    ·
      refine ⟨314635575243420851937403441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419514100324561135916537921 314635575243420851937403441)
      ·
        refine ⟨235976681432565638953052581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314635575243420851937403441 235976681432565638953052581)
        ·
          refine ⟨44245627768606057303697359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235976681432565638953052581 44245627768606057303697359)
          ·
            refine ⟨66368441652909085955546039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44245627768606057303697359 66368441652909085955546039)
            ·
              refine ⟨99552662479363628933319059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66368441652909085955546039 99552662479363628933319059)
              ·
                refine ⟨149328993719045443399978589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99552662479363628933319059 149328993719045443399978589)
                ·
                  refine ⟨55998372644642041274991971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149328993719045443399978589 55998372644642041274991971)
                  ·
                    refine ⟨83997558966963061912487957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55998372644642041274991971 83997558966963061912487957)
                    ·
                      refine ⟨3937385576576393527147873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83997558966963061912487957 3937385576576393527147873)
                      ·
                        rfl

theorem cell23_7668031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_7668031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668031 prefixEnd_7668031 := by exact prefixLift 7668031
  have htrace : WordTrace (prefixWord ++ tailWord_7668031) baseStart_7668031 baseEnd_7668031 := by
    simpa [prefixWord, tailWord_7668031, baseEnd_7668031] using wordTrace_append hprefix tailTrace_7668031
  have hstable : (prefixWord ++ tailWord_7668031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668031).length < 2 ^ (prefixWord ++ tailWord_7668031).sum := by decide
  have hdescent : baseEnd_7668031 < baseStart_7668031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668052 : List Nat := [2, 4, 1, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_7668052 : Nat := 118140960795 + 7668052 * 2 ^ 59
def prefixEnd_7668052 : Nat := 4983230072969 + 3 ^ 40 * 7668052 * 2
def baseEnd_7668052 : Nat := 3937396359670137944985277

theorem tailTrace_7668052 : CollatzResearch.WordTrace tailWord_7668052 prefixEnd_7668052 3937396359670137944985277 := by
  unfold tailWord_7668052
  simp only [CollatzResearch.WordTrace]
  refine ⟨139838416407982338932103205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186451221877309785242804273 139838416407982338932103205)
  ·
    refine ⟨26219703076496688549769351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139838416407982338932103205 26219703076496688549769351)
    ·
      refine ⟨39329554614745032824654027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26219703076496688549769351 39329554614745032824654027)
      ·
        refine ⟨58994331922117549236981041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39329554614745032824654027 58994331922117549236981041)
        ·
          refine ⟨44245748941588161927735781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58994331922117549236981041 44245748941588161927735781)
          ·
            refine ⟨8296077926547780361450459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44245748941588161927735781 8296077926547780361450459)
            ·
              refine ⟨12444116889821670542175689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8296077926547780361450459 12444116889821670542175689)
              ·
                refine ⟨9333087667366252906631767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12444116889821670542175689 9333087667366252906631767)
                ·
                  refine ⟨13999631501049379359947651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9333087667366252906631767 13999631501049379359947651)
                  ·
                    refine ⟨20999447251574069039921477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13999631501049379359947651 20999447251574069039921477)
                    ·
                      refine ⟨3937396359670137944985277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20999447251574069039921477 3937396359670137944985277)
                      ·
                        rfl

theorem cell23_7668052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_7668052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668052 prefixEnd_7668052 := by exact prefixLift 7668052
  have htrace : WordTrace (prefixWord ++ tailWord_7668052) baseStart_7668052 baseEnd_7668052 := by
    simpa [prefixWord, tailWord_7668052, baseEnd_7668052] using wordTrace_append hprefix tailTrace_7668052
  have hstable : (prefixWord ++ tailWord_7668052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668052).length < 2 ^ (prefixWord ++ tailWord_7668052).sum := by decide
  have hdescent : baseEnd_7668052 < baseStart_7668052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668136 : List Nat := [2, 1, 6, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_7668136 : Nat := 118140960795 + 7668136 * 2 ^ 59
def prefixEnd_7668136 : Nat := 4983230072969 + 3 ^ 40 * 7668136 * 2
def baseEnd_7668136 : Nat := 3937439492045115616334891

theorem tailTrace_7668136 : CollatzResearch.WordTrace tailWord_7668136 prefixEnd_7668136 3937439492045115616334891 := by
  unfold tailWord_7668136
  simp only [CollatzResearch.WordTrace]
  refine ⟨139839948273830180105132131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186453264365106906806842841 139839948273830180105132131)
  ·
    refine ⟨209759922410745270157698197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139839948273830180105132131 209759922410745270157698197)
    ·
      refine ⟨9832496363003684538642103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 209759922410745270157698197 9832496363003684538642103)
      ·
        refine ⟨14748744544505526807963155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9832496363003684538642103 14748744544505526807963155)
        ·
          refine ⟨22123116816758290211944733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14748744544505526807963155 22123116816758290211944733)
          ·
            refine ⟨8296168806284358829479275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22123116816758290211944733 8296168806284358829479275)
            ·
              refine ⟨12444253209426538244218913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8296168806284358829479275 12444253209426538244218913)
              ·
                refine ⟨9333189907069903683164185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12444253209426538244218913 9333189907069903683164185)
                ·
                  refine ⟨6999892430302427762373139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9333189907069903683164185 6999892430302427762373139)
                  ·
                    refine ⟨10499838645453641643559709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6999892430302427762373139 10499838645453641643559709)
                    ·
                      refine ⟨3937439492045115616334891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10499838645453641643559709 3937439492045115616334891)
                      ·
                        rfl

theorem cell23_7668136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_7668136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668136 prefixEnd_7668136 := by exact prefixLift 7668136
  have htrace : WordTrace (prefixWord ++ tailWord_7668136) baseStart_7668136 baseEnd_7668136 := by
    simpa [prefixWord, tailWord_7668136, baseEnd_7668136] using wordTrace_append hprefix tailTrace_7668136
  have hstable : (prefixWord ++ tailWord_7668136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668136).length < 2 ^ (prefixWord ++ tailWord_7668136).sum := by decide
  have hdescent : baseEnd_7668136 < baseStart_7668136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668205 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_7668205 : Nat := 118140960795 + 7668205 * 2 ^ 59
def prefixEnd_7668205 : Nat := 4983230072969 + 3 ^ 40 * 7668205 * 2
def baseEnd_7668205 : Nat := 3937474922210275846372073

theorem tailTrace_7668205 : CollatzResearch.WordTrace tailWord_7668205 prefixEnd_7668205 3937474922210275846372073 := by
  unfold tailWord_7668205
  simp only [CollatzResearch.WordTrace]
  refine ⟨279682413184410384994526069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186454942122940256663017379 279682413184410384994526069)
  ·
    refine ⟨26220226236038473593236819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279682413184410384994526069 26220226236038473593236819)
    ·
      refine ⟨39330339354057710389855229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26220226236038473593236819 39330339354057710389855229)
      ·
        refine ⟨14748877257771641396195711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39330339354057710389855229 14748877257771641396195711)
        ·
          refine ⟨22123315886657462094293567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14748877257771641396195711 22123315886657462094293567)
          ·
            refine ⟨33184973829986193141440351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22123315886657462094293567 33184973829986193141440351)
            ·
              refine ⟨49777460744979289712160527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33184973829986193141440351 49777460744979289712160527)
              ·
                refine ⟨74666191117468934568240791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49777460744979289712160527 74666191117468934568240791)
                ·
                  refine ⟨111999286676203401852361187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74666191117468934568240791 111999286676203401852361187)
                  ·
                    refine ⟨167998930014305102778541781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111999286676203401852361187 167998930014305102778541781)
                    ·
                      refine ⟨3937474922210275846372073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167998930014305102778541781 3937474922210275846372073)
                      ·
                        rfl

theorem cell23_7668205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_7668205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668205 prefixEnd_7668205 := by exact prefixLift 7668205
  have htrace : WordTrace (prefixWord ++ tailWord_7668205) baseStart_7668205 baseEnd_7668205 := by
    simpa [prefixWord, tailWord_7668205, baseEnd_7668205] using wordTrace_append hprefix tailTrace_7668205
  have hstable : (prefixWord ++ tailWord_7668205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668205).length < 2 ^ (prefixWord ++ tailWord_7668205).sum := by decide
  have hdescent : baseEnd_7668205 < baseStart_7668205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668210 : List Nat := [3, 2, 1, 4, 3, 1, 2, 1, 2, 2, 2]
def baseStart_7668210 : Nat := 118140960795 + 7668210 * 2 ^ 59
def prefixEnd_7668210 : Nat := 4983230072969 + 3 ^ 40 * 7668210 * 2
def baseEnd_7668210 : Nat := 3937477489613548326809551

theorem tailTrace_7668210 : CollatzResearch.WordTrace tailWord_7668210 prefixEnd_7668210 3937477489613548326809551 := by
  unfold tailWord_7668210
  simp only [CollatzResearch.WordTrace]
  refine ⟨69920648887348067712114521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186455063699594847232305389 69920648887348067712114521)
  ·
    refine ⟨52440486665511050784085891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69920648887348067712114521 52440486665511050784085891)
    ·
      refine ⟨78660729998266576176128837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52440486665511050784085891 78660729998266576176128837)
      ·
        refine ⟨14748886874674983033024157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78660729998266576176128837 14748886874674983033024157)
        ·
          refine ⟨5530832578003118637384059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14748886874674983033024157 5530832578003118637384059)
          ·
            refine ⟨8296248867004677956076089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5530832578003118637384059 8296248867004677956076089)
            ·
              refine ⟨6222186650253508467057067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8296248867004677956076089 6222186650253508467057067)
              ·
                refine ⟨9333279975380262700585601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6222186650253508467057067 9333279975380262700585601)
                ·
                  refine ⟨6999959981535197025439201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9333279975380262700585601 6999959981535197025439201)
                  ·
                    refine ⟨5249969986151397769079401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6999959981535197025439201 5249969986151397769079401)
                    ·
                      refine ⟨3937477489613548326809551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5249969986151397769079401 3937477489613548326809551)
                      ·
                        rfl

theorem cell23_7668210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_7668210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668210 prefixEnd_7668210 := by exact prefixLift 7668210
  have htrace : WordTrace (prefixWord ++ tailWord_7668210) baseStart_7668210 baseEnd_7668210 := by
    simpa [prefixWord, tailWord_7668210, baseEnd_7668210] using wordTrace_append hprefix tailTrace_7668210
  have hstable : (prefixWord ++ tailWord_7668210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668210).length < 2 ^ (prefixWord ++ tailWord_7668210).sum := by decide
  have hdescent : baseEnd_7668210 < baseStart_7668210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668215 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 6, 4, 2]
def baseStart_7668215 : Nat := 118140960795 + 7668215 * 2 ^ 59
def prefixEnd_7668215 : Nat := 4983230072969 + 3 ^ 40 * 7668215 * 2
def baseEnd_7668215 : Nat := 3937480057016820807247027

theorem tailTrace_7668215 : CollatzResearch.WordTrace tailWord_7668215 prefixEnd_7668215 3937480057016820807247027 := by
  unfold tailWord_7668215
  simp only [CollatzResearch.WordTrace]
  refine ⟨279682777914374156702390099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186455185276249437801593399 279682777914374156702390099)
  ·
    refine ⟨419524166871561235053585149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279682777914374156702390099 419524166871561235053585149)
    ·
      refine ⟨157321562576835463145094431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419524166871561235053585149 157321562576835463145094431)
      ·
        refine ⟨235982343865253194717641647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157321562576835463145094431 235982343865253194717641647)
        ·
          refine ⟨353973515797879792076462471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235982343865253194717641647 353973515797879792076462471)
          ·
            refine ⟨530960273696819688114693707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353973515797879792076462471 530960273696819688114693707)
            ·
              refine ⟨796440410545229532172040561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530960273696819688114693707 796440410545229532172040561)
              ·
                refine ⟨597330307908922149129030421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796440410545229532172040561 597330307908922149129030421)
                ·
                  refine ⟨27999858183230725740423301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 597330307908922149129030421 27999858183230725740423301)
                  ·
                    refine ⟨5249973409355761076329369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27999858183230725740423301 5249973409355761076329369)
                    ·
                      refine ⟨3937480057016820807247027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5249973409355761076329369 3937480057016820807247027)
                      ·
                        rfl

theorem cell23_7668215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 4, 2].length) (baseStart_7668215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668215 prefixEnd_7668215 := by exact prefixLift 7668215
  have htrace : WordTrace (prefixWord ++ tailWord_7668215) baseStart_7668215 baseEnd_7668215 := by
    simpa [prefixWord, tailWord_7668215, baseEnd_7668215] using wordTrace_append hprefix tailTrace_7668215
  have hstable : (prefixWord ++ tailWord_7668215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668215).length < 2 ^ (prefixWord ++ tailWord_7668215).sum := by decide
  have hdescent : baseEnd_7668215 < baseStart_7668215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668252 : List Nat := [2, 2, 3, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_7668252 : Nat := 118140960795 + 7668252 * 2 ^ 59
def prefixEnd_7668252 : Nat := 4983230072969 + 3 ^ 40 * 7668252 * 2
def baseEnd_7668252 : Nat := 3937499055801037162484357

theorem tailTrace_7668252 : CollatzResearch.WordTrace tailWord_7668252 prefixEnd_7668252 3937499055801037162484357 := by
  unfold tailWord_7668252
  simp only [CollatzResearch.WordTrace]
  refine ⟨139842063707620056010743505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186456084943493408014324673 139842063707620056010743505)
  ·
    refine ⟨104881547780715042008057629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139842063707620056010743505 104881547780715042008057629)
    ·
      refine ⟨39330580417768140753021611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104881547780715042008057629 39330580417768140753021611)
      ·
        refine ⟨58995870626652211129532417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39330580417768140753021611 58995870626652211129532417)
        ·
          refine ⟨44246902969989158347149313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58995870626652211129532417 44246902969989158347149313)
          ·
            refine ⟨33185177227491868760361985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44246902969989158347149313 33185177227491868760361985)
            ·
              refine ⟨24888882920618901570271489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33185177227491868760361985 24888882920618901570271489)
              ·
                refine ⟨18666662190464176177703617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24888882920618901570271489 18666662190464176177703617)
                ·
                  refine ⟨13999996642848132133277713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18666662190464176177703617 13999996642848132133277713)
                  ·
                    refine ⟨10499997482136099099958285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13999996642848132133277713 10499997482136099099958285)
                    ·
                      refine ⟨3937499055801037162484357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10499997482136099099958285 3937499055801037162484357)
                      ·
                        rfl

theorem cell23_7668252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_7668252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668252 prefixEnd_7668252 := by exact prefixLift 7668252
  have htrace : WordTrace (prefixWord ++ tailWord_7668252) baseStart_7668252 baseEnd_7668252 := by
    simpa [prefixWord, tailWord_7668252, baseEnd_7668252] using wordTrace_append hprefix tailTrace_7668252
  have hstable : (prefixWord ++ tailWord_7668252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668252).length < 2 ^ (prefixWord ++ tailWord_7668252).sum := by decide
  have hdescent : baseEnd_7668252 < baseStart_7668252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668259 : List Nat := [1, 1, 1, 4, 4, 2, 1, 4, 1, 4]
def baseStart_7668259 : Nat := 118140960795 + 7668259 * 2 ^ 59
def prefixEnd_7668259 : Nat := 4983230072969 + 3 ^ 40 * 7668259 * 2
def baseEnd_7668259 : Nat := 1312500883388539545032275

theorem tailTrace_7668259 : CollatzResearch.WordTrace tailWord_7668259 prefixEnd_7668259 1312500883388539545032275 := by
  unfold tailWord_7668259
  simp only [CollatzResearch.WordTrace]
  refine ⟨279684382726214752216991831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186456255150809834811327887 279684382726214752216991831)
  ·
    refine ⟨419526574089322128325487747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279684382726214752216991831 419526574089322128325487747)
    ·
      refine ⟨629289861133983192488231621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419526574089322128325487747 629289861133983192488231621)
      ·
        refine ⟨117991848962621848591543429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 629289861133983192488231621 117991848962621848591543429)
        ·
          refine ⟨22123471680491596610914393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117991848962621848591543429 22123471680491596610914393)
          ·
            refine ⟨16592603760368697458185795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22123471680491596610914393 16592603760368697458185795)
            ·
              refine ⟨24888905640553046187278693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16592603760368697458185795 24888905640553046187278693)
              ·
                refine ⟨4666669807603696160114755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24888905640553046187278693 4666669807603696160114755)
                ·
                  refine ⟨7000004711405544240172133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4666669807603696160114755 7000004711405544240172133)
                  ·
                    refine ⟨1312500883388539545032275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7000004711405544240172133 1312500883388539545032275)
                    ·
                      rfl

theorem cell23_7668259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 1, 4].length) (baseStart_7668259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668259 prefixEnd_7668259 := by exact prefixLift 7668259
  have htrace : WordTrace (prefixWord ++ tailWord_7668259) baseStart_7668259 baseEnd_7668259 := by
    simpa [prefixWord, tailWord_7668259, baseEnd_7668259] using wordTrace_append hprefix tailTrace_7668259
  have hstable : (prefixWord ++ tailWord_7668259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668259).length < 2 ^ (prefixWord ++ tailWord_7668259).sum := by decide
  have hdescent : baseEnd_7668259 < baseStart_7668259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668276 : List Nat := [2, 5, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_7668276 : Nat := 118140960795 + 7668276 * 2 ^ 59
def prefixEnd_7668276 : Nat := 4983230072969 + 3 ^ 40 * 7668276 * 2
def baseEnd_7668276 : Nat := 1312503793112248356194749

theorem tailTrace_7668276 : CollatzResearch.WordTrace tailWord_7668276 prefixEnd_7668276 1312503793112248356194749 := by
  unfold tailWord_7668276
  simp only [CollatzResearch.WordTrace]
  refine ⟨139842501383576582060180341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186456668511435442746907121 139842501383576582060180341)
  ·
    refine ⟨13110234504710304568141907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139842501383576582060180341 13110234504710304568141907)
    ·
      refine ⟨19665351757065456852212861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13110234504710304568141907 19665351757065456852212861)
      ·
        refine ⟨7374506908899546319579823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19665351757065456852212861 7374506908899546319579823)
        ·
          refine ⟨11061760363349319479369735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7374506908899546319579823 11061760363349319479369735)
          ·
            refine ⟨16592640545023979219054603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11061760363349319479369735 16592640545023979219054603)
            ·
              refine ⟨24888960817535968828581905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16592640545023979219054603 24888960817535968828581905)
              ·
                refine ⟨18666720613151976621436429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24888960817535968828581905 18666720613151976621436429)
                ·
                  refine ⟨7000020229931991233038661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18666720613151976621436429 7000020229931991233038661)
                  ·
                    refine ⟨1312503793112248356194749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7000020229931991233038661 1312503793112248356194749)
                    ·
                      rfl

theorem cell23_7668276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_7668276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668276 prefixEnd_7668276 := by exact prefixLift 7668276
  have htrace : WordTrace (prefixWord ++ tailWord_7668276) baseStart_7668276 baseEnd_7668276 := by
    simpa [prefixWord, tailWord_7668276, baseEnd_7668276] using wordTrace_append hprefix tailTrace_7668276
  have hstable : (prefixWord ++ tailWord_7668276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668276).length < 2 ^ (prefixWord ++ tailWord_7668276).sum := by decide
  have hdescent : baseEnd_7668276 < baseStart_7668276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668282 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3]
def baseStart_7668282 : Nat := 118140960795 + 7668282 * 2 ^ 59
def prefixEnd_7668282 : Nat := 4983230072969 + 3 ^ 40 * 7668282 * 2
def baseEnd_7668282 : Nat := 3937514460220672045109219

theorem tailTrace_7668282 : CollatzResearch.WordTrace tailWord_7668282 prefixEnd_7668282 3937514460220672045109219 := by
  unfold tailWord_7668282
  simp only [CollatzResearch.WordTrace]
  refine ⟨69921305401282856786269775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186456814403420951430052733 69921305401282856786269775)
  ·
    refine ⟨104881958101924285179404663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69921305401282856786269775 104881958101924285179404663)
    ·
      refine ⟨157322937152886427769106995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104881958101924285179404663 157322937152886427769106995)
      ·
        refine ⟨235984405729329641653660493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157322937152886427769106995 235984405729329641653660493)
        ·
          refine ⟨88494152148498615620122685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235984405729329641653660493 88494152148498615620122685)
          ·
            refine ⟨33185307055686980857546007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88494152148498615620122685 33185307055686980857546007)
            ·
              refine ⟨49777960583530471286319011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33185307055686980857546007 49777960583530471286319011)
              ·
                refine ⟨74666940875295706929478517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49777960583530471286319011 74666940875295706929478517)
                ·
                  refine ⟨7000025707058972524638611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74666940875295706929478517 7000025707058972524638611)
                  ·
                    refine ⟨10500038560588458786957917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7000025707058972524638611 10500038560588458786957917)
                    ·
                      refine ⟨3937514460220672045109219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10500038560588458786957917 3937514460220672045109219)
                      ·
                        rfl

theorem cell23_7668282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3].length) (baseStart_7668282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668282 prefixEnd_7668282 := by exact prefixLift 7668282
  have htrace : WordTrace (prefixWord ++ tailWord_7668282) baseStart_7668282 baseEnd_7668282 := by
    simpa [prefixWord, tailWord_7668282, baseEnd_7668282] using wordTrace_append hprefix tailTrace_7668282
  have hstable : (prefixWord ++ tailWord_7668282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668282).length < 2 ^ (prefixWord ++ tailWord_7668282).sum := by decide
  have hdescent : baseEnd_7668282 < baseStart_7668282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668299 : List Nat := [1, 1, 1, 1, 3, 1, 5, 5, 1, 1, 3]
def baseStart_7668299 : Nat := 118140960795 + 7668299 * 2 ^ 59
def prefixEnd_7668299 : Nat := 4983230072969 + 3 ^ 40 * 7668299 * 2
def baseEnd_7668299 : Nat := 3937523189391798478596641

theorem tailTrace_7668299 : CollatzResearch.WordTrace tailWord_7668299 prefixEnd_7668299 3937523189391798478596641 := by
  unfold tailWord_7668299
  simp only [CollatzResearch.WordTrace]
  refine ⟨279685841646069839048447951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186457227764046559365631967 279685841646069839048447951)
  ·
    refine ⟨419528762469104758572671927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279685841646069839048447951 419528762469104758572671927)
    ·
      refine ⟨629293143703657137859007891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419528762469104758572671927 629293143703657137859007891)
      ·
        refine ⟨943939715555485706788511837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629293143703657137859007891 943939715555485706788511837)
        ·
          refine ⟨353977393333307140045691939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 943939715555485706788511837 353977393333307140045691939)
          ·
            refine ⟨530966089999960710068537909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353977393333307140045691939 530966089999960710068537909)
            ·
              refine ⟨49778070937496316568925429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 530966089999960710068537909 49778070937496316568925429)
              ·
                refine ⟨4666694150390279678336759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49778070937496316568925429 4666694150390279678336759)
                ·
                  refine ⟨7000041225585419517505139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4666694150390279678336759 7000041225585419517505139)
                  ·
                    refine ⟨10500061838378129276257709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7000041225585419517505139 10500061838378129276257709)
                    ·
                      refine ⟨3937523189391798478596641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10500061838378129276257709 3937523189391798478596641)
                      ·
                        rfl

theorem cell23_7668299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 1, 1, 3].length) (baseStart_7668299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668299 prefixEnd_7668299 := by exact prefixLift 7668299
  have htrace : WordTrace (prefixWord ++ tailWord_7668299) baseStart_7668299 baseEnd_7668299 := by
    simpa [prefixWord, tailWord_7668299, baseEnd_7668299] using wordTrace_append hprefix tailTrace_7668299
  have hstable : (prefixWord ++ tailWord_7668299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668299).length < 2 ^ (prefixWord ++ tailWord_7668299).sum := by decide
  have hdescent : baseEnd_7668299 < baseStart_7668299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668316 : List Nat := [2, 2, 4, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_7668316 : Nat := 118140960795 + 7668316 * 2 ^ 59
def prefixEnd_7668316 : Nat := 4983230072969 + 3 ^ 40 * 7668316 * 2
def baseEnd_7668316 : Nat := 3937531918562924912084063

theorem tailTrace_7668316 : CollatzResearch.WordTrace tailWord_7668316 prefixEnd_7668316 3937531918562924912084063 := by
  unfold tailWord_7668316
  simp only [CollatzResearch.WordTrace]
  refine ⟨139843230843504125475908401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186457641124672167301211201 139843230843504125475908401)
  ·
    refine ⟨104882423132628094106931301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139843230843504125475908401 104882423132628094106931301)
    ·
      refine ⟨19665454337367767645049619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104882423132628094106931301 19665454337367767645049619)
      ·
        refine ⟨29498181506051651467574429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19665454337367767645049619 29498181506051651467574429)
        ·
          refine ⟨11061818064769369300340411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29498181506051651467574429 11061818064769369300340411)
          ·
            refine ⟨16592727097154053950510617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11061818064769369300340411 16592727097154053950510617)
            ·
              refine ⟨12444545322865540462882963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16592727097154053950510617 12444545322865540462882963)
              ·
                refine ⟨18666817984298310694324445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12444545322865540462882963 18666817984298310694324445)
                ·
                  refine ⟨7000056744111866510371667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18666817984298310694324445 7000056744111866510371667)
                  ·
                    refine ⟨10500085116167799765557501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7000056744111866510371667 10500085116167799765557501)
                    ·
                      refine ⟨3937531918562924912084063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10500085116167799765557501 3937531918562924912084063)
                      ·
                        rfl

theorem cell23_7668316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_7668316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668316 prefixEnd_7668316 := by exact prefixLift 7668316
  have htrace : WordTrace (prefixWord ++ tailWord_7668316) baseStart_7668316 baseEnd_7668316 := by
    simpa [prefixWord, tailWord_7668316, baseEnd_7668316] using wordTrace_append hprefix tailTrace_7668316
  have hstable : (prefixWord ++ tailWord_7668316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668316).length < 2 ^ (prefixWord ++ tailWord_7668316).sum := by decide
  have hdescent : baseEnd_7668316 < baseStart_7668316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668332 : List Nat := [2, 2, 1, 1, 3, 1, 2, 5, 2, 4]
def baseStart_7668332 : Nat := 118140960795 + 7668332 * 2 ^ 59
def prefixEnd_7668332 : Nat := 4983230072969 + 3 ^ 40 * 7668332 * 2
def baseEnd_7668332 : Nat := 1312513378084465616494663

theorem tailTrace_7668332 : CollatzResearch.WordTrace tailWord_7668332 prefixEnd_7668332 1312513378084465616494663 := by
  unfold tailWord_7668332
  simp only [CollatzResearch.WordTrace]
  refine ⟨139843522627475142842199625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186458030169966857122932833 139843522627475142842199625)
  ·
    refine ⟨104882641970606357131649719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139843522627475142842199625 104882641970606357131649719)
    ·
      refine ⟨157323962955909535697474579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104882641970606357131649719 157323962955909535697474579)
      ·
        refine ⟨235985944433864303546211869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157323962955909535697474579 235985944433864303546211869)
        ·
          refine ⟨88494729162699113829829451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235985944433864303546211869 88494729162699113829829451)
          ·
            refine ⟨132742093744048670744744177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88494729162699113829829451 132742093744048670744744177)
            ·
              refine ⟨99556570308036503058558133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132742093744048670744744177 99556570308036503058558133)
              ·
                refine ⟨9333428466378422161739825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99556570308036503058558133 9333428466378422161739825)
                ·
                  refine ⟨7000071349783816621304869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9333428466378422161739825 7000071349783816621304869)
                  ·
                    refine ⟨1312513378084465616494663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7000071349783816621304869 1312513378084465616494663)
                    ·
                      rfl

theorem cell23_7668332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_7668332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668332 prefixEnd_7668332 := by exact prefixLift 7668332
  have htrace : WordTrace (prefixWord ++ tailWord_7668332) baseStart_7668332 baseEnd_7668332 := by
    simpa [prefixWord, tailWord_7668332, baseEnd_7668332] using wordTrace_append hprefix tailTrace_7668332
  have hstable : (prefixWord ++ tailWord_7668332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668332).length < 2 ^ (prefixWord ++ tailWord_7668332).sum := by decide
  have hdescent : baseEnd_7668332 < baseStart_7668332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668345 : List Nat := [1, 2, 1, 3, 3, 3, 1, 9]
def baseStart_7668345 : Nat := 118140960795 + 7668345 * 2 ^ 59
def prefixEnd_7668345 : Nat := 4983230072969 + 3 ^ 40 * 7668345 * 2
def baseEnd_7668345 : Nat := 145835067018589085134127

theorem tailTrace_7668345 : CollatzResearch.WordTrace tailWord_7668345 prefixEnd_7668345 145835067018589085134127 := by
  unfold tailWord_7668345
  simp only [CollatzResearch.WordTrace]
  refine ⟨279687519403903188904622489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186458346269268792603081659 279687519403903188904622489)
  ·
    refine ⟨209765639552927391678466867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279687519403903188904622489 209765639552927391678466867)
    ·
      refine ⟨314648459329391087517700301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209765639552927391678466867 314648459329391087517700301)
      ·
        refine ⟨117993172248521657819137613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314648459329391087517700301 117993172248521657819137613)
        ·
          refine ⟨44247439593195621682176605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117993172248521657819137613 44247439593195621682176605)
          ·
            refine ⟨16592789847448358130816227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44247439593195621682176605 16592789847448358130816227)
            ·
              refine ⟨24889184771172537196224341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16592789847448358130816227 24889184771172537196224341)
              ·
                refine ⟨145835067018589085134127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24889184771172537196224341 145835067018589085134127)
                ·
                  rfl

theorem cell23_7668345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 9].length) (baseStart_7668345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668345 prefixEnd_7668345 := by exact prefixLift 7668345
  have htrace : WordTrace (prefixWord ++ tailWord_7668345) baseStart_7668345 baseEnd_7668345 := by
    simpa [prefixWord, tailWord_7668345, baseEnd_7668345] using wordTrace_append hprefix tailTrace_7668345
  have hstable : (prefixWord ++ tailWord_7668345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668345).length < 2 ^ (prefixWord ++ tailWord_7668345).sum := by decide
  have hdescent : baseEnd_7668345 < baseStart_7668345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668362 : List Nat := [3, 1, 2, 3, 3, 2, 9]
def baseStart_7668362 : Nat := 118140960795 + 7668362 * 2 ^ 59
def prefixEnd_7668362 : Nat := 4983230072969 + 3 ^ 40 * 7668362 * 2
def baseEnd_7668362 : Nat := 48611796773741132495171

theorem tailTrace_7668362 : CollatzResearch.WordTrace tailWord_7668362 prefixEnd_7668362 48611796773741132495171 := by
  unfold tailWord_7668362
  simp only [CollatzResearch.WordTrace]
  refine ⟨69922034861210400201997835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186458759629894400538660893 69922034861210400201997835)
  ·
    refine ⟨104883052291815600302996753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69922034861210400201997835 104883052291815600302996753)
    ·
      refine ⟨78662289218861700227247565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104883052291815600302996753 78662289218861700227247565)
      ·
        refine ⟨29498358457073137585217837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78662289218861700227247565 29498358457073137585217837)
        ·
          refine ⟨11061884421402426594456689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29498358457073137585217837 11061884421402426594456689)
          ·
            refine ⟨8296413316051819945842517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11061884421402426594456689 8296413316051819945842517)
            ·
              refine ⟨48611796773741132495171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8296413316051819945842517 48611796773741132495171)
              ·
                rfl

theorem cell23_7668362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 9].length) (baseStart_7668362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668362 prefixEnd_7668362 := by exact prefixLift 7668362
  have htrace : WordTrace (prefixWord ++ tailWord_7668362) baseStart_7668362 baseEnd_7668362 := by
    simpa [prefixWord, tailWord_7668362, baseEnd_7668362] using wordTrace_append hprefix tailTrace_7668362
  have hstable : (prefixWord ++ tailWord_7668362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668362).length < 2 ^ (prefixWord ++ tailWord_7668362).sum := by decide
  have hdescent : baseEnd_7668362 < baseStart_7668362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668375 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 2, 7]
def baseStart_7668375 : Nat := 118140960795 + 7668375 * 2 ^ 59
def prefixEnd_7668375 : Nat := 4983230072969 + 3 ^ 40 * 7668375 * 2
def baseEnd_7668375 : Nat := 1312520737973846727082097

theorem tailTrace_7668375 : CollatzResearch.WordTrace tailWord_7668375 prefixEnd_7668375 1312520737973846727082097 := by
  unfold tailWord_7668375
  simp only [CollatzResearch.WordTrace]
  refine ⟨279688613593794504028214579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186459075729196336018809719 279688613593794504028214579)
  ·
    refine ⟨419532920390691756042321869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279688613593794504028214579 419532920390691756042321869)
    ·
      refine ⟨157324845146509408515870701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419532920390691756042321869 157324845146509408515870701)
      ·
        refine ⟨58996816929941028193451513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157324845146509408515870701 58996816929941028193451513)
        ·
          refine ⟨44247612697455771145088635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58996816929941028193451513 44247612697455771145088635)
          ·
            refine ⟨66371419046183656717632953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44247612697455771145088635 66371419046183656717632953)
            ·
              refine ⟨49778564284637742538224715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66371419046183656717632953 49778564284637742538224715)
              ·
                refine ⟨74667846426956613807337073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49778564284637742538224715 74667846426956613807337073)
                ·
                  refine ⟨56000884820217460355502805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74667846426956613807337073 56000884820217460355502805)
                  ·
                    refine ⟨1312520737973846727082097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56000884820217460355502805 1312520737973846727082097)
                    ·
                      rfl

theorem cell23_7668375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_7668375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668375 prefixEnd_7668375 := by exact prefixLift 7668375
  have htrace : WordTrace (prefixWord ++ tailWord_7668375) baseStart_7668375 baseEnd_7668375 := by
    simpa [prefixWord, tailWord_7668375, baseEnd_7668375] using wordTrace_append hprefix tailTrace_7668375
  have hstable : (prefixWord ++ tailWord_7668375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668375).length < 2 ^ (prefixWord ++ tailWord_7668375).sum := by decide
  have hdescent : baseEnd_7668375 < baseStart_7668375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668382 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_7668382 : Nat := 118140960795 + 7668382 * 2 ^ 59
def prefixEnd_7668382 : Nat := 4983230072969 + 3 ^ 40 * 7668382 * 2
def baseEnd_7668382 : Nat := 3937565808286121653858759

theorem tailTrace_7668382 : CollatzResearch.WordTrace tailWord_7668382 prefixEnd_7668382 3937565808286121653858759 := by
  unfold tailWord_7668382
  simp only [CollatzResearch.WordTrace]
  refine ⟨34961108613096143027964925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186459245936512762815812933 34961108613096143027964925)
  ·
    refine ⟨13110415729911053635486847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34961108613096143027964925 13110415729911053635486847)
    ·
      refine ⟨19665623594866580453230271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13110415729911053635486847 19665623594866580453230271)
      ·
        refine ⟨29498435392299870679845407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19665623594866580453230271 29498435392299870679845407)
        ·
          refine ⟨44247653088449806019768111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29498435392299870679845407 44247653088449806019768111)
          ·
            refine ⟨66371479632674709029652167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44247653088449806019768111 66371479632674709029652167)
            ·
              refine ⟨99557219449012063544478251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66371479632674709029652167 99557219449012063544478251)
              ·
                refine ⟨149335829173518095316717377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99557219449012063544478251 149335829173518095316717377)
                ·
                  refine ⟨112001871880138571487538033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149335829173518095316717377 112001871880138571487538033)
                  ·
                    refine ⟨84001403910103928615653525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112001871880138571487538033 84001403910103928615653525)
                    ·
                      refine ⟨3937565808286121653858759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84001403910103928615653525 3937565808286121653858759)
                      ·
                        rfl

theorem cell23_7668382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_7668382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668382 prefixEnd_7668382 := by exact prefixLift 7668382
  have htrace : WordTrace (prefixWord ++ tailWord_7668382) baseStart_7668382 baseEnd_7668382 := by
    simpa [prefixWord, tailWord_7668382, baseEnd_7668382] using wordTrace_append hprefix tailTrace_7668382
  have hstable : (prefixWord ++ tailWord_7668382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668382).length < 2 ^ (prefixWord ++ tailWord_7668382).sum := by decide
  have hdescent : baseEnd_7668382 < baseStart_7668382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668399 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 3, 3, 2]
def baseStart_7668399 : Nat := 118140960795 + 7668399 * 2 ^ 59
def prefixEnd_7668399 : Nat := 4983230072969 + 3 ^ 40 * 7668399 * 2
def baseEnd_7668399 : Nat := 3937574537457248087346181

theorem tailTrace_7668399 : CollatzResearch.WordTrace tailWord_7668399 prefixEnd_7668399 3937574537457248087346181 := by
  unfold tailWord_7668399
  simp only [CollatzResearch.WordTrace]
  refine ⟨279689488945707556127088251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186459659297138370751392167 279689488945707556127088251)
  ·
    refine ⟨419534233418561334190632377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279689488945707556127088251 419534233418561334190632377)
    ·
      refine ⟨314650675063921000642974283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419534233418561334190632377 314650675063921000642974283)
      ·
        refine ⟨471976012595881500964461425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314650675063921000642974283 471976012595881500964461425)
        ·
          refine ⟨353982009446911125723346069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471976012595881500964461425 353982009446911125723346069)
          ·
            refine ⟨16592906692823959018281847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 353982009446911125723346069 16592906692823959018281847)
            ·
              refine ⟨24889360039235938527422771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16592906692823959018281847 24889360039235938527422771)
              ·
                refine ⟨37334040058853907791134157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24889360039235938527422771 37334040058853907791134157)
                ·
                  refine ⟨14000265022070215421675309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37334040058853907791134157 14000265022070215421675309)
                  ·
                    refine ⟨5250099383276330783128241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14000265022070215421675309 5250099383276330783128241)
                    ·
                      refine ⟨3937574537457248087346181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5250099383276330783128241 3937574537457248087346181)
                      ·
                        rfl

theorem cell23_7668399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 3, 2].length) (baseStart_7668399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668399 prefixEnd_7668399 := by exact prefixLift 7668399
  have htrace : WordTrace (prefixWord ++ tailWord_7668399) baseStart_7668399 baseEnd_7668399 := by
    simpa [prefixWord, tailWord_7668399, baseEnd_7668399] using wordTrace_append hprefix tailTrace_7668399
  have hstable : (prefixWord ++ tailWord_7668399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668399).length < 2 ^ (prefixWord ++ tailWord_7668399).sum := by decide
  have hdescent : baseEnd_7668399 < baseStart_7668399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668425 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 5, 4, 4]
def baseStart_7668425 : Nat := 118140960795 + 7668425 * 2 ^ 59
def prefixEnd_7668425 : Nat := 4983230072969 + 3 ^ 40 * 7668425 * 2
def baseEnd_7668425 : Nat := 3937587887954264985621061

theorem tailTrace_7668425 : CollatzResearch.WordTrace tailWord_7668425 prefixEnd_7668425 3937587887954264985621061 := by
  unfold tailWord_7668425
  simp only [CollatzResearch.WordTrace]
  refine ⟨279690437243613362567534729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186460291495742241711689819 279690437243613362567534729)
  ·
    refine ⟨209767827932710021925651047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279690437243613362567534729 209767827932710021925651047)
    ·
      refine ⟨314651741899065032888476571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209767827932710021925651047 314651741899065032888476571)
      ·
        refine ⟨471977612848597549332714857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314651741899065032888476571 471977612848597549332714857)
        ·
          refine ⟨353983209636448161999536143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471977612848597549332714857 353983209636448161999536143)
          ·
            refine ⟨530974814454672242999304215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353983209636448161999536143 530974814454672242999304215)
            ·
              refine ⟨796462221682008364498956323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530974814454672242999304215 796462221682008364498956323)
              ·
                refine ⟨1194693332523012546748434485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796462221682008364498956323 1194693332523012546748434485)
                ·
                  refine ⟨112002499924032426257665733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1194693332523012546748434485 112002499924032426257665733)
                  ·
                    refine ⟨21000468735756079923312325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112002499924032426257665733 21000468735756079923312325)
                    ·
                      refine ⟨3937587887954264985621061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21000468735756079923312325 3937587887954264985621061)
                      ·
                        rfl

theorem cell23_7668425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_7668425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668425 prefixEnd_7668425 := by exact prefixLift 7668425
  have htrace : WordTrace (prefixWord ++ tailWord_7668425) baseStart_7668425 baseEnd_7668425 := by
    simpa [prefixWord, tailWord_7668425, baseEnd_7668425] using wordTrace_append hprefix tailTrace_7668425
  have hstable : (prefixWord ++ tailWord_7668425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668425).length < 2 ^ (prefixWord ++ tailWord_7668425).sum := by decide
  have hdescent : baseEnd_7668425 < baseStart_7668425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668442 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4]
def baseStart_7668442 : Nat := 118140960795 + 7668442 * 2 ^ 59
def prefixEnd_7668442 : Nat := 4983230072969 + 3 ^ 40 * 7668442 * 2
def baseEnd_7668442 : Nat := 3937596617125391419108483

theorem tailTrace_7668442 : CollatzResearch.WordTrace tailWord_7668442 prefixEnd_7668442 3937596617125391419108483 := by
  unfold tailWord_7668442
  simp only [CollatzResearch.WordTrace]
  refine ⟨69922764321137943617725895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186460704856367849647269053 69922764321137943617725895)
  ·
    refine ⟨104884146481706915426588843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69922764321137943617725895 104884146481706915426588843)
    ·
      refine ⟨157326219722560373139883265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104884146481706915426588843 157326219722560373139883265)
      ·
        refine ⟨117994664791920279854912449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157326219722560373139883265 117994664791920279854912449)
        ·
          refine ⟨88495998593940209891184337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117994664791920279854912449 88495998593940209891184337)
          ·
            refine ⟨66371998945455157418388253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88495998593940209891184337 66371998945455157418388253)
            ·
              refine ⟨24889499604545684031895595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66371998945455157418388253 24889499604545684031895595)
              ·
                refine ⟨37334249406818526047843393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24889499604545684031895595 37334249406818526047843393)
                ·
                  refine ⟨28000687055113894535882545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37334249406818526047843393 28000687055113894535882545)
                  ·
                    refine ⟨21000515291335420901911909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28000687055113894535882545 21000515291335420901911909)
                    ·
                      refine ⟨3937596617125391419108483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21000515291335420901911909 3937596617125391419108483)
                      ·
                        rfl

theorem cell23_7668442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_7668442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668442 prefixEnd_7668442 := by exact prefixLift 7668442
  have htrace : WordTrace (prefixWord ++ tailWord_7668442) baseStart_7668442 baseEnd_7668442 := by
    simpa [prefixWord, tailWord_7668442, baseEnd_7668442] using wordTrace_append hprefix tailTrace_7668442
  have hstable : (prefixWord ++ tailWord_7668442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668442).length < 2 ^ (prefixWord ++ tailWord_7668442).sum := by decide
  have hdescent : baseEnd_7668442 < baseStart_7668442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668452 : List Nat := [2, 3, 1, 1, 1, 5, 1, 2, 7]
def baseStart_7668452 : Nat := 118140960795 + 7668452 * 2 ^ 59
def prefixEnd_7668452 : Nat := 4983230072969 + 3 ^ 40 * 7668452 * 2
def baseEnd_7668452 : Nat := 437511305770215153331493

theorem tailTrace_7668452 : CollatzResearch.WordTrace tailWord_7668452 prefixEnd_7668452 437511305770215153331493 := by
  unfold tailWord_7668452
  simp only [CollatzResearch.WordTrace]
  refine ⟨139845711007257773089383805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186460948009677030785845073 139845711007257773089383805)
  ·
    refine ⟨52442141627721664908518927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139845711007257773089383805 52442141627721664908518927)
    ·
      refine ⟨78663212441582497362778391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52442141627721664908518927 78663212441582497362778391)
      ·
        refine ⟨117994818662373746044167587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78663212441582497362778391 117994818662373746044167587)
        ·
          refine ⟨176992227993560619066251381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117994818662373746044167587 176992227993560619066251381)
          ·
            refine ⟨16593021374396308037461067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176992227993560619066251381 16593021374396308037461067)
            ·
              refine ⟨24889532061594462056191601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16593021374396308037461067 24889532061594462056191601)
              ·
                refine ⟨18667149046195846542143701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24889532061594462056191601 18667149046195846542143701)
                ·
                  refine ⟨437511305770215153331493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18667149046195846542143701 437511305770215153331493)
                  ·
                    rfl

theorem cell23_7668452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_7668452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668452 prefixEnd_7668452 := by exact prefixLift 7668452
  have htrace : WordTrace (prefixWord ++ tailWord_7668452) baseStart_7668452 baseEnd_7668452 := by
    simpa [prefixWord, tailWord_7668452, baseEnd_7668452] using wordTrace_append hprefix tailTrace_7668452
  have hstable : (prefixWord ++ tailWord_7668452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668452).length < 2 ^ (prefixWord ++ tailWord_7668452).sum := by decide
  have hdescent : baseEnd_7668452 < baseStart_7668452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668602 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 5, 6]
def baseStart_7668602 : Nat := 118140960795 + 7668602 * 2 ^ 59
def prefixEnd_7668602 : Nat := 4983230072969 + 3 ^ 40 * 7668602 * 2
def baseEnd_7668602 : Nat := 1312559591343370264369249

theorem tailTrace_7668602 : CollatzResearch.WordTrace tailWord_7668602 prefixEnd_7668602 1312559591343370264369249 := by
  unfold tailWord_7668602
  simp only [CollatzResearch.WordTrace]
  refine ⟨69924223240993030449182015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186464595309314747864485373 69924223240993030449182015)
  ·
    refine ⟨104886334861489545673773023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69924223240993030449182015 104886334861489545673773023)
    ·
      refine ⟨157329502292234318510659535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104886334861489545673773023 157329502292234318510659535)
      ·
        refine ⟨235994253438351477765989303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157329502292234318510659535 235994253438351477765989303)
        ·
          refine ⟨353991380157527216648983955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235994253438351477765989303 353991380157527216648983955)
          ·
            refine ⟨530987070236290824973475933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353991380157527216648983955 530987070236290824973475933)
            ·
              refine ⟨199120151338609059365053475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 530987070236290824973475933 199120151338609059365053475)
              ·
                refine ⟨298680227007913589047580213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199120151338609059365053475 298680227007913589047580213)
                ·
                  refine ⟨28001271281991898973210645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 298680227007913589047580213 28001271281991898973210645)
                  ·
                    refine ⟨1312559591343370264369249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28001271281991898973210645 1312559591343370264369249)
                    ·
                      rfl

theorem cell23_7668602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_7668602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668602 prefixEnd_7668602 := by exact prefixLift 7668602
  have htrace : WordTrace (prefixWord ++ tailWord_7668602) baseStart_7668602 baseEnd_7668602 := by
    simpa [prefixWord, tailWord_7668602, baseEnd_7668602] using wordTrace_append hprefix tailTrace_7668602
  have hstable : (prefixWord ++ tailWord_7668602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668602).length < 2 ^ (prefixWord ++ tailWord_7668602).sum := by decide
  have hdescent : baseEnd_7668602 < baseStart_7668602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668694 : List Nat := [5, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_7668694 : Nat := 118140960795 + 7668694 * 2 ^ 59
def prefixEnd_7668694 : Nat := 4983230072969 + 3 ^ 40 * 7668694 * 2
def baseEnd_7668694 : Nat := 3937726014250324433157325

theorem tailTrace_7668694 : CollatzResearch.WordTrace tailWord_7668694 prefixEnd_7668694 3937726014250324433157325 := by
  unfold tailWord_7668694
  simp only [CollatzResearch.WordTrace]
  refine ⟨17481265529977426344317321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186466832319759214339384757 17481265529977426344317321)
  ·
    refine ⟨13110949147483069758237991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17481265529977426344317321 13110949147483069758237991)
    ·
      refine ⟨19666423721224604637356987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13110949147483069758237991 19666423721224604637356987)
      ·
        refine ⟨29499635581836906956035481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19666423721224604637356987 29499635581836906956035481)
        ·
          refine ⟨22124726686377680217026611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29499635581836906956035481 22124726686377680217026611)
          ·
            refine ⟨33187090029566520325539917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22124726686377680217026611 33187090029566520325539917)
            ·
              refine ⟨12445158761087445122077469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33187090029566520325539917 12445158761087445122077469)
              ·
                refine ⟨4666934535407791920779051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12445158761087445122077469 4666934535407791920779051)
                ·
                  refine ⟨7000401803111687881168577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4666934535407791920779051 7000401803111687881168577)
                  ·
                    refine ⟨5250301352333765910876433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7000401803111687881168577 5250301352333765910876433)
                    ·
                      refine ⟨3937726014250324433157325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5250301352333765910876433 3937726014250324433157325)
                      ·
                        rfl

theorem cell23_7668694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_7668694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668694 prefixEnd_7668694 := by exact prefixLift 7668694
  have htrace : WordTrace (prefixWord ++ tailWord_7668694) baseStart_7668694 baseEnd_7668694 := by
    simpa [prefixWord, tailWord_7668694, baseEnd_7668694] using wordTrace_append hprefix tailTrace_7668694
  have hstable : (prefixWord ++ tailWord_7668694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668694).length < 2 ^ (prefixWord ++ tailWord_7668694).sum := by decide
  have hdescent : baseEnd_7668694 < baseStart_7668694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668729 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 1, 4, 4]
def baseStart_7668729 : Nat := 118140960795 + 7668729 * 2 ^ 59
def prefixEnd_7668729 : Nat := 4983230072969 + 3 ^ 40 * 7668729 * 2
def baseEnd_7668729 : Nat := 3937743986073231796219663

theorem tailTrace_7668729 : CollatzResearch.WordTrace tailWord_7668729 prefixEnd_7668729 3937743986073231796219663 := by
  unfold tailWord_7668729
  simp only [CollatzResearch.WordTrace]
  refine ⟨279701525034512022486601241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186467683356341348324400827 279701525034512022486601241)
  ·
    refine ⟨209776143775884016864950931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279701525034512022486601241 209776143775884016864950931)
    ·
      refine ⟨314664215663826025297426397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209776143775884016864950931 314664215663826025297426397)
      ·
        refine ⟨117999080873934759486534899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314664215663826025297426397 117999080873934759486534899)
        ·
          refine ⟨176998621310902139229802349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117999080873934759486534899 176998621310902139229802349)
          ·
            refine ⟨66374482991588302211175881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176998621310902139229802349 66374482991588302211175881)
            ·
              refine ⟨49780862243691226658381911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66374482991588302211175881 49780862243691226658381911)
              ·
                refine ⟨74671293365536839987572867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49780862243691226658381911 74671293365536839987572867)
                ·
                  refine ⟨112006940048305259981359301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74671293365536839987572867 112006940048305259981359301)
                  ·
                    refine ⟨21001301259057236246504869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112006940048305259981359301 21001301259057236246504869)
                    ·
                      refine ⟨3937743986073231796219663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21001301259057236246504869 3937743986073231796219663)
                      ·
                        rfl

theorem cell23_7668729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_7668729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668729 prefixEnd_7668729 := by exact prefixLift 7668729
  have htrace : WordTrace (prefixWord ++ tailWord_7668729) baseStart_7668729 baseEnd_7668729 := by
    simpa [prefixWord, tailWord_7668729, baseEnd_7668729] using wordTrace_append hprefix tailTrace_7668729
  have hstable : (prefixWord ++ tailWord_7668729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668729).length < 2 ^ (prefixWord ++ tailWord_7668729).sum := by decide
  have hdescent : baseEnd_7668729 < baseStart_7668729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668779 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 5]
def baseStart_7668779 : Nat := 118140960795 + 7668779 * 2 ^ 59
def prefixEnd_7668779 : Nat := 4983230072969 + 3 ^ 40 * 7668779 * 2
def baseEnd_7668779 : Nat := 3937769660105956600594433

theorem tailTrace_7668779 : CollatzResearch.WordTrace tailWord_7668779 prefixEnd_7668779 3937769660105956600594433 := by
  unfold tailWord_7668779
  simp only [CollatzResearch.WordTrace]
  refine ⟨279703348684330881025921391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186468899122887254017280927 279703348684330881025921391)
  ·
    refine ⟨419555023026496321538882087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279703348684330881025921391 419555023026496321538882087)
    ·
      refine ⟨629332534539744482308323131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419555023026496321538882087 629332534539744482308323131)
      ·
        refine ⟨943998801809616723462484697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629332534539744482308323131 943998801809616723462484697)
        ·
          refine ⟨707999101357212542596863523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 943998801809616723462484697 707999101357212542596863523)
          ·
            refine ⟨1061998652035818813895295285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707999101357212542596863523 1061998652035818813895295285)
            ·
              refine ⟨99562373628358013802683933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1061998652035818813895295285 99562373628358013802683933)
              ·
                refine ⟨37335890110634255176006475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99562373628358013802683933 37335890110634255176006475)
                ·
                  refine ⟨56003835165951382764009713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37335890110634255176006475 56003835165951382764009713)
                  ·
                    refine ⟨42002876374463537073007285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56003835165951382764009713 42002876374463537073007285)
                    ·
                      refine ⟨3937769660105956600594433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42002876374463537073007285 3937769660105956600594433)
                      ·
                        rfl

theorem cell23_7668779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 5].length) (baseStart_7668779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668779 prefixEnd_7668779 := by exact prefixLift 7668779
  have htrace : WordTrace (prefixWord ++ tailWord_7668779) baseStart_7668779 baseEnd_7668779 := by
    simpa [prefixWord, tailWord_7668779, baseEnd_7668779] using wordTrace_append hprefix tailTrace_7668779
  have hstable : (prefixWord ++ tailWord_7668779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668779).length < 2 ^ (prefixWord ++ tailWord_7668779).sum := by decide
  have hdescent : baseEnd_7668779 < baseStart_7668779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668809 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 2, 3, 5]
def baseStart_7668809 : Nat := 118140960795 + 7668809 * 2 ^ 59
def prefixEnd_7668809 : Nat := 4983230072969 + 3 ^ 40 * 7668809 * 2
def baseEnd_7668809 : Nat := 3937785064525591483219295

theorem tailTrace_7668809 : CollatzResearch.WordTrace tailWord_7668809 prefixEnd_7668809 3937785064525591483219295 := by
  unfold tailWord_7668809
  simp only [CollatzResearch.WordTrace]
  refine ⟨279704442874222196149513481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186469628582814797433008987 279704442874222196149513481)
  ·
    refine ⟨209778332155666647112135111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279704442874222196149513481 209778332155666647112135111)
    ·
      refine ⟨314667498233499970668202667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209778332155666647112135111 314667498233499970668202667)
      ·
        refine ⟨472001247350249956002304001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314667498233499970668202667 472001247350249956002304001)
        ·
          refine ⟨354000935512687467001728001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472001247350249956002304001 354000935512687467001728001)
          ·
            refine ⟨265500701634515600251296001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354000935512687467001728001 265500701634515600251296001)
            ·
              refine ⟨199125526225886700188472001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265500701634515600251296001 199125526225886700188472001)
              ·
                refine ⟨149344144669415025141354001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199125526225886700188472001 149344144669415025141354001)
                ·
                  refine ⟨112008108502061268856015501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149344144669415025141354001 112008108502061268856015501)
                  ·
                    refine ⟨42003040688272975821005813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112008108502061268856015501 42003040688272975821005813)
                    ·
                      refine ⟨3937785064525591483219295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42003040688272975821005813 3937785064525591483219295)
                      ·
                        rfl

theorem cell23_7668809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_7668809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668809 prefixEnd_7668809 := by exact prefixLift 7668809
  have htrace : WordTrace (prefixWord ++ tailWord_7668809) baseStart_7668809 baseEnd_7668809 := by
    simpa [prefixWord, tailWord_7668809, baseEnd_7668809] using wordTrace_append hprefix tailTrace_7668809
  have hstable : (prefixWord ++ tailWord_7668809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668809).length < 2 ^ (prefixWord ++ tailWord_7668809).sum := by decide
  have hdescent : baseEnd_7668809 < baseStart_7668809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668819 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 6]
def baseStart_7668819 : Nat := 118140960795 + 7668819 * 2 ^ 59
def prefixEnd_7668819 : Nat := 4983230072969 + 3 ^ 40 * 7668819 * 2
def baseEnd_7668819 : Nat := 3937790199332136444094249

theorem tailTrace_7668819 : CollatzResearch.WordTrace tailWord_7668819 prefixEnd_7668819 3937790199332136444094249 := by
  unfold tailWord_7668819
  simp only [CollatzResearch.WordTrace]
  refine ⟨279704807604185967857377511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186469871736123978571585007 279704807604185967857377511)
  ·
    refine ⟨419557211406278951786066267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279704807604185967857377511 419557211406278951786066267)
    ·
      refine ⟨629335817109418427679099401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419557211406278951786066267 629335817109418427679099401)
      ·
        refine ⟨472001862832063820759324551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629335817109418427679099401 472001862832063820759324551)
        ·
          refine ⟨708002794248095731138986827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472001862832063820759324551 708002794248095731138986827)
          ·
            refine ⟨1062004191372143596708480241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708002794248095731138986827 1062004191372143596708480241)
            ·
              refine ⟨796503143529107697531360181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062004191372143596708480241 796503143529107697531360181)
              ·
                refine ⟨74672169705853846643565017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 796503143529107697531360181 74672169705853846643565017)
                ·
                  refine ⟨56004127279390384982673763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74672169705853846643565017 56004127279390384982673763)
                  ·
                    refine ⟨84006190919085577474010645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56004127279390384982673763 84006190919085577474010645)
                    ·
                      refine ⟨3937790199332136444094249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84006190919085577474010645 3937790199332136444094249)
                      ·
                        rfl

theorem cell23_7668819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_7668819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668819 prefixEnd_7668819 := by exact prefixLift 7668819
  have htrace : WordTrace (prefixWord ++ tailWord_7668819) baseStart_7668819 baseEnd_7668819 := by
    simpa [prefixWord, tailWord_7668819, baseEnd_7668819] using wordTrace_append hprefix tailTrace_7668819
  have hstable : (prefixWord ++ tailWord_7668819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668819).length < 2 ^ (prefixWord ++ tailWord_7668819).sum := by decide
  have hdescent : baseEnd_7668819 < baseStart_7668819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668859 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 2, 9]
def baseStart_7668859 : Nat := 118140960795 + 7668859 * 2 ^ 59
def prefixEnd_7668859 : Nat := 4983230072969 + 3 ^ 40 * 7668859 * 2
def baseEnd_7668859 : Nat := 1312603579519438762531355

theorem tailTrace_7668859 : CollatzResearch.WordTrace tailWord_7668859 prefixEnd_7668859 1312603579519438762531355 := by
  unfold tailWord_7668859
  simp only [CollatzResearch.WordTrace]
  refine ⟨279706266524041054688833631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186470844349360703125889087 279706266524041054688833631)
  ·
    refine ⟨419559399786061582033250447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279706266524041054688833631 419559399786061582033250447)
    ·
      refine ⟨629339099679092373049875671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419559399786061582033250447 629339099679092373049875671)
      ·
        refine ⟨944008649518638559574813507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629339099679092373049875671 944008649518638559574813507)
        ·
          refine ⟨1416012974277957839362220261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944008649518638559574813507 1416012974277957839362220261)
          ·
            refine ⟨265502432677117094880416299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1416012974277957839362220261 265502432677117094880416299)
            ·
              refine ⟨398253649015675642320624449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265502432677117094880416299 398253649015675642320624449)
              ·
                refine ⟨298690236761756731740468337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398253649015675642320624449 298690236761756731740468337)
                ·
                  refine ⟨224017677571317548805351253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298690236761756731740468337 224017677571317548805351253)
                  ·
                    refine ⟨1312603579519438762531355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 224017677571317548805351253 1312603579519438762531355)
                    ·
                      rfl

theorem cell23_7668859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 9].length) (baseStart_7668859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668859 prefixEnd_7668859 := by exact prefixLift 7668859
  have htrace : WordTrace (prefixWord ++ tailWord_7668859) baseStart_7668859 baseEnd_7668859 := by
    simpa [prefixWord, tailWord_7668859, baseEnd_7668859] using wordTrace_append hprefix tailTrace_7668859
  have hstable : (prefixWord ++ tailWord_7668859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668859).length < 2 ^ (prefixWord ++ tailWord_7668859).sum := by decide
  have hdescent : baseEnd_7668859 < baseStart_7668859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668883 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 4, 3, 2]
def baseStart_7668883 : Nat := 118140960795 + 7668883 * 2 ^ 59
def prefixEnd_7668883 : Nat := 4983230072969 + 3 ^ 40 * 7668883 * 2
def baseEnd_7668883 : Nat := 3937823062094024193693955

theorem tailTrace_7668883 : CollatzResearch.WordTrace tailWord_7668883 prefixEnd_7668883 3937823062094024193693955 := by
  unfold tailWord_7668883
  simp only [CollatzResearch.WordTrace]
  refine ⟨279707141875954106787707303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186471427917302737858471535 279707141875954106787707303)
  ·
    refine ⟨419560712813931160181560955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279707141875954106787707303 419560712813931160181560955)
    ·
      refine ⟨629341069220896740272341433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419560712813931160181560955 629341069220896740272341433)
      ·
        refine ⟨472005801915672555204256075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629341069220896740272341433 472005801915672555204256075)
        ·
          refine ⟨708008702873508832806384113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472005801915672555204256075 708008702873508832806384113)
          ·
            refine ⟨531006527155131624604788085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 708008702873508832806384113 531006527155131624604788085)
            ·
              refine ⟨49781861920793589806698883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 531006527155131624604788085 49781861920793589806698883)
              ·
                refine ⟨74672792881190384710048325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49781861920793589806698883 74672792881190384710048325)
                ·
                  refine ⟨14001148665223197133134061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74672792881190384710048325 14001148665223197133134061)
                  ·
                    refine ⟨5250430749458698924925273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14001148665223197133134061 5250430749458698924925273)
                    ·
                      refine ⟨3937823062094024193693955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5250430749458698924925273 3937823062094024193693955)
                      ·
                        rfl

theorem cell23_7668883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 3, 2].length) (baseStart_7668883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668883 prefixEnd_7668883 := by exact prefixLift 7668883
  have htrace : WordTrace (prefixWord ++ tailWord_7668883) baseStart_7668883 baseEnd_7668883 := by
    simpa [prefixWord, tailWord_7668883, baseEnd_7668883] using wordTrace_append hprefix tailTrace_7668883
  have hstable : (prefixWord ++ tailWord_7668883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668883).length < 2 ^ (prefixWord ++ tailWord_7668883).sum := by decide
  have hdescent : baseEnd_7668883 < baseStart_7668883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7668947 : List Nat := [1, 1, 1, 2, 1, 1, 1, 10, 1, 2, 2]
def baseStart_7668947 : Nat := 118140960795 + 7668947 * 2 ^ 59
def prefixEnd_7668947 : Nat := 4983230072969 + 3 ^ 40 * 7668947 * 2
def baseEnd_7668947 : Nat := 3937855924855911943293661

theorem tailTrace_7668947 : CollatzResearch.WordTrace tailWord_7668947 prefixEnd_7668947 3937855924855911943293661 := by
  unfold tailWord_7668947
  simp only [CollatzResearch.WordTrace]
  refine ⟨279709476147722245718037095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186472984098481497145358063 279709476147722245718037095)
  ·
    refine ⟨419564214221583368577055643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279709476147722245718037095 419564214221583368577055643)
    ·
      refine ⟨629346321332375052865583465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419564214221583368577055643 629346321332375052865583465)
      ·
        refine ⟨472009740999281289649187599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629346321332375052865583465 472009740999281289649187599)
        ·
          refine ⟨708014611498921934473781399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472009740999281289649187599 708014611498921934473781399)
          ·
            refine ⟨1062021917248382901710672099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708014611498921934473781399 1062021917248382901710672099)
            ·
              refine ⟨1593032875872574352566008149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062021917248382901710672099 1593032875872574352566008149)
              ·
                refine ⟨4667088503532932673533227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1593032875872574352566008149 4667088503532932673533227)
                ·
                  refine ⟨7000632755299399010299841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4667088503532932673533227 7000632755299399010299841)
                  ·
                    refine ⟨5250474566474549257724881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7000632755299399010299841 5250474566474549257724881)
                    ·
                      refine ⟨3937855924855911943293661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5250474566474549257724881 3937855924855911943293661)
                      ·
                        rfl

theorem cell23_7668947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 1, 2, 2].length) (baseStart_7668947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7668947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7668947 prefixEnd_7668947 := by exact prefixLift 7668947
  have htrace : WordTrace (prefixWord ++ tailWord_7668947) baseStart_7668947 baseEnd_7668947 := by
    simpa [prefixWord, tailWord_7668947, baseEnd_7668947] using wordTrace_append hprefix tailTrace_7668947
  have hstable : (prefixWord ++ tailWord_7668947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7668947).length < 2 ^ (prefixWord ++ tailWord_7668947).sum := by decide
  have hdescent : baseEnd_7668947 < baseStart_7668947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7668947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669024 : List Nat := [2, 1, 1, 5, 3, 1, 2, 2, 1, 3, 2]
def baseStart_7669024 : Nat := 118140960795 + 7669024 * 2 ^ 59
def prefixEnd_7669024 : Nat := 4983230072969 + 3 ^ 40 * 7669024 * 2
def baseEnd_7669024 : Nat := 3937895462866308142030807

theorem tailTrace_7669024 : CollatzResearch.WordTrace tailWord_7669024 prefixEnd_7669024 3937895462866308142030807 := by
  unfold tailWord_7669024
  simp only [CollatzResearch.WordTrace]
  refine ⟨139856142284221643934295063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186474856378962191912393417 139856142284221643934295063)
  ·
    refine ⟨209784213426332465901442595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139856142284221643934295063 209784213426332465901442595)
    ·
      refine ⟨314676320139498698852163893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209784213426332465901442595 314676320139498698852163893)
      ·
        refine ⟨29500905013078003017390365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 314676320139498698852163893 29500905013078003017390365)
        ·
          refine ⟨11062839379904251131521387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29500905013078003017390365 11062839379904251131521387)
          ·
            refine ⟨16594259069856376697282081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11062839379904251131521387 16594259069856376697282081)
            ·
              refine ⟨12445694302392282522961561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16594259069856376697282081 12445694302392282522961561)
              ·
                refine ⟨9334270726794211892221171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12445694302392282522961561 9334270726794211892221171)
                ·
                  refine ⟨14001406090191317838331757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9334270726794211892221171 14001406090191317838331757)
                  ·
                    refine ⟨5250527283821744189374409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14001406090191317838331757 5250527283821744189374409)
                    ·
                      refine ⟨3937895462866308142030807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5250527283821744189374409 3937895462866308142030807)
                      ·
                        rfl

theorem cell23_7669024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_7669024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669024 prefixEnd_7669024 := by exact prefixLift 7669024
  have htrace : WordTrace (prefixWord ++ tailWord_7669024) baseStart_7669024 baseEnd_7669024 := by
    simpa [prefixWord, tailWord_7669024, baseEnd_7669024] using wordTrace_append hprefix tailTrace_7669024
  have hstable : (prefixWord ++ tailWord_7669024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669024).length < 2 ^ (prefixWord ++ tailWord_7669024).sum := by decide
  have hdescent : baseEnd_7669024 < baseStart_7669024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669054 : List Nat := [4, 2, 1, 2, 1, 1, 2, 4, 2, 2, 2]
def baseStart_7669054 : Nat := 118140960795 + 7669054 * 2 ^ 59
def prefixEnd_7669054 : Nat := 4983230072969 + 3 ^ 40 * 7669054 * 2
def baseEnd_7669054 : Nat := 3937910867285943024655669

theorem tailTrace_7669054 : CollatzResearch.WordTrace tailWord_7669054 prefixEnd_7669054 3937910867285943024655669 := by
  unfold tailWord_7669054
  simp only [CollatzResearch.WordTrace]
  refine ⟨34964172344791825374022777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186475585838889735328121477 34964172344791825374022777)
  ·
    refine ⟨26223129258593869030517083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34964172344791825374022777 26223129258593869030517083)
    ·
      refine ⟨39334693887890803545775625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26223129258593869030517083 39334693887890803545775625)
      ·
        refine ⟨29501020415918102659331719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39334693887890803545775625 29501020415918102659331719)
        ·
          refine ⟨44251530623877153988997579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29501020415918102659331719 44251530623877153988997579)
          ·
            refine ⟨66377295935815730983496369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44251530623877153988997579 66377295935815730983496369)
            ·
              refine ⟨49782971951861798237622277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66377295935815730983496369 49782971951861798237622277)
              ·
                refine ⟨9334307240974087169554177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49782971951861798237622277 9334307240974087169554177)
                ·
                  refine ⟨7000730430730565377165633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9334307240974087169554177 7000730430730565377165633)
                  ·
                    refine ⟨5250547823047924032874225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7000730430730565377165633 5250547823047924032874225)
                    ·
                      refine ⟨3937910867285943024655669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5250547823047924032874225 3937910867285943024655669)
                      ·
                        rfl

theorem cell23_7669054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_7669054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669054 prefixEnd_7669054 := by exact prefixLift 7669054
  have htrace : WordTrace (prefixWord ++ tailWord_7669054) baseStart_7669054 baseEnd_7669054 := by
    simpa [prefixWord, tailWord_7669054, baseEnd_7669054] using wordTrace_append hprefix tailTrace_7669054
  have hstable : (prefixWord ++ tailWord_7669054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669054).length < 2 ^ (prefixWord ++ tailWord_7669054).sum := by decide
  have hdescent : baseEnd_7669054 < baseStart_7669054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669073 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 4, 5]
def baseStart_7669073 : Nat := 118140960795 + 7669073 * 2 ^ 59
def prefixEnd_7669073 : Nat := 4983230072969 + 3 ^ 40 * 7669073 * 2
def baseEnd_7669073 : Nat := 1312640207806126150106027

theorem tailTrace_7669073 : CollatzResearch.WordTrace tailWord_7669073 prefixEnd_7669073 1312640207806126150106027 := by
  unfold tailWord_7669073
  simp only [CollatzResearch.WordTrace]
  refine ⟨279714071745265769237123873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186476047830177179491415915 279714071745265769237123873)
  ·
    refine ⟨209785553808949326927842905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279714071745265769237123873 209785553808949326927842905)
    ·
      refine ⟨157339165356711995195882179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209785553808949326927842905 157339165356711995195882179)
      ·
        refine ⟨236008748035067992793823269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157339165356711995195882179 236008748035067992793823269)
        ·
          refine ⟨44251640256575248648841863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236008748035067992793823269 44251640256575248648841863)
          ·
            refine ⟨66377460384862872973262795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44251640256575248648841863 66377460384862872973262795)
            ·
              refine ⟨99566190577294309459894193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66377460384862872973262795 99566190577294309459894193)
              ·
                refine ⟨74674642932970732094920645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99566190577294309459894193 74674642932970732094920645)
                ·
                  refine ⟨14001495549932012267797621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74674642932970732094920645 14001495549932012267797621)
                  ·
                    refine ⟨1312640207806126150106027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14001495549932012267797621 1312640207806126150106027)
                    ·
                      rfl

theorem cell23_7669073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_7669073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669073 prefixEnd_7669073 := by exact prefixLift 7669073
  have htrace : WordTrace (prefixWord ++ tailWord_7669073) baseStart_7669073 baseEnd_7669073 := by
    simpa [prefixWord, tailWord_7669073, baseEnd_7669073] using wordTrace_append hprefix tailTrace_7669073
  have hstable : (prefixWord ++ tailWord_7669073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669073).length < 2 ^ (prefixWord ++ tailWord_7669073).sum := by decide
  have hdescent : baseEnd_7669073 < baseStart_7669073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669127 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 2, 4, 2]
def baseStart_7669127 : Nat := 118140960795 + 7669127 * 2 ^ 59
def prefixEnd_7669127 : Nat := 4983230072969 + 3 ^ 40 * 7669127 * 2
def baseEnd_7669127 : Nat := 3937948351373721239042833

theorem tailTrace_7669127 : CollatzResearch.WordTrace tailWord_7669127 prefixEnd_7669127 3937948351373721239042833 := by
  unfold tailWord_7669127
  simp only [CollatzResearch.WordTrace]
  refine ⟨279716041287070136459589635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186477360858046757639726423 279716041287070136459589635)
  ·
    refine ⟨419574061930605204689384453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279716041287070136459589635 419574061930605204689384453)
    ·
      refine ⟨78670136611988475879259585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 419574061930605204689384453 78670136611988475879259585)
      ·
        refine ⟨59002602458991356909444689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78670136611988475879259585 59002602458991356909444689)
        ·
          refine ⟨44251951844243517682083517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59002602458991356909444689 44251951844243517682083517)
          ·
            refine ⟨16594481941591319130781319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44251951844243517682083517 16594481941591319130781319)
            ·
              refine ⟨24891722912386978696171979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16594481941591319130781319 24891722912386978696171979)
              ·
                refine ⟨37337584368580468044257969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24891722912386978696171979 37337584368580468044257969)
                ·
                  refine ⟨28003188276435351033193477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37337584368580468044257969 28003188276435351033193477)
                  ·
                    refine ⟨5250597801831628318723777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28003188276435351033193477 5250597801831628318723777)
                    ·
                      refine ⟨3937948351373721239042833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5250597801831628318723777 3937948351373721239042833)
                      ·
                        rfl

theorem cell23_7669127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_7669127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669127 prefixEnd_7669127 := by exact prefixLift 7669127
  have htrace : WordTrace (prefixWord ++ tailWord_7669127) baseStart_7669127 baseEnd_7669127 := by
    simpa [prefixWord, tailWord_7669127, baseEnd_7669127] using wordTrace_append hprefix tailTrace_7669127
  have hstable : (prefixWord ++ tailWord_7669127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669127).length < 2 ^ (prefixWord ++ tailWord_7669127).sum := by decide
  have hdescent : baseEnd_7669127 < baseStart_7669127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669144 : List Nat := [2, 1, 2, 5, 2, 2, 1, 1, 2, 1, 4]
def baseStart_7669144 : Nat := 118140960795 + 7669144 * 2 ^ 59
def prefixEnd_7669144 : Nat := 4983230072969 + 3 ^ 40 * 7669144 * 2
def baseEnd_7669144 : Nat := 3937957080544847672530255

theorem tailTrace_7669144 : CollatzResearch.WordTrace tailWord_7669144 prefixEnd_7669144 3937957080544847672530255 := by
  unfold tailWord_7669144
  simp only [CollatzResearch.WordTrace]
  refine ⟨139858330664004274181479243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186477774218672365575305657 139858330664004274181479243)
  ·
    refine ⟨209787495996006411272218865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139858330664004274181479243 209787495996006411272218865)
    ·
      refine ⟨157340621997004808454164149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209787495996006411272218865 157340621997004808454164149)
      ·
        refine ⟨14750683312219200792577889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157340621997004808454164149 14750683312219200792577889)
        ·
          refine ⟨11063012484164400594433417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14750683312219200792577889 11063012484164400594433417)
          ·
            refine ⟨8297259363123300445825063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11063012484164400594433417 8297259363123300445825063)
            ·
              refine ⟨12445889044684950668737595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8297259363123300445825063 12445889044684950668737595)
              ·
                refine ⟨18668833567027426003106393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12445889044684950668737595 18668833567027426003106393)
                ·
                  refine ⟨14001625175270569502329795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18668833567027426003106393 14001625175270569502329795)
                  ·
                    refine ⟨21002437762905854253494693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14001625175270569502329795 21002437762905854253494693)
                    ·
                      refine ⟨3937957080544847672530255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21002437762905854253494693 3937957080544847672530255)
                      ·
                        rfl

theorem cell23_7669144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_7669144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669144 prefixEnd_7669144 := by exact prefixLift 7669144
  have htrace : WordTrace (prefixWord ++ tailWord_7669144) baseStart_7669144 baseEnd_7669144 := by
    simpa [prefixWord, tailWord_7669144, baseEnd_7669144] using wordTrace_append hprefix tailTrace_7669144
  have hstable : (prefixWord ++ tailWord_7669144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669144).length < 2 ^ (prefixWord ++ tailWord_7669144).sum := by decide
  have hdescent : baseEnd_7669144 < baseStart_7669144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669154 : List Nat := [3, 3, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_7669154 : Nat := 118140960795 + 7669154 * 2 ^ 59
def prefixEnd_7669154 : Nat := 4983230072969 + 3 ^ 40 * 7669154 * 2
def baseEnd_7669154 : Nat := 1312654071783797544468403

theorem tailTrace_7669154 : CollatzResearch.WordTrace tailWord_7669154 prefixEnd_7669154 1312654071783797544468403 := by
  unfold tailWord_7669154
  simp only [CollatzResearch.WordTrace]
  refine ⟨69929256514493080017705629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186478017371981546713881677 69929256514493080017705629)
  ·
    refine ⟨26223471192934905006639611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69929256514493080017705629 26223471192934905006639611)
    ·
      refine ⟨39335206789402357509959417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26223471192934905006639611 39335206789402357509959417)
      ·
        refine ⟨29501405092051768132469563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39335206789402357509959417 29501405092051768132469563)
        ·
          refine ⟨44252107638077652198704345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29501405092051768132469563 44252107638077652198704345)
          ·
            refine ⟨33189080728558239149028259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44252107638077652198704345 33189080728558239149028259)
            ·
              refine ⟨49783621092837358723542389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33189080728558239149028259 49783621092837358723542389)
              ·
                refine ⟨4667214477453502380332099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49783621092837358723542389 4667214477453502380332099)
                ·
                  refine ⟨7000821716180253570498149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4667214477453502380332099 7000821716180253570498149)
                  ·
                    refine ⟨1312654071783797544468403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7000821716180253570498149 1312654071783797544468403)
                    ·
                      rfl

theorem cell23_7669154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_7669154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669154 prefixEnd_7669154 := by exact prefixLift 7669154
  have htrace : WordTrace (prefixWord ++ tailWord_7669154) baseStart_7669154 baseEnd_7669154 := by
    simpa [prefixWord, tailWord_7669154, baseEnd_7669154] using wordTrace_append hprefix tailTrace_7669154
  have hstable : (prefixWord ++ tailWord_7669154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669154).length < 2 ^ (prefixWord ++ tailWord_7669154).sum := by decide
  have hdescent : baseEnd_7669154 < baseStart_7669154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669217 : List Nat := [1, 2, 3, 1, 2, 3, 2, 3, 1, 1, 4]
def baseStart_7669217 : Nat := 118140960795 + 7669217 * 2 ^ 59
def prefixEnd_7669217 : Nat := 4983230072969 + 3 ^ 40 * 7669217 * 2
def baseEnd_7669217 : Nat := 3937994564632625886917419

theorem tailTrace_7669217 : CollatzResearch.WordTrace tailWord_7669217 prefixEnd_7669217 3937994564632625886917419 := by
  unfold tailWord_7669217
  simp only [CollatzResearch.WordTrace]
  refine ⟨279719323856744081830365905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186479549237829387886910603 279719323856744081830365905)
  ·
    refine ⟨209789492892558061372774429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279719323856744081830365905 209789492892558061372774429)
    ·
      refine ⟨78671059834709273014790411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209789492892558061372774429 78671059834709273014790411)
      ·
        refine ⟨118006589752063909522185617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78671059834709273014790411 118006589752063909522185617)
        ·
          refine ⟨88504942314047932141639213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118006589752063909522185617 88504942314047932141639213)
          ·
            refine ⟨33189353367767974553114705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88504942314047932141639213 33189353367767974553114705)
            ·
              refine ⟨24892015025825980914836029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33189353367767974553114705 24892015025825980914836029)
              ·
                refine ⟨9334505634684742843063511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24892015025825980914836029 9334505634684742843063511)
                ·
                  refine ⟨14001758452027114264595267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9334505634684742843063511 14001758452027114264595267)
                  ·
                    refine ⟨21002637678040671396892901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14001758452027114264595267 21002637678040671396892901)
                    ·
                      refine ⟨3937994564632625886917419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21002637678040671396892901 3937994564632625886917419)
                      ·
                        rfl

theorem cell23_7669217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_7669217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669217 prefixEnd_7669217 := by exact prefixLift 7669217
  have htrace : WordTrace (prefixWord ++ tailWord_7669217) baseStart_7669217 baseEnd_7669217 := by
    simpa [prefixWord, tailWord_7669217, baseEnd_7669217] using wordTrace_append hprefix tailTrace_7669217
  have hstable : (prefixWord ++ tailWord_7669217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669217).length < 2 ^ (prefixWord ++ tailWord_7669217).sum := by decide
  have hdescent : baseEnd_7669217 < baseStart_7669217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669230 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_7669230 : Nat := 118140960795 + 7669230 * 2 ^ 59
def prefixEnd_7669230 : Nat := 4983230072969 + 3 ^ 40 * 7669230 * 2
def baseEnd_7669230 : Nat := 3938001239881134336054859

theorem tailTrace_7669230 : CollatzResearch.WordTrace tailWord_7669230 prefixEnd_7669230 3938001239881134336054859 := by
  unfold tailWord_7669230
  simp only [CollatzResearch.WordTrace]
  refine ⟨34964974750712123131323643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186479865337131323367059429 34964974750712123131323643)
  ·
    refine ⟨52447462126068184696985465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34964974750712123131323643 52447462126068184696985465)
    ·
      refine ⟨39335596594551138522739099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52447462126068184696985465 39335596594551138522739099)
      ·
        refine ⟨59003394891826707784108649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39335596594551138522739099 59003394891826707784108649)
        ·
          refine ⟨44252546168870030838081487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59003394891826707784108649 44252546168870030838081487)
          ·
            refine ⟨66378819253305046257122231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44252546168870030838081487 66378819253305046257122231)
            ·
              refine ⟨99568228879957569385683347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66378819253305046257122231 99568228879957569385683347)
              ·
                refine ⟨149352343319936354078525021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99568228879957569385683347 149352343319936354078525021)
                ·
                  refine ⟨56007128744976132779446883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149352343319936354078525021 56007128744976132779446883)
                  ·
                    refine ⟨84010693117464199169170325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56007128744976132779446883 84010693117464199169170325)
                    ·
                      refine ⟨3938001239881134336054859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84010693117464199169170325 3938001239881134336054859)
                      ·
                        rfl

theorem cell23_7669230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_7669230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669230 prefixEnd_7669230 := by exact prefixLift 7669230
  have htrace : WordTrace (prefixWord ++ tailWord_7669230) baseStart_7669230 baseEnd_7669230 := by
    simpa [prefixWord, tailWord_7669230, baseEnd_7669230] using wordTrace_append hprefix tailTrace_7669230
  have hstable : (prefixWord ++ tailWord_7669230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669230).length < 2 ^ (prefixWord ++ tailWord_7669230).sum := by decide
  have hdescent : baseEnd_7669230 < baseStart_7669230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669240 : List Nat := [2, 1, 2, 1, 1, 6, 2, 8]
def baseStart_7669240 : Nat := 118140960795 + 7669240 * 2 ^ 59
def prefixEnd_7669240 : Nat := 4983230072969 + 3 ^ 40 * 7669240 * 2
def baseEnd_7669240 : Nat := 145852087951395529515919

theorem tailTrace_7669240 : CollatzResearch.WordTrace tailWord_7669240 prefixEnd_7669240 145852087951395529515919 := by
  unfold tailWord_7669240
  simp only [CollatzResearch.WordTrace]
  refine ⟨139860081367830378379226587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186480108490440504505635449 139860081367830378379226587)
  ·
    refine ⟨209790122051745567568839881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139860081367830378379226587 209790122051745567568839881)
    ·
      refine ⟨157342591538809175676629911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209790122051745567568839881 157342591538809175676629911)
      ·
        refine ⟨236013887308213763514944867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157342591538809175676629911 236013887308213763514944867)
        ·
          refine ⟨354020830962320645272417301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236013887308213763514944867 354020830962320645272417301)
          ·
            refine ⟨16594726451358780247144561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 354020830962320645272417301 16594726451358780247144561)
            ·
              refine ⟨12446044838519085185358421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16594726451358780247144561 12446044838519085185358421)
              ·
                refine ⟨145852087951395529515919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12446044838519085185358421 145852087951395529515919)
                ·
                  rfl

theorem cell23_7669240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 8].length) (baseStart_7669240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669240 prefixEnd_7669240 := by exact prefixLift 7669240
  have htrace : WordTrace (prefixWord ++ tailWord_7669240) baseStart_7669240 baseEnd_7669240 := by
    simpa [prefixWord, tailWord_7669240, baseEnd_7669240] using wordTrace_append hprefix tailTrace_7669240
  have hstable : (prefixWord ++ tailWord_7669240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669240).length < 2 ^ (prefixWord ++ tailWord_7669240).sum := by decide
  have hdescent : baseEnd_7669240 < baseStart_7669240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669244 : List Nat := [2, 2, 2, 1, 2, 1, 6, 1, 2, 4]
def baseStart_7669244 : Nat := 118140960795 + 7669244 * 2 ^ 59
def prefixEnd_7669244 : Nat := 4983230072969 + 3 ^ 40 * 7669244 * 2
def baseEnd_7669244 : Nat := 1312669476203432427093265

theorem tailTrace_7669244 : CollatzResearch.WordTrace tailWord_7669244 prefixEnd_7669244 1312669476203432427093265 := by
  unfold tailWord_7669244
  simp only [CollatzResearch.WordTrace]
  refine ⟨139860154313823132720799393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186480205751764176961065857 139860154313823132720799393)
  ·
    refine ⟨104895115735367349540599545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139860154313823132720799393 104895115735367349540599545)
    ·
      refine ⟨78671336801525512155449659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104895115735367349540599545 78671336801525512155449659)
      ·
        refine ⟨118007005202288268233174489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78671336801525512155449659 118007005202288268233174489)
        ·
          refine ⟨88505253901716201174880867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118007005202288268233174489 88505253901716201174880867)
          ·
            refine ⟨132757880852574301762321301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88505253901716201174880867 132757880852574301762321301)
            ·
              refine ⟨6223025664964420395108811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132757880852574301762321301 6223025664964420395108811)
              ·
                refine ⟨9334538497446630592663217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6223025664964420395108811 9334538497446630592663217)
                ·
                  refine ⟨7000903873084972944497413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9334538497446630592663217 7000903873084972944497413)
                  ·
                    refine ⟨1312669476203432427093265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7000903873084972944497413 1312669476203432427093265)
                    ·
                      rfl

theorem cell23_7669244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_7669244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669244 prefixEnd_7669244 := by exact prefixLift 7669244
  have htrace : WordTrace (prefixWord ++ tailWord_7669244) baseStart_7669244 baseEnd_7669244 := by
    simpa [prefixWord, tailWord_7669244, baseEnd_7669244] using wordTrace_append hprefix tailTrace_7669244
  have hstable : (prefixWord ++ tailWord_7669244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669244).length < 2 ^ (prefixWord ++ tailWord_7669244).sum := by decide
  have hdescent : baseEnd_7669244 < baseStart_7669244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669261 : List Nat := [1, 7, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_7669261 : Nat := 118140960795 + 7669261 * 2 ^ 59
def prefixEnd_7669261 : Nat := 4983230072969 + 3 ^ 40 * 7669261 * 2
def baseEnd_7669261 : Nat := 1312672385927141238255739

theorem tailTrace_7669261 : CollatzResearch.WordTrace tailWord_7669261 prefixEnd_7669261 1312672385927141238255739 := by
  unfold tailWord_7669261
  simp only [CollatzResearch.WordTrace]
  refine ⟨279720928668584677344967637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186480619112389784896645091 279720928668584677344967637)
  ·
    refine ⟨6555959265669953375272679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 279720928668584677344967637 6555959265669953375272679)
    ·
      refine ⟨9833938898504930062909019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6555959265669953375272679 9833938898504930062909019)
      ·
        refine ⟨14750908347757395094363529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9833938898504930062909019 14750908347757395094363529)
        ·
          refine ⟨11063181260818046320772647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14750908347757395094363529 11063181260818046320772647)
          ·
            refine ⟨16594771891227069481158971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11063181260818046320772647 16594771891227069481158971)
            ·
              refine ⟨24892157836840604221738457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16594771891227069481158971 24892157836840604221738457)
              ·
                refine ⟨18669118377630453166303843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24892157836840604221738457 18669118377630453166303843)
                ·
                  refine ⟨28003677566445679749455765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18669118377630453166303843 28003677566445679749455765)
                  ·
                    refine ⟨1312672385927141238255739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28003677566445679749455765 1312672385927141238255739)
                    ·
                      rfl

theorem cell23_7669261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_7669261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669261 prefixEnd_7669261 := by exact prefixLift 7669261
  have htrace : WordTrace (prefixWord ++ tailWord_7669261) baseStart_7669261 baseEnd_7669261 := by
    simpa [prefixWord, tailWord_7669261, baseEnd_7669261] using wordTrace_append hprefix tailTrace_7669261
  have hstable : (prefixWord ++ tailWord_7669261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669261).length < 2 ^ (prefixWord ++ tailWord_7669261).sum := by decide
  have hdescent : baseEnd_7669261 < baseStart_7669261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669267 : List Nat := [1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 3]
def baseStart_7669267 : Nat := 118140960795 + 7669267 * 2 ^ 59
def prefixEnd_7669267 : Nat := 4983230072969 + 3 ^ 40 * 7669267 * 2
def baseEnd_7669267 : Nat := 3938020238665350691292189

theorem tailTrace_7669267 : CollatzResearch.WordTrace tailWord_7669267 prefixEnd_7669267 3938020238665350691292189 := by
  unfold tailWord_7669267
  simp only [CollatzResearch.WordTrace]
  refine ⟨279721147506562940369686055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186480765004375293579790703 279721147506562940369686055)
  ·
    refine ⟨419581721259844410554529083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279721147506562940369686055 419581721259844410554529083)
    ·
      refine ⟨629372581889766615831793625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419581721259844410554529083 629372581889766615831793625)
      ·
        refine ⟨472029436417324961873845219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629372581889766615831793625 472029436417324961873845219)
        ·
          refine ⟨708044154625987442810767829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472029436417324961873845219 708044154625987442810767829)
          ·
            refine ⟨16594784874046580690877371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 708044154625987442810767829 16594784874046580690877371)
            ·
              refine ⟨24892177311069871036316057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16594784874046580690877371 24892177311069871036316057)
              ·
                refine ⟨18669132983302403277237043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24892177311069871036316057 18669132983302403277237043)
                ·
                  refine ⟨28003699474953604915855565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18669132983302403277237043 28003699474953604915855565)
                  ·
                    refine ⟨10501387303107601843445837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28003699474953604915855565 10501387303107601843445837)
                    ·
                      refine ⟨3938020238665350691292189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10501387303107601843445837 3938020238665350691292189)
                      ·
                        rfl

theorem cell23_7669267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 3].length) (baseStart_7669267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669267 prefixEnd_7669267 := by exact prefixLift 7669267
  have htrace : WordTrace (prefixWord ++ tailWord_7669267) baseStart_7669267 baseEnd_7669267 := by
    simpa [prefixWord, tailWord_7669267, baseEnd_7669267] using wordTrace_append hprefix tailTrace_7669267
  have hstable : (prefixWord ++ tailWord_7669267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669267).length < 2 ^ (prefixWord ++ tailWord_7669267).sum := by decide
  have hdescent : baseEnd_7669267 < baseStart_7669267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669268 : List Nat := [2, 4, 3, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_7669268 : Nat := 118140960795 + 7669268 * 2 ^ 59
def prefixEnd_7669268 : Nat := 4983230072969 + 3 ^ 40 * 7669268 * 2
def baseEnd_7669268 : Nat := 3938020752146005187379685

theorem tailTrace_7669268 : CollatzResearch.WordTrace tailWord_7669268 prefixEnd_7669268 3938020752146005187379685 := by
  unfold tailWord_7669268
  simp only [CollatzResearch.WordTrace]
  refine ⟨139860591989779658770236229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186480789319706211693648305 139860591989779658770236229)
  ·
    refine ⟨26223860998083686019419293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139860591989779658770236229 26223860998083686019419293)
    ·
      refine ⟨9833947874281382257282235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26223860998083686019419293 9833947874281382257282235)
      ·
        refine ⟨14750921811422073385923353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9833947874281382257282235 14750921811422073385923353)
        ·
          refine ⟨11063191358566555039442515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14750921811422073385923353 11063191358566555039442515)
          ·
            refine ⟨16594787037849832559163773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11063191358566555039442515 16594787037849832559163773)
            ·
              refine ⟨6223045139193687209686415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16594787037849832559163773 6223045139193687209686415)
              ·
                refine ⟨9334567708790530814529623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6223045139193687209686415 9334567708790530814529623)
                ·
                  refine ⟨14001851563185796221794435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9334567708790530814529623 14001851563185796221794435)
                  ·
                    refine ⟨21002777344778694332691653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14001851563185796221794435 21002777344778694332691653)
                    ·
                      refine ⟨3938020752146005187379685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21002777344778694332691653 3938020752146005187379685)
                      ·
                        rfl

theorem cell23_7669268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_7669268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669268 prefixEnd_7669268 := by exact prefixLift 7669268
  have htrace : WordTrace (prefixWord ++ tailWord_7669268) baseStart_7669268 baseEnd_7669268 := by
    simpa [prefixWord, tailWord_7669268, baseEnd_7669268] using wordTrace_append hprefix tailTrace_7669268
  have hstable : (prefixWord ++ tailWord_7669268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669268).length < 2 ^ (prefixWord ++ tailWord_7669268).sum := by decide
  have hdescent : baseEnd_7669268 < baseStart_7669268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669324 : List Nat := [2, 2, 1, 3, 1, 3, 2, 2, 1, 4, 2]
def baseStart_7669324 : Nat := 118140960795 + 7669324 * 2 ^ 59
def prefixEnd_7669324 : Nat := 4983230072969 + 3 ^ 40 * 7669324 * 2
def baseEnd_7669324 : Nat := 3938049507062656968279427

theorem tailTrace_7669324 : CollatzResearch.WordTrace tailWord_7669324 prefixEnd_7669324 3938049507062656968279427 := by
  unfold tailWord_7669324
  simp only [CollatzResearch.WordTrace]
  refine ⟨139861613233678219552255513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186482150978237626069674017 139861613233678219552255513)
  ·
    refine ⟨104896209925258664664191635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139861613233678219552255513 104896209925258664664191635)
    ·
      refine ⟨157344314887887996996287453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104896209925258664664191635 157344314887887996996287453)
      ·
        refine ⟨59004118082957998873607795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157344314887887996996287453 59004118082957998873607795)
        ·
          refine ⟨88506177124436998310411693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59004118082957998873607795 88506177124436998310411693)
          ·
            refine ⟨33189816421663874366404385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88506177124436998310411693 33189816421663874366404385)
            ·
              refine ⟨24892362316247905774803289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33189816421663874366404385 24892362316247905774803289)
              ·
                refine ⟨18669271737185929331102467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24892362316247905774803289 18669271737185929331102467)
                ·
                  refine ⟨28003907605778893996653701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18669271737185929331102467 28003907605778893996653701)
                  ·
                    refine ⟨5250732676083542624372569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28003907605778893996653701 5250732676083542624372569)
                    ·
                      refine ⟨3938049507062656968279427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5250732676083542624372569 3938049507062656968279427)
                      ·
                        rfl

theorem cell23_7669324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_7669324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669324 prefixEnd_7669324 := by exact prefixLift 7669324
  have htrace : WordTrace (prefixWord ++ tailWord_7669324) baseStart_7669324 baseEnd_7669324 := by
    simpa [prefixWord, tailWord_7669324, baseEnd_7669324] using wordTrace_append hprefix tailTrace_7669324
  have hstable : (prefixWord ++ tailWord_7669324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669324).length < 2 ^ (prefixWord ++ tailWord_7669324).sum := by decide
  have hdescent : baseEnd_7669324 < baseStart_7669324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669347 : List Nat := [1, 1, 1, 5, 1, 4, 2, 1, 7]
def baseStart_7669347 : Nat := 118140960795 + 7669347 * 2 ^ 59
def prefixEnd_7669347 : Nat := 4983230072969 + 3 ^ 40 * 7669347 * 2
def baseEnd_7669347 : Nat := 437562368568634486476869

theorem tailTrace_7669347 : CollatzResearch.WordTrace tailWord_7669347 prefixEnd_7669347 437562368568634486476869 := by
  unfold tailWord_7669347
  simp only [CollatzResearch.WordTrace]
  refine ⟨279724065346273114032598295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186482710230848742688398863 279724065346273114032598295)
  ·
    refine ⟨419586098019409671048897443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279724065346273114032598295 419586098019409671048897443)
    ·
      refine ⟨629379147029114506573346165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419586098019409671048897443 629379147029114506573346165)
      ·
        refine ⟨59004295033979484991251203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 629379147029114506573346165 59004295033979484991251203)
        ·
          refine ⟨88506442550969227486876805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59004295033979484991251203 88506442550969227486876805)
          ·
            refine ⟨16594957978306730153789401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88506442550969227486876805 16594957978306730153789401)
            ·
              refine ⟨12446218483730047615342051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16594957978306730153789401 12446218483730047615342051)
              ·
                refine ⟨18669327725595071423013077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12446218483730047615342051 18669327725595071423013077)
                ·
                  refine ⟨437562368568634486476869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18669327725595071423013077 437562368568634486476869)
                  ·
                    rfl

theorem cell23_7669347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 7].length) (baseStart_7669347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669347 prefixEnd_7669347 := by exact prefixLift 7669347
  have htrace : WordTrace (prefixWord ++ tailWord_7669347) baseStart_7669347 baseEnd_7669347 := by
    simpa [prefixWord, tailWord_7669347, baseEnd_7669347] using wordTrace_append hprefix tailTrace_7669347
  have hstable : (prefixWord ++ tailWord_7669347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669347).length < 2 ^ (prefixWord ++ tailWord_7669347).sum := by decide
  have hdescent : baseEnd_7669347 < baseStart_7669347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669358 : List Nat := [4, 1, 2, 2, 3, 2, 1, 1, 1, 4, 2]
def baseStart_7669358 : Nat := 118140960795 + 7669358 * 2 ^ 59
def prefixEnd_7669358 : Nat := 4983230072969 + 3 ^ 40 * 7669358 * 2
def baseEnd_7669358 : Nat := 3938066965404909835254271

theorem tailTrace_7669358 : CollatzResearch.WordTrace tailWord_7669358 prefixEnd_7669358 3938066965404909835254271 := by
  unfold tailWord_7669358
  simp only [CollatzResearch.WordTrace]
  refine ⟨34965558318654157863906091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186482977699488841940832485 34965558318654157863906091)
  ·
    refine ⟨52448337477981236795859137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34965558318654157863906091 52448337477981236795859137)
    ·
      refine ⟨39336253108485927596894353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52448337477981236795859137 39336253108485927596894353)
      ·
        refine ⟨29502189831364445697670765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39336253108485927596894353 29502189831364445697670765)
        ·
          refine ⟨11063321186761667136626537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29502189831364445697670765 11063321186761667136626537)
          ·
            refine ⟨8297490890071250352469903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11063321186761667136626537 8297490890071250352469903)
            ·
              refine ⟨12446236335106875528704855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8297490890071250352469903 12446236335106875528704855)
              ·
                refine ⟨18669354502660313293057283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12446236335106875528704855 18669354502660313293057283)
                ·
                  refine ⟨28004031753990469939585925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18669354502660313293057283 28004031753990469939585925)
                  ·
                    refine ⟨5250755953873213113672361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28004031753990469939585925 5250755953873213113672361)
                    ·
                      refine ⟨3938066965404909835254271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5250755953873213113672361 3938066965404909835254271)
                      ·
                        rfl

theorem cell23_7669358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_7669358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669358 prefixEnd_7669358 := by exact prefixLift 7669358
  have htrace : WordTrace (prefixWord ++ tailWord_7669358) baseStart_7669358 baseEnd_7669358 := by
    simpa [prefixWord, tailWord_7669358, baseEnd_7669358] using wordTrace_append hprefix tailTrace_7669358
  have hstable : (prefixWord ++ tailWord_7669358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669358).length < 2 ^ (prefixWord ++ tailWord_7669358).sum := by decide
  have hdescent : baseEnd_7669358 < baseStart_7669358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669370 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7]
def baseStart_7669370 : Nat := 118140960795 + 7669370 * 2 ^ 59
def prefixEnd_7669370 : Nat := 4983230072969 + 3 ^ 40 * 7669370 * 2
def baseEnd_7669370 : Nat := 3938073127172763788304215

theorem tailTrace_7669370 : CollatzResearch.WordTrace tailWord_7669370 prefixEnd_7669370 3938073127172763788304215 := by
  unfold tailWord_7669370
  simp only [CollatzResearch.WordTrace]
  refine ⟨69931226056297447240171391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186483269483459859307123709 69931226056297447240171391)
  ·
    refine ⟨104896839084446170860257087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69931226056297447240171391 104896839084446170860257087)
    ·
      refine ⟨157345258626669256290385631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104896839084446170860257087 157345258626669256290385631)
      ·
        refine ⟨236017887940003884435578447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157345258626669256290385631 236017887940003884435578447)
        ·
          refine ⟨354026831910005826653367671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236017887940003884435578447 354026831910005826653367671)
          ·
            refine ⟨531040247865008739980051507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354026831910005826653367671 531040247865008739980051507)
            ·
              refine ⟨796560371797513109970077261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531040247865008739980051507 796560371797513109970077261)
              ·
                refine ⟨298710139424067416238778973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 796560371797513109970077261 298710139424067416238778973)
                ·
                  refine ⟨112016302284025281089542115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 298710139424067416238778973 112016302284025281089542115)
                  ·
                    refine ⟨168024453426037921634313173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112016302284025281089542115 168024453426037921634313173)
                    ·
                      refine ⟨3938073127172763788304215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168024453426037921634313173 3938073127172763788304215)
                      ·
                        rfl

theorem cell23_7669370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_7669370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669370 prefixEnd_7669370 := by exact prefixLift 7669370
  have htrace : WordTrace (prefixWord ++ tailWord_7669370) baseStart_7669370 baseEnd_7669370 := by
    simpa [prefixWord, tailWord_7669370, baseEnd_7669370] using wordTrace_append hprefix tailTrace_7669370
  have hstable : (prefixWord ++ tailWord_7669370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669370).length < 2 ^ (prefixWord ++ tailWord_7669370).sum := by decide
  have hdescent : baseEnd_7669370 < baseStart_7669370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669377 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 1, 7]
def baseStart_7669377 : Nat := 118140960795 + 7669377 * 2 ^ 59
def prefixEnd_7669377 : Nat := 4983230072969 + 3 ^ 40 * 7669377 * 2
def baseEnd_7669377 : Nat := 1312692240512448420305561

theorem tailTrace_7669377 : CollatzResearch.WordTrace tailWord_7669377 prefixEnd_7669377 1312692240512448420305561 := by
  unfold tailWord_7669377
  simp only [CollatzResearch.WordTrace]
  refine ⟨279725159536164429156190385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186483439690776286104126923 279725159536164429156190385)
  ·
    refine ⟨209793869652123321867142789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279725159536164429156190385 209793869652123321867142789)
    ·
      refine ⟨39336350559773122850089273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209793869652123321867142789 39336350559773122850089273)
      ·
        refine ⟨29502262919829842137566955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39336350559773122850089273 29502262919829842137566955)
        ·
          refine ⟨44253394379744763206350433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29502262919829842137566955 44253394379744763206350433)
          ·
            refine ⟨33190045784808572404762825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44253394379744763206350433 33190045784808572404762825)
            ·
              refine ⟨24892534338606429303572119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33190045784808572404762825 24892534338606429303572119)
              ·
                refine ⟨37338801507909643955358179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24892534338606429303572119 37338801507909643955358179)
                ·
                  refine ⟨56008202261864465933037269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37338801507909643955358179 56008202261864465933037269)
                  ·
                    refine ⟨1312692240512448420305561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56008202261864465933037269 1312692240512448420305561)
                    ·
                      rfl

theorem cell23_7669377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_7669377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669377 prefixEnd_7669377 := by exact prefixLift 7669377
  have htrace : WordTrace (prefixWord ++ tailWord_7669377) baseStart_7669377 baseEnd_7669377 := by
    simpa [prefixWord, tailWord_7669377, baseEnd_7669377] using wordTrace_append hprefix tailTrace_7669377
  have hstable : (prefixWord ++ tailWord_7669377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669377).length < 2 ^ (prefixWord ++ tailWord_7669377).sum := by decide
  have hdescent : baseEnd_7669377 < baseStart_7669377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669404 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_7669404 : Nat := 118140960795 + 7669404 * 2 ^ 59
def prefixEnd_7669404 : Nat := 4983230072969 + 3 ^ 40 * 7669404 * 2
def baseEnd_7669404 : Nat := 3938090585515016655279059

theorem tailTrace_7669404 : CollatzResearch.WordTrace tailWord_7669404 prefixEnd_7669404 3938090585515016655279059 := by
  unfold tailWord_7669404
  simp only [CollatzResearch.WordTrace]
  refine ⟨139863072153533306383711633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186484096204711075178282177 139863072153533306383711633)
  ·
    refine ⟨104897304115149979787783725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139863072153533306383711633 104897304115149979787783725)
    ·
      refine ⟨39336489043181242420418897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104897304115149979787783725 39336489043181242420418897)
      ·
        refine ⟨29502366782385931815314173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39336489043181242420418897 29502366782385931815314173)
        ·
          refine ⟨11063387543394724430742815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29502366782385931815314173 11063387543394724430742815)
          ·
            refine ⟨16595081315092086646114223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11063387543394724430742815 16595081315092086646114223)
            ·
              refine ⟨24892621972638129969171335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16595081315092086646114223 24892621972638129969171335)
              ·
                refine ⟨37338932958957194953757003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24892621972638129969171335 37338932958957194953757003)
                ·
                  refine ⟨56008399438435792430635505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37338932958957194953757003 56008399438435792430635505)
                  ·
                    refine ⟨42006299578826844322976629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56008399438435792430635505 42006299578826844322976629)
                    ·
                      refine ⟨3938090585515016655279059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42006299578826844322976629 3938090585515016655279059)
                      ·
                        rfl

theorem cell23_7669404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_7669404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669404 prefixEnd_7669404 := by exact prefixLift 7669404
  have htrace : WordTrace (prefixWord ++ tailWord_7669404) baseStart_7669404 baseEnd_7669404 := by
    simpa [prefixWord, tailWord_7669404, baseEnd_7669404] using wordTrace_append hprefix tailTrace_7669404
  have hstable : (prefixWord ++ tailWord_7669404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669404).length < 2 ^ (prefixWord ++ tailWord_7669404).sum := by decide
  have hdescent : baseEnd_7669404 < baseStart_7669404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669434 : List Nat := [3, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3]
def baseStart_7669434 : Nat := 118140960795 + 7669434 * 2 ^ 59
def prefixEnd_7669434 : Nat := 4983230072969 + 3 ^ 40 * 7669434 * 2
def baseEnd_7669434 : Nat := 3938105989934651537903921

theorem tailTrace_7669434 : CollatzResearch.WordTrace tailWord_7669434 prefixEnd_7669434 3938105989934651537903921 := by
  unfold tailWord_7669434
  simp only [CollatzResearch.WordTrace]
  refine ⟨69931809624239481972753839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186484825664638618594010237 69931809624239481972753839)
  ·
    refine ⟨104897714436359222959130759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69931809624239481972753839 104897714436359222959130759)
    ·
      refine ⟨157346571654538834438696139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104897714436359222959130759 157346571654538834438696139)
      ·
        refine ⟨236019857481808251658044209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157346571654538834438696139 236019857481808251658044209)
        ·
          refine ⟨177014893111356188743533157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236019857481808251658044209 177014893111356188743533157)
          ·
            refine ⟨33190292458379285389412467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177014893111356188743533157 33190292458379285389412467)
            ·
              refine ⟨49785438687568928084118701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33190292458379285389412467 49785438687568928084118701)
              ·
                refine ⟨18669539507838348031544513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49785438687568928084118701 18669539507838348031544513)
                ·
                  refine ⟨14002154630878761023658385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18669539507838348031544513 14002154630878761023658385)
                  ·
                    refine ⟨10501615973159070767743789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14002154630878761023658385 10501615973159070767743789)
                    ·
                      refine ⟨3938105989934651537903921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10501615973159070767743789 3938105989934651537903921)
                      ·
                        rfl

theorem cell23_7669434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_7669434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669434 prefixEnd_7669434 := by exact prefixLift 7669434
  have htrace : WordTrace (prefixWord ++ tailWord_7669434) baseStart_7669434 baseEnd_7669434 := by
    simpa [prefixWord, tailWord_7669434, baseEnd_7669434] using wordTrace_append hprefix tailTrace_7669434
  have hstable : (prefixWord ++ tailWord_7669434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669434).length < 2 ^ (prefixWord ++ tailWord_7669434).sum := by decide
  have hdescent : baseEnd_7669434 < baseStart_7669434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669454 : List Nat := [4, 1, 1, 1, 3, 1, 4, 2, 6]
def baseStart_7669454 : Nat := 118140960795 + 7669454 * 2 ^ 59
def prefixEnd_7669454 : Nat := 4983230072969 + 3 ^ 40 * 7669454 * 2
def baseEnd_7669454 : Nat := 437568473283082384405981

theorem tailTrace_7669454 : CollatzResearch.WordTrace tailWord_7669454 prefixEnd_7669454 437568473283082384405981 := by
  unfold tailWord_7669454
  simp only [CollatzResearch.WordTrace]
  refine ⟨34965995994610683913342927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186485311971256980871162277 34965995994610683913342927)
  ·
    refine ⟨52448993991916025870014391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34965995994610683913342927 52448993991916025870014391)
    ·
      refine ⟨78673490987874038805021587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52448993991916025870014391 78673490987874038805021587)
      ·
        refine ⟨118010236481811058207532381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78673490987874038805021587 118010236481811058207532381)
        ·
          refine ⟨44253838680679146827824643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118010236481811058207532381 44253838680679146827824643)
          ·
            refine ⟨66380758021018720241736965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44253838680679146827824643 66380758021018720241736965)
            ·
              refine ⟨12446392128941010045325681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66380758021018720241736965 12446392128941010045325681)
              ·
                refine ⟨9334794096705757533994261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12446392128941010045325681 9334794096705757533994261)
                ·
                  refine ⟨437568473283082384405981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9334794096705757533994261 437568473283082384405981)
                  ·
                    rfl

theorem cell23_7669454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_7669454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669454 prefixEnd_7669454 := by exact prefixLift 7669454
  have htrace : WordTrace (prefixWord ++ tailWord_7669454) baseStart_7669454 baseEnd_7669454 := by
    simpa [prefixWord, tailWord_7669454, baseEnd_7669454] using wordTrace_append hprefix tailTrace_7669454
  have hstable : (prefixWord ++ tailWord_7669454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669454).length < 2 ^ (prefixWord ++ tailWord_7669454).sum := by decide
  have hdescent : baseEnd_7669454 < baseStart_7669454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669458 : List Nat := [3, 2, 2, 2, 2, 2, 1, 4, 1, 4]
def baseStart_7669458 : Nat := 118140960795 + 7669458 * 2 ^ 59
def prefixEnd_7669458 : Nat := 4983230072969 + 3 ^ 40 * 7669458 * 2
def baseEnd_7669458 : Nat := 1312706104490119814667937

theorem tailTrace_7669458 : CollatzResearch.WordTrace tailWord_7669458 prefixEnd_7669458 1312706104490119814667937 := by
  unfold tailWord_7669458
  simp only [CollatzResearch.WordTrace]
  refine ⟨69932028462217744997472257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186485409232580653326592685 69932028462217744997472257)
  ·
    refine ⟨52449021346663308748104193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69932028462217744997472257 52449021346663308748104193)
    ·
      refine ⟨39336766009997481561078145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52449021346663308748104193 39336766009997481561078145)
      ·
        refine ⟨29502574507498111170808609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39336766009997481561078145 29502574507498111170808609)
        ·
          refine ⟨22126930880623583378106457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29502574507498111170808609 22126930880623583378106457)
          ·
            refine ⟨16595198160467687533579843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22126930880623583378106457 16595198160467687533579843)
            ·
              refine ⟨24892797240701531300369765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16595198160467687533579843 24892797240701531300369765)
              ·
                refine ⟨4667399482631537118819331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24892797240701531300369765 4667399482631537118819331)
                ·
                  refine ⟨7001099223947305678228997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4667399482631537118819331 7001099223947305678228997)
                  ·
                    refine ⟨1312706104490119814667937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7001099223947305678228997 1312706104490119814667937)
                    ·
                      rfl

theorem cell23_7669458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_7669458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669458 prefixEnd_7669458 := by exact prefixLift 7669458
  have htrace : WordTrace (prefixWord ++ tailWord_7669458) baseStart_7669458 baseEnd_7669458 := by
    simpa [prefixWord, tailWord_7669458, baseEnd_7669458] using wordTrace_append hprefix tailTrace_7669458
  have hstable : (prefixWord ++ tailWord_7669458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669458).length < 2 ^ (prefixWord ++ tailWord_7669458).sum := by decide
  have hdescent : baseEnd_7669458 < baseStart_7669458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669477 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 2, 1, 7]
def baseStart_7669477 : Nat := 118140960795 + 7669477 * 2 ^ 59
def prefixEnd_7669477 : Nat := 4983230072969 + 3 ^ 40 * 7669477 * 2
def baseEnd_7669477 : Nat := 3938128069602794869666223

theorem tailTrace_7669477 : CollatzResearch.WordTrace tailWord_7669477 prefixEnd_7669477 3938128069602794869666223 := by
  unfold tailWord_7669477
  simp only [CollatzResearch.WordTrace]
  refine ⟨279728806835802146234830685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186485871223868097489887123 279728806835802146234830685)
  ·
    refine ⟨104898302563425804838061507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279728806835802146234830685 104898302563425804838061507)
    ·
      refine ⟨157347453845138707257092261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104898302563425804838061507 157347453845138707257092261)
      ·
        refine ⟨29502647595963507610704799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157347453845138707257092261 29502647595963507610704799)
        ·
          refine ⟨44253971393945261416057199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29502647595963507610704799 44253971393945261416057199)
          ·
            refine ⟨66380957090917892124085799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44253971393945261416057199 66380957090917892124085799)
            ·
              refine ⟨99571435636376838186128699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66380957090917892124085799 99571435636376838186128699)
              ·
                refine ⟨149357153454565257279193049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99571435636376838186128699 149357153454565257279193049)
                ·
                  refine ⟨112017865090923942959394787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149357153454565257279193049 112017865090923942959394787)
                  ·
                    refine ⟨168026797636385914439092181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112017865090923942959394787 168026797636385914439092181)
                    ·
                      refine ⟨3938128069602794869666223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168026797636385914439092181 3938128069602794869666223)
                      ·
                        rfl

theorem cell23_7669477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_7669477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669477 prefixEnd_7669477 := by exact prefixLift 7669477
  have htrace : WordTrace (prefixWord ++ tailWord_7669477) baseStart_7669477 baseEnd_7669477 := by
    simpa [prefixWord, tailWord_7669477, baseEnd_7669477] using wordTrace_append hprefix tailTrace_7669477
  have hstable : (prefixWord ++ tailWord_7669477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669477).length < 2 ^ (prefixWord ++ tailWord_7669477).sum := by decide
  have hdescent : baseEnd_7669477 < baseStart_7669477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669491 : List Nat := [1, 1, 1, 2, 2, 3, 5, 1, 2, 3, 2]
def baseStart_7669491 : Nat := 118140960795 + 7669491 * 2 ^ 59
def prefixEnd_7669491 : Nat := 4983230072969 + 3 ^ 40 * 7669491 * 2
def baseEnd_7669491 : Nat := 3938135258331957814891159

theorem tailTrace_7669491 : CollatzResearch.WordTrace tailWord_7669491 prefixEnd_7669491 3938135258331957814891159 := by
  unfold tailWord_7669491
  simp only [CollatzResearch.WordTrace]
  refine ⟨279729317457751426625840327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186486211638500951083893551 279729317457751426625840327)
  ·
    refine ⟨419593976186627139938760491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279729317457751426625840327 419593976186627139938760491)
    ·
      refine ⟨629390964279940709908140737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419593976186627139938760491 629390964279940709908140737)
      ·
        refine ⟨472043223209955532431105553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629390964279940709908140737 472043223209955532431105553)
        ·
          refine ⟨354032417407466649323329165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472043223209955532431105553 354032417407466649323329165)
          ·
            refine ⟨132762156527799993496248437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354032417407466649323329165 132762156527799993496248437)
            ·
              refine ⟨12446452174481249390273291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132762156527799993496248437 12446452174481249390273291)
              ·
                refine ⟨18669678261721874085409937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12446452174481249390273291 18669678261721874085409937)
                ·
                  refine ⟨14002258696291405564057453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18669678261721874085409937 14002258696291405564057453)
                  ·
                    refine ⟨5250847011109277086521545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14002258696291405564057453 5250847011109277086521545)
                    ·
                      refine ⟨3938135258331957814891159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5250847011109277086521545 3938135258331957814891159)
                      ·
                        rfl

theorem cell23_7669491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 3, 2].length) (baseStart_7669491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669491 prefixEnd_7669491 := by exact prefixLift 7669491
  have htrace : WordTrace (prefixWord ++ tailWord_7669491) baseStart_7669491 baseEnd_7669491 := by
    simpa [prefixWord, tailWord_7669491, baseEnd_7669491] using wordTrace_append hprefix tailTrace_7669491
  have hstable : (prefixWord ++ tailWord_7669491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669491).length < 2 ^ (prefixWord ++ tailWord_7669491).sum := by decide
  have hdescent : baseEnd_7669491 < baseStart_7669491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669492 : List Nat := [2, 6, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_7669492 : Nat := 118140960795 + 7669492 * 2 ^ 59
def prefixEnd_7669492 : Nat := 4983230072969 + 3 ^ 40 * 7669492 * 2
def baseEnd_7669492 : Nat := 1312711923937537436992885

theorem tailTrace_7669492 : CollatzResearch.WordTrace tailWord_7669492 prefixEnd_7669492 1312711923937537436992885 := by
  unfold tailWord_7669492
  simp only [CollatzResearch.WordTrace]
  refine ⟨139864676965373901898313365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186486235953831869197751153 139864676965373901898313365)
  ·
    refine ⟨6556156732751901651483439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 139864676965373901898313365 6556156732751901651483439)
    ·
      refine ⟨9834235099127852477225159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6556156732751901651483439 9834235099127852477225159)
      ·
        refine ⟨14751352648691778715837739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9834235099127852477225159 14751352648691778715837739)
        ·
          refine ⟨22127028973037668073756609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14751352648691778715837739 22127028973037668073756609)
          ·
            refine ⟨16595271729778251055317457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22127028973037668073756609 16595271729778251055317457)
            ·
              refine ⟨12446453797333688291488093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16595271729778251055317457 12446453797333688291488093)
              ·
                refine ⟨4667420174000133109308035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12446453797333688291488093 4667420174000133109308035)
                ·
                  refine ⟨7001130261000199663962053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4667420174000133109308035 7001130261000199663962053)
                  ·
                    refine ⟨1312711923937537436992885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7001130261000199663962053 1312711923937537436992885)
                    ·
                      rfl

theorem cell23_7669492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_7669492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669492 prefixEnd_7669492 := by exact prefixLift 7669492
  have htrace : WordTrace (prefixWord ++ tailWord_7669492) baseStart_7669492 baseEnd_7669492 := by
    simpa [prefixWord, tailWord_7669492, baseEnd_7669492] using wordTrace_append hprefix tailTrace_7669492
  have hstable : (prefixWord ++ tailWord_7669492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669492).length < 2 ^ (prefixWord ++ tailWord_7669492).sum := by decide
  have hdescent : baseEnd_7669492 < baseStart_7669492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669504 : List Nat := [2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 4]
def baseStart_7669504 : Nat := 118140960795 + 7669504 * 2 ^ 59
def prefixEnd_7669504 : Nat := 4983230072969 + 3 ^ 40 * 7669504 * 2
def baseEnd_7669504 : Nat := 3938141933580466264028599

theorem tailTrace_7669504 : CollatzResearch.WordTrace tailWord_7669504 prefixEnd_7669504 3938141933580466264028599 := by
  unfold tailWord_7669504
  simp only [CollatzResearch.WordTrace]
  refine ⟨139864895803352164923031783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186486527737802886564042377 139864895803352164923031783)
  ·
    refine ⟨209797343705028247384547675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139864895803352164923031783 209797343705028247384547675)
    ·
      refine ⟨314696015557542371076821513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209797343705028247384547675 314696015557542371076821513)
      ·
        refine ⟨236022011668156778307616135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314696015557542371076821513 236022011668156778307616135)
        ·
          refine ⟨354033017502235167461424203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236022011668156778307616135 354033017502235167461424203)
          ·
            refine ⟨531049526253352751192136305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354033017502235167461424203 531049526253352751192136305)
            ·
              refine ⟨398287144690014563394102229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531049526253352751192136305 398287144690014563394102229)
              ·
                refine ⟨9334854953672216329549271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 398287144690014563394102229 9334854953672216329549271)
                ·
                  refine ⟨14002282430508324494323907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9334854953672216329549271 14002282430508324494323907)
                  ·
                    refine ⟨21003423645762486741485861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14002282430508324494323907 21003423645762486741485861)
                    ·
                      refine ⟨3938141933580466264028599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21003423645762486741485861 3938141933580466264028599)
                      ·
                        rfl

theorem cell23_7669504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 4].length) (baseStart_7669504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669504 prefixEnd_7669504 := by exact prefixLift 7669504
  have htrace : WordTrace (prefixWord ++ tailWord_7669504) baseStart_7669504 baseEnd_7669504 := by
    simpa [prefixWord, tailWord_7669504, baseEnd_7669504] using wordTrace_append hprefix tailTrace_7669504
  have hstable : (prefixWord ++ tailWord_7669504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669504).length < 2 ^ (prefixWord ++ tailWord_7669504).sum := by decide
  have hdescent : baseEnd_7669504 < baseStart_7669504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669538 : List Nat := [3, 3, 1, 1, 2, 1, 1, 4, 3, 2, 2]
def baseStart_7669538 : Nat := 118140960795 + 7669538 * 2 ^ 59
def prefixEnd_7669538 : Nat := 4983230072969 + 3 ^ 40 * 7669538 * 2
def baseEnd_7669538 : Nat := 3938159391922719131003443

theorem tailTrace_7669538 : CollatzResearch.WordTrace tailWord_7669538 prefixEnd_7669538 3938159391922719131003443 := by
  unfold tailWord_7669538
  simp only [CollatzResearch.WordTrace]
  refine ⟨69932757922145288413200317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186487354459054102435200845 69932757922145288413200317)
  ·
    refine ⟨26224784220804483154950119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69932757922145288413200317 26224784220804483154950119)
    ·
      refine ⟨39337176331206724732425179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26224784220804483154950119 39337176331206724732425179)
      ·
        refine ⟨59005764496810087098637769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39337176331206724732425179 59005764496810087098637769)
        ·
          refine ⟨44254323372607565323978327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59005764496810087098637769 44254323372607565323978327)
          ·
            refine ⟨66381485058911347985967491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44254323372607565323978327 66381485058911347985967491)
            ·
              refine ⟨99572227588367021978951237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66381485058911347985967491 99572227588367021978951237)
              ·
                refine ⟨18669792672818816621053357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99572227588367021978951237 18669792672818816621053357)
                ·
                  refine ⟨7001172252307056232895009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18669792672818816621053357 7001172252307056232895009)
                  ·
                    refine ⟨5250879189230292174671257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7001172252307056232895009 5250879189230292174671257)
                    ·
                      refine ⟨3938159391922719131003443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5250879189230292174671257 3938159391922719131003443)
                      ·
                        rfl

theorem cell23_7669538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_7669538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669538 prefixEnd_7669538 := by exact prefixLift 7669538
  have htrace : WordTrace (prefixWord ++ tailWord_7669538) baseStart_7669538 baseEnd_7669538 := by
    simpa [prefixWord, tailWord_7669538, baseEnd_7669538] using wordTrace_append hprefix tailTrace_7669538
  have hstable : (prefixWord ++ tailWord_7669538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669538).length < 2 ^ (prefixWord ++ tailWord_7669538).sum := by decide
  have hdescent : baseEnd_7669538 < baseStart_7669538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669541 : List Nat := [1, 3, 1, 2, 3, 2, 1, 4, 1, 2, 3]
def baseStart_7669541 : Nat := 118140960795 + 7669541 * 2 ^ 59
def prefixEnd_7669541 : Nat := 4983230072969 + 3 ^ 40 * 7669541 * 2
def baseEnd_7669541 : Nat := 3938160932364682619265929

theorem tailTrace_7669541 : CollatzResearch.WordTrace tailWord_7669541 prefixEnd_7669541 3938160932364682619265929 := by
  unfold tailWord_7669541
  simp only [CollatzResearch.WordTrace]
  refine ⟨279731141107570285165160477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186487427405046856776773651 279731141107570285165160477)
  ·
    refine ⟨104899177915338856936935179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279731141107570285165160477 104899177915338856936935179)
    ·
      refine ⟨157348766873008285405402769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104899177915338856936935179 157348766873008285405402769)
      ·
        refine ⟨118011575154756214054052077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157348766873008285405402769 118011575154756214054052077)
        ·
          refine ⟨44254340683033580270269529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118011575154756214054052077 44254340683033580270269529)
          ·
            refine ⟨33190755512275185202702147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44254340683033580270269529 33190755512275185202702147)
            ·
              refine ⟨49786133268412777804053221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33190755512275185202702147 49786133268412777804053221)
              ·
                refine ⟨9334899987827395838259979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49786133268412777804053221 9334899987827395838259979)
                ·
                  refine ⟨14002349981741093757389969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9334899987827395838259979 14002349981741093757389969)
                  ·
                    refine ⟨10501762486305820318042477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14002349981741093757389969 10501762486305820318042477)
                    ·
                      refine ⟨3938160932364682619265929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10501762486305820318042477 3938160932364682619265929)
                      ·
                        rfl

theorem cell23_7669541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_7669541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669541 prefixEnd_7669541 := by exact prefixLift 7669541
  have htrace : WordTrace (prefixWord ++ tailWord_7669541) baseStart_7669541 baseEnd_7669541 := by
    simpa [prefixWord, tailWord_7669541, baseEnd_7669541] using wordTrace_append hprefix tailTrace_7669541
  have hstable : (prefixWord ++ tailWord_7669541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669541).length < 2 ^ (prefixWord ++ tailWord_7669541).sum := by decide
  have hdescent : baseEnd_7669541 < baseStart_7669541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669544 : List Nat := [2, 1, 5, 1, 1, 3, 1, 9]
def baseStart_7669544 : Nat := 118140960795 + 7669544 * 2 ^ 59
def prefixEnd_7669544 : Nat := 4983230072969 + 3 ^ 40 * 7669544 * 2
def baseEnd_7669544 : Nat := 145857869363209115093645

theorem tailTrace_7669544 : CollatzResearch.WordTrace tailWord_7669544 prefixEnd_7669544 145857869363209115093645 := by
  unfold tailWord_7669544
  simp only [CollatzResearch.WordTrace]
  refine ⟨139865625263279708338759843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186487500351039611118346457 139865625263279708338759843)
  ·
    refine ⟨209798437894919562508139765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139865625263279708338759843 209798437894919562508139765)
    ·
      refine ⟨19668603552648708985138103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209798437894919562508139765 19668603552648708985138103)
      ·
        refine ⟨29502905328973063477707155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19668603552648708985138103 29502905328973063477707155)
        ·
          refine ⟨44254357993459595216560733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29502905328973063477707155 44254357993459595216560733)
          ·
            refine ⟨16595384247547348206210275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44254357993459595216560733 16595384247547348206210275)
            ·
              refine ⟨24893076371321022309315413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16595384247547348206210275 24893076371321022309315413)
              ·
                refine ⟨145857869363209115093645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24893076371321022309315413 145857869363209115093645)
                ·
                  rfl

theorem cell23_7669544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 9].length) (baseStart_7669544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669544 prefixEnd_7669544 := by exact prefixLift 7669544
  have htrace : WordTrace (prefixWord ++ tailWord_7669544) baseStart_7669544 baseEnd_7669544 := by
    simpa [prefixWord, tailWord_7669544, baseEnd_7669544] using wordTrace_append hprefix tailTrace_7669544
  have hstable : (prefixWord ++ tailWord_7669544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669544).length < 2 ^ (prefixWord ++ tailWord_7669544).sum := by decide
  have hdescent : baseEnd_7669544 < baseStart_7669544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669558 : List Nat := [5, 1, 2, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_7669558 : Nat := 118140960795 + 7669558 * 2 ^ 59
def prefixEnd_7669558 : Nat := 4983230072969 + 3 ^ 40 * 7669558 * 2
def baseEnd_7669558 : Nat := 3938169661535809052753351

theorem tailTrace_7669558 : CollatzResearch.WordTrace tailWord_7669558 prefixEnd_7669558 3938169661535809052753351 := by
  unfold tailWord_7669558
  simp only [CollatzResearch.WordTrace]
  refine ⟨17483235071781793566783083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186487840765672464712352885 17483235071781793566783083)
  ·
    refine ⟨26224852607672690350174625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17483235071781793566783083 26224852607672690350174625)
    ·
      refine ⟨19668639455754517762630969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26224852607672690350174625 19668639455754517762630969)
      ·
        refine ⟨14751479591815888321973227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19668639455754517762630969 14751479591815888321973227)
        ·
          refine ⟨22127219387723832482959841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14751479591815888321973227 22127219387723832482959841)
          ·
            refine ⟨16595414540792874362219881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22127219387723832482959841 16595414540792874362219881)
            ·
              refine ⟨12446560905594655771664911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16595414540792874362219881 12446560905594655771664911)
              ·
                refine ⟨18669841358391983657497367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12446560905594655771664911 18669841358391983657497367)
                ·
                  refine ⟨28004762037587975486246051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18669841358391983657497367 28004762037587975486246051)
                  ·
                    refine ⟨42007143056381963229369077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28004762037587975486246051 42007143056381963229369077)
                    ·
                      refine ⟨3938169661535809052753351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42007143056381963229369077 3938169661535809052753351)
                      ·
                        rfl

theorem cell23_7669558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_7669558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669558 prefixEnd_7669558 := by exact prefixLift 7669558
  have htrace : WordTrace (prefixWord ++ tailWord_7669558) baseStart_7669558 baseEnd_7669558 := by
    simpa [prefixWord, tailWord_7669558, baseEnd_7669558] using wordTrace_append hprefix tailTrace_7669558
  have hstable : (prefixWord ++ tailWord_7669558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669558).length < 2 ^ (prefixWord ++ tailWord_7669558).sum := by decide
  have hdescent : baseEnd_7669558 < baseStart_7669558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669561 : List Nat := [1, 2, 1, 7, 1, 2, 9]
def baseStart_7669561 : Nat := 118140960795 + 7669561 * 2 ^ 59
def prefixEnd_7669561 : Nat := 4983230072969 + 3 ^ 40 * 7669561 * 2
def baseEnd_7669561 : Nat := 48619397555281142481677

theorem tailTrace_7669561 : CollatzResearch.WordTrace tailWord_7669561 prefixEnd_7669561 48619397555281142481677 := by
  unfold tailWord_7669561
  simp only [CollatzResearch.WordTrace]
  refine ⟨279731870567497828580888537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186487913711665219053925691 279731870567497828580888537)
  ·
    refine ⟨209798902925623371435666403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279731870567497828580888537 209798902925623371435666403)
    ·
      refine ⟨314698354388435057153499605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209798902925623371435666403 314698354388435057153499605)
      ·
        refine ⟨7375742680978946652035147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 314698354388435057153499605 7375742680978946652035147)
        ·
          refine ⟨11063614021468419978052721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7375742680978946652035147 11063614021468419978052721)
          ·
            refine ⟨8297710516101314983539541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11063614021468419978052721 8297710516101314983539541)
            ·
              refine ⟨48619397555281142481677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8297710516101314983539541 48619397555281142481677)
              ·
                rfl

theorem cell23_7669561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 9].length) (baseStart_7669561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669561 prefixEnd_7669561 := by exact prefixLift 7669561
  have htrace : WordTrace (prefixWord ++ tailWord_7669561) baseStart_7669561 baseEnd_7669561 := by
    simpa [prefixWord, tailWord_7669561, baseEnd_7669561] using wordTrace_append hprefix tailTrace_7669561
  have hstable : (prefixWord ++ tailWord_7669561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669561).length < 2 ^ (prefixWord ++ tailWord_7669561).sum := by decide
  have hdescent : baseEnd_7669561 < baseStart_7669561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669571 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 4, 1, 3]
def baseStart_7669571 : Nat := 118140960795 + 7669571 * 2 ^ 59
def prefixEnd_7669571 : Nat := 4983230072969 + 3 ^ 40 * 7669571 * 2
def baseEnd_7669571 : Nat := 3938176336784317501890791

theorem tailTrace_7669571 : CollatzResearch.WordTrace tailWord_7669571 prefixEnd_7669571 3938176336784317501890791 := by
  unfold tailWord_7669571
  simp only [CollatzResearch.WordTrace]
  refine ⟨279732235297461600288752567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186488156864974400192501711 279732235297461600288752567)
  ·
    refine ⟨419598352946192400433128851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279732235297461600288752567 419598352946192400433128851)
    ·
      refine ⟨629397529419288600649693277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419598352946192400433128851 629397529419288600649693277)
      ·
        refine ⟨236024073532233225243634979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 629397529419288600649693277 236024073532233225243634979)
        ·
          refine ⟨354036110298349837865452469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236024073532233225243634979 354036110298349837865452469)
          ·
            refine ⟨33190885340470297299886169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 354036110298349837865452469 33190885340470297299886169)
            ·
              refine ⟨24893164005352722974914627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33190885340470297299886169 24893164005352722974914627)
              ·
                refine ⟨37339746008029084462371941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24893164005352722974914627 37339746008029084462371941)
                ·
                  refine ⟨7001202376505453336694739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37339746008029084462371941 7001202376505453336694739)
                  ·
                    refine ⟨10501803564758180005042109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7001202376505453336694739 10501803564758180005042109)
                    ·
                      refine ⟨3938176336784317501890791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10501803564758180005042109 3938176336784317501890791)
                      ·
                        rfl

theorem cell23_7669571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 1, 3].length) (baseStart_7669571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669571 prefixEnd_7669571 := by exact prefixLift 7669571
  have htrace : WordTrace (prefixWord ++ tailWord_7669571) baseStart_7669571 baseEnd_7669571 := by
    simpa [prefixWord, tailWord_7669571, baseEnd_7669571] using wordTrace_append hprefix tailTrace_7669571
  have hstable : (prefixWord ++ tailWord_7669571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669571).length < 2 ^ (prefixWord ++ tailWord_7669571).sum := by decide
  have hdescent : baseEnd_7669571 < baseStart_7669571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669622 : List Nat := [5, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_7669622 : Nat := 118140960795 + 7669622 * 2 ^ 59
def prefixEnd_7669622 : Nat := 4983230072969 + 3 ^ 40 * 7669622 * 2
def baseEnd_7669622 : Nat := 3938202524297696802353057

theorem tailTrace_7669622 : CollatzResearch.WordTrace tailWord_7669622 prefixEnd_7669622 3938202524297696802353057 := by
  unfold tailWord_7669622
  simp only [CollatzResearch.WordTrace]
  refine ⟨17483380963767302249928695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186489396946851223999239413 17483380963767302249928695)
  ·
    refine ⟨26225071445650953374893043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17483380963767302249928695 26225071445650953374893043)
    ·
      refine ⟨39337607168476430062339565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26225071445650953374893043 39337607168476430062339565)
      ·
        refine ⟨14751602688178661273377337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39337607168476430062339565 14751602688178661273377337)
        ·
          refine ⟨11063702016133995955033003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14751602688178661273377337 11063702016133995955033003)
          ·
            refine ⟨16595553024200993932549505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11063702016133995955033003 16595553024200993932549505)
            ·
              refine ⟨12446664768150745449412129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16595553024200993932549505 12446664768150745449412129)
              ·
                refine ⟨9334998576113059087059097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12446664768150745449412129 9334998576113059087059097)
                ·
                  refine ⟨7001248932084794315294323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9334998576113059087059097 7001248932084794315294323)
                  ·
                    refine ⟨10501873398127191472941485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7001248932084794315294323 10501873398127191472941485)
                    ·
                      refine ⟨3938202524297696802353057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10501873398127191472941485 3938202524297696802353057)
                      ·
                        rfl

theorem cell23_7669622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_7669622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669622 prefixEnd_7669622 := by exact prefixLift 7669622
  have htrace : WordTrace (prefixWord ++ tailWord_7669622) baseStart_7669622 baseEnd_7669622 := by
    simpa [prefixWord, tailWord_7669622, baseEnd_7669622] using wordTrace_append hprefix tailTrace_7669622
  have hstable : (prefixWord ++ tailWord_7669622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669622).length < 2 ^ (prefixWord ++ tailWord_7669622).sum := by decide
  have hdescent : baseEnd_7669622 < baseStart_7669622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669668 : List Nat := [2, 3, 1, 2, 1, 4, 2, 3, 5]
def baseStart_7669668 : Nat := 118140960795 + 7669668 * 2 ^ 59
def prefixEnd_7669668 : Nat := 4983230072969 + 3 ^ 40 * 7669668 * 2
def baseEnd_7669668 : Nat := 437580682711978180264205

theorem tailTrace_7669668 : CollatzResearch.WordTrace tailWord_7669668 prefixEnd_7669668 437580682711978180264205 := by
  unfold tailWord_7669668
  simp only [CollatzResearch.WordTrace]
  refine ⟨139867886589055092927516829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186490515452073457236689105 139867886589055092927516829)
  ·
    refine ⟨52450457470895659847818811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139867886589055092927516829 52450457470895659847818811)
    ·
      refine ⟨78675686206343489771728217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52450457470895659847818811 78675686206343489771728217)
      ·
        refine ⟨59006764654757617328796163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78675686206343489771728217 59006764654757617328796163)
        ·
          refine ⟨88510146982136425993194245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59006764654757617328796163 88510146982136425993194245)
          ·
            refine ⟨16595652559150579873723921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88510146982136425993194245 16595652559150579873723921)
            ·
              refine ⟨12446739419362934905292941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16595652559150579873723921 12446739419362934905292941)
              ·
                refine ⟨4667527282261100589484853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12446739419362934905292941 4667527282261100589484853)
                ·
                  refine ⟨437580682711978180264205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4667527282261100589484853 437580682711978180264205)
                  ·
                    rfl

theorem cell23_7669668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_7669668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669668 prefixEnd_7669668 := by exact prefixLift 7669668
  have htrace : WordTrace (prefixWord ++ tailWord_7669668) baseStart_7669668 baseEnd_7669668 := by
    simpa [prefixWord, tailWord_7669668, baseEnd_7669668] using wordTrace_append hprefix tailTrace_7669668
  have hstable : (prefixWord ++ tailWord_7669668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669668).length < 2 ^ (prefixWord ++ tailWord_7669668).sum := by decide
  have hdescent : baseEnd_7669668 < baseStart_7669668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669701 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 1, 6, 2]
def baseStart_7669701 : Nat := 118140960795 + 7669701 * 2 ^ 59
def prefixEnd_7669701 : Nat := 4983230072969 + 3 ^ 40 * 7669701 * 2
def baseEnd_7669701 : Nat := 3938243089269401993265193

theorem tailTrace_7669701 : CollatzResearch.WordTrace tailWord_7669701 prefixEnd_7669701 3938243089269401993265193 := by
  unfold tailWord_7669701
  simp only [CollatzResearch.WordTrace]
  refine ⟨279736976786990632490984957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186491317857993754993989971 279736976786990632490984957)
  ·
    refine ⟨104901366295121487184119359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279736976786990632490984957 104901366295121487184119359)
    ·
      refine ⟨157352049442682230776179039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104901366295121487184119359 157352049442682230776179039)
      ·
        refine ⟨236028074164023346164268559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157352049442682230776179039 236028074164023346164268559)
        ·
          refine ⟨354042111246035019246402839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236028074164023346164268559 354042111246035019246402839)
          ·
            refine ⟨531063166869052528869604259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354042111246035019246402839 531063166869052528869604259)
            ·
              refine ⟨796594750303578793304406389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531063166869052528869604259 796594750303578793304406389)
              ·
                refine ⟨74680757840960511872288099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 796594750303578793304406389 74680757840960511872288099)
                ·
                  refine ⟨112021136761440767808432149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74680757840960511872288099 112021136761440767808432149)
                  ·
                    refine ⟨5250990785692535991020257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112021136761440767808432149 5250990785692535991020257)
                    ·
                      refine ⟨3938243089269401993265193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5250990785692535991020257 3938243089269401993265193)
                      ·
                        rfl

theorem cell23_7669701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 6, 2].length) (baseStart_7669701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669701 prefixEnd_7669701 := by exact prefixLift 7669701
  have htrace : WordTrace (prefixWord ++ tailWord_7669701) baseStart_7669701 baseEnd_7669701 := by
    simpa [prefixWord, tailWord_7669701, baseEnd_7669701] using wordTrace_append hprefix tailTrace_7669701
  have hstable : (prefixWord ++ tailWord_7669701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669701).length < 2 ^ (prefixWord ++ tailWord_7669701).sum := by decide
  have hdescent : baseEnd_7669701 < baseStart_7669701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669711 : List Nat := [1, 1, 2, 1, 1, 5, 1, 4, 3, 4]
def baseStart_7669711 : Nat := 118140960795 + 7669711 * 2 ^ 59
def prefixEnd_7669711 : Nat := 4983230072969 + 3 ^ 40 * 7669711 * 2
def baseEnd_7669711 : Nat := 1312749408025315651380049

theorem tailTrace_7669711 : CollatzResearch.WordTrace tailWord_7669711 prefixEnd_7669711 1312749408025315651380049 := by
  unfold tailWord_7669711
  simp only [CollatzResearch.WordTrace]
  refine ⟨279737341516954404198848987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186491561011302936132565991 279737341516954404198848987)
  ·
    refine ⟨419606012275431606298273481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279737341516954404198848987 419606012275431606298273481)
    ·
      refine ⟨314704509206573704723705111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419606012275431606298273481 314704509206573704723705111)
      ·
        refine ⟨472056763809860557085557667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314704509206573704723705111 472056763809860557085557667)
        ·
          refine ⟨708085145714790835628336501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472056763809860557085557667 708085145714790835628336501)
          ·
            refine ⟨66382982410761640840156547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 708085145714790835628336501 66382982410761640840156547)
            ·
              refine ⟨99574473616142461260234821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66382982410761640840156547 99574473616142461260234821)
              ·
                refine ⟨18670213803026711486294029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99574473616142461260234821 18670213803026711486294029)
                ·
                  refine ⟨7001330176135016807360261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18670213803026711486294029 7001330176135016807360261)
                  ·
                    refine ⟨1312749408025315651380049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7001330176135016807360261 1312749408025315651380049)
                    ·
                      rfl

theorem cell23_7669711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 4].length) (baseStart_7669711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669711 prefixEnd_7669711 := by exact prefixLift 7669711
  have htrace : WordTrace (prefixWord ++ tailWord_7669711) baseStart_7669711 baseEnd_7669711 := by
    simpa [prefixWord, tailWord_7669711, baseEnd_7669711] using wordTrace_append hprefix tailTrace_7669711
  have hstable : (prefixWord ++ tailWord_7669711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669711).length < 2 ^ (prefixWord ++ tailWord_7669711).sum := by decide
  have hdescent : baseEnd_7669711 < baseStart_7669711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669738 : List Nat := [3, 1, 3, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_7669738 : Nat := 118140960795 + 7669738 * 2 ^ 59
def prefixEnd_7669738 : Nat := 4983230072969 + 3 ^ 40 * 7669738 * 2
def baseEnd_7669738 : Nat := 3938262088053618348502523

theorem tailTrace_7669738 : CollatzResearch.WordTrace tailWord_7669738 prefixEnd_7669738 3938262088053618348502523 := by
  unfold tailWord_7669738
  simp only [CollatzResearch.WordTrace]
  refine ⟨69934581571964146952520467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186492217525237725206721245 69934581571964146952520467)
  ·
    refine ⟨104901872357946220428780701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69934581571964146952520467 104901872357946220428780701)
    ·
      refine ⟨39338202134229832660792763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104901872357946220428780701 39338202134229832660792763)
      ·
        refine ⟨59007303201344748991189145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39338202134229832660792763 59007303201344748991189145)
        ·
          refine ⟨44255477401008561743391859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59007303201344748991189145 44255477401008561743391859)
          ·
            refine ⟨66383216101512842615087789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44255477401008561743391859 66383216101512842615087789)
            ·
              refine ⟨24893706038067315980657921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66383216101512842615087789 24893706038067315980657921)
              ·
                refine ⟨18670279528550486985493441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24893706038067315980657921 18670279528550486985493441)
                ·
                  refine ⟨14002709646412865239120081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18670279528550486985493441 14002709646412865239120081)
                  ·
                    refine ⟨10502032234809648929340061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14002709646412865239120081 10502032234809648929340061)
                    ·
                      refine ⟨3938262088053618348502523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10502032234809648929340061 3938262088053618348502523)
                      ·
                        rfl

theorem cell23_7669738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_7669738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669738 prefixEnd_7669738 := by exact prefixLift 7669738
  have htrace : WordTrace (prefixWord ++ tailWord_7669738) baseStart_7669738 baseEnd_7669738 := by
    simpa [prefixWord, tailWord_7669738, baseEnd_7669738] using wordTrace_append hprefix tailTrace_7669738
  have hstable : (prefixWord ++ tailWord_7669738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669738).length < 2 ^ (prefixWord ++ tailWord_7669738).sum := by decide
  have hdescent : baseEnd_7669738 < baseStart_7669738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669744 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 8]
def baseStart_7669744 : Nat := 118140960795 + 7669744 * 2 ^ 59
def prefixEnd_7669744 : Nat := 4983230072969 + 3 ^ 40 * 7669744 * 2
def baseEnd_7669744 : Nat := 3938265168937545325027495

theorem tailTrace_7669744 : CollatzResearch.WordTrace tailWord_7669744 prefixEnd_7669744 3938265168937545325027495 := by
  unfold tailWord_7669744
  simp only [CollatzResearch.WordTrace]
  refine ⟨139869272562917425417400143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186492363417223233889866857 139869272562917425417400143)
  ·
    refine ⟨209803908844376138126100215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139869272562917425417400143 209803908844376138126100215)
    ·
      refine ⟨314705863266564207189150323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209803908844376138126100215 314705863266564207189150323)
      ·
        refine ⟨472058794899846310783725485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314705863266564207189150323 472058794899846310783725485)
        ·
          refine ⟨177022048087442366543897057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472058794899846310783725485 177022048087442366543897057)
          ·
            refine ⟨132766536065581774907922793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177022048087442366543897057 132766536065581774907922793)
            ·
              refine ⟨99574902049186331180942095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132766536065581774907922793 99574902049186331180942095)
              ·
                refine ⟨149362353073779496771413143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99574902049186331180942095 149362353073779496771413143)
                ·
                  refine ⟨224043529610669245157119715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149362353073779496771413143 224043529610669245157119715)
                  ·
                    refine ⟨336065294416003867735679573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 224043529610669245157119715 336065294416003867735679573)
                    ·
                      refine ⟨3938265168937545325027495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 336065294416003867735679573 3938265168937545325027495)
                      ·
                        rfl

theorem cell23_7669744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_7669744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669744 prefixEnd_7669744 := by exact prefixLift 7669744
  have htrace : WordTrace (prefixWord ++ tailWord_7669744) baseStart_7669744 baseEnd_7669744 := by
    simpa [prefixWord, tailWord_7669744, baseEnd_7669744] using wordTrace_append hprefix tailTrace_7669744
  have hstable : (prefixWord ++ tailWord_7669744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669744).length < 2 ^ (prefixWord ++ tailWord_7669744).sum := by decide
  have hdescent : baseEnd_7669744 < baseStart_7669744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669745 : List Nat := [1, 2, 2, 2, 5, 2, 1, 1, 3, 4]
def baseStart_7669745 : Nat := 118140960795 + 7669745 * 2 ^ 59
def prefixEnd_7669745 : Nat := 4983230072969 + 3 ^ 40 * 7669745 * 2
def baseEnd_7669745 : Nat := 1312755227472733273704997

theorem tailTrace_7669745 : CollatzResearch.WordTrace tailWord_7669745 prefixEnd_7669745 1312755227472733273704997 := by
  unfold tailWord_7669745
  simp only [CollatzResearch.WordTrace]
  refine ⟨279738581598831228005586689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186492387732554152003724459 279738581598831228005586689)
  ·
    refine ⟨209803936199123421004190017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279738581598831228005586689 209803936199123421004190017)
    ·
      refine ⟨157352952149342565753142513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209803936199123421004190017 157352952149342565753142513)
      ·
        refine ⟨118014714112006924314856885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157352952149342565753142513 118014714112006924314856885)
        ·
          refine ⟨11063879448000649154517833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118014714112006924314856885 11063879448000649154517833)
          ·
            refine ⟨8297909586000486865888375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11063879448000649154517833 8297909586000486865888375)
            ·
              refine ⟨12446864379000730298832563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8297909586000486865888375 12446864379000730298832563)
              ·
                refine ⟨18670296568501095448248845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12446864379000730298832563 18670296568501095448248845)
                ·
                  refine ⟨7001361213187910793093317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18670296568501095448248845 7001361213187910793093317)
                  ·
                    refine ⟨1312755227472733273704997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7001361213187910793093317 1312755227472733273704997)
                    ·
                      rfl

theorem cell23_7669745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_7669745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669745 prefixEnd_7669745 := by exact prefixLift 7669745
  have htrace : WordTrace (prefixWord ++ tailWord_7669745) baseStart_7669745 baseEnd_7669745 := by
    simpa [prefixWord, tailWord_7669745, baseEnd_7669745] using wordTrace_append hprefix tailTrace_7669745
  have hstable : (prefixWord ++ tailWord_7669745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669745).length < 2 ^ (prefixWord ++ tailWord_7669745).sum := by decide
  have hdescent : baseEnd_7669745 < baseStart_7669745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669754 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 1, 11]
def baseStart_7669754 : Nat := 118140960795 + 7669754 * 2 ^ 59
def prefixEnd_7669754 : Nat := 4983230072969 + 3 ^ 40 * 7669754 * 2
def baseEnd_7669754 : Nat := 1312756767914696761967483

theorem tailTrace_7669754 : CollatzResearch.WordTrace tailWord_7669754 prefixEnd_7669754 1312756767914696761967483 := by
  unfold tailWord_7669754
  simp only [CollatzResearch.WordTrace]
  refine ⟨69934727463949655635666079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186492606570532415028442877 69934727463949655635666079)
  ·
    refine ⟨104902091195924483453499119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69934727463949655635666079 104902091195924483453499119)
    ·
      refine ⟨157353136793886725180248679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104902091195924483453499119 157353136793886725180248679)
      ·
        refine ⟨236029705190830087770373019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157353136793886725180248679 236029705190830087770373019)
        ·
          refine ⟨354044557786245131655559529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236029705190830087770373019 354044557786245131655559529)
          ·
            refine ⟨265533418339683848741669647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354044557786245131655559529 265533418339683848741669647)
            ·
              refine ⟨398300127509525773112504471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265533418339683848741669647 398300127509525773112504471)
              ·
                refine ⟨597450191264288659668756707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398300127509525773112504471 597450191264288659668756707)
                ·
                  refine ⟨896175286896432989503135061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 597450191264288659668756707 896175286896432989503135061)
                  ·
                    refine ⟨1312756767914696761967483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 896175286896432989503135061 1312756767914696761967483)
                    ·
                      rfl

theorem cell23_7669754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_7669754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669754 prefixEnd_7669754 := by exact prefixLift 7669754
  have htrace : WordTrace (prefixWord ++ tailWord_7669754) baseStart_7669754 baseEnd_7669754 := by
    simpa [prefixWord, tailWord_7669754, baseEnd_7669754] using wordTrace_append hprefix tailTrace_7669754
  have hstable : (prefixWord ++ tailWord_7669754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669754).length < 2 ^ (prefixWord ++ tailWord_7669754).sum := by decide
  have hdescent : baseEnd_7669754 < baseStart_7669754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669768 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 5, 1, 3]
def baseStart_7669768 : Nat := 118140960795 + 7669768 * 2 ^ 59
def prefixEnd_7669768 : Nat := 4983230072969 + 3 ^ 40 * 7669768 * 2
def baseEnd_7669768 : Nat := 3938277492473253231127385

theorem tailTrace_7669768 : CollatzResearch.WordTrace tailWord_7669768 prefixEnd_7669768 3938277492473253231127385 := by
  unfold tailWord_7669768
  simp only [CollatzResearch.WordTrace]
  refine ⟨139869710238873951466836979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186492946985165268622449305 139869710238873951466836979)
  ·
    refine ⟨209804565358310927200255469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139869710238873951466836979 209804565358310927200255469)
    ·
      refine ⟨78676712009366597700095801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209804565358310927200255469 78676712009366597700095801)
      ·
        refine ⟨59007534007024948275071851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78676712009366597700095801 59007534007024948275071851)
        ·
          refine ⟨88511301010537422412607777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59007534007024948275071851 88511301010537422412607777)
          ·
            refine ⟨66383475757903066809455833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88511301010537422412607777 66383475757903066809455833)
            ·
              refine ⟨49787606818427300107091875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66383475757903066809455833 49787606818427300107091875)
              ·
                refine ⟨74681410227640950160637813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49787606818427300107091875 74681410227640950160637813)
                ·
                  refine ⟨7001382208841339077559795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74681410227640950160637813 7001382208841339077559795)
                  ·
                    refine ⟨10502073313262008616339693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7001382208841339077559795 10502073313262008616339693)
                    ·
                      refine ⟨3938277492473253231127385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10502073313262008616339693 3938277492473253231127385)
                      ·
                        rfl

theorem cell23_7669768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_7669768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669768 prefixEnd_7669768 := by exact prefixLift 7669768
  have htrace : WordTrace (prefixWord ++ tailWord_7669768) baseStart_7669768 baseEnd_7669768 := by
    simpa [prefixWord, tailWord_7669768, baseEnd_7669768] using wordTrace_append hprefix tailTrace_7669768
  have hstable : (prefixWord ++ tailWord_7669768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669768).length < 2 ^ (prefixWord ++ tailWord_7669768).sum := by decide
  have hdescent : baseEnd_7669768 < baseStart_7669768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669771 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 3, 5]
def baseStart_7669771 : Nat := 118140960795 + 7669771 * 2 ^ 59
def prefixEnd_7669771 : Nat := 4983230072969 + 3 ^ 40 * 7669771 * 2
def baseEnd_7669771 : Nat := 1312759677638405573129957

theorem tailTrace_7669771 : CollatzResearch.WordTrace tailWord_7669771 prefixEnd_7669771 1312759677638405573129957 := by
  unfold tailWord_7669771
  simp only [CollatzResearch.WordTrace]
  refine ⟨279739529896737034446033167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186493019931158022964022111 279739529896737034446033167)
  ·
    refine ⟨419609294845105551669049751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279739529896737034446033167 419609294845105551669049751)
    ·
      refine ⟨629413942267658327503574627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419609294845105551669049751 629413942267658327503574627)
      ·
        refine ⟨944120913401487491255361941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629413942267658327503574627 944120913401487491255361941)
        ·
          refine ⟨44255667815694726152595091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 944120913401487491255361941 44255667815694726152595091)
          ·
            refine ⟨66383501723542089228892637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44255667815694726152595091 66383501723542089228892637)
            ·
              refine ⟨24893813146328283460834739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66383501723542089228892637 24893813146328283460834739)
              ·
                refine ⟨37340719719492425191252109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24893813146328283460834739 37340719719492425191252109)
                ·
                  refine ⟨14002769894809659446719541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37340719719492425191252109 14002769894809659446719541)
                  ·
                    refine ⟨1312759677638405573129957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14002769894809659446719541 1312759677638405573129957)
                    ·
                      rfl

theorem cell23_7669771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 5].length) (baseStart_7669771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669771 prefixEnd_7669771 := by exact prefixLift 7669771
  have htrace : WordTrace (prefixWord ++ tailWord_7669771) baseStart_7669771 baseEnd_7669771 := by
    simpa [prefixWord, tailWord_7669771, baseEnd_7669771] using wordTrace_append hprefix tailTrace_7669771
  have hstable : (prefixWord ++ tailWord_7669771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669771).length < 2 ^ (prefixWord ++ tailWord_7669771).sum := by decide
  have hdescent : baseEnd_7669771 < baseStart_7669771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669785 : List Nat := [1, 2, 1, 2, 1, 1, 3, 7, 1, 1, 3]
def baseStart_7669785 : Nat := 118140960795 + 7669785 * 2 ^ 59
def prefixEnd_7669785 : Nat := 4983230072969 + 3 ^ 40 * 7669785 * 2
def baseEnd_7669785 : Nat := 3938286221644379664614807

theorem tailTrace_7669785 : CollatzResearch.WordTrace tailWord_7669785 prefixEnd_7669785 3938286221644379664614807 := by
  unfold tailWord_7669785
  simp only [CollatzResearch.WordTrace]
  refine ⟨279740040518686314837042809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186493360345790876558028539 279740040518686314837042809)
  ·
    refine ⟨209805030389014736127782107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279740040518686314837042809 209805030389014736127782107)
    ·
      refine ⟨314707545583522104191673161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209805030389014736127782107 314707545583522104191673161)
      ·
        refine ⟨236030659187641578143754871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314707545583522104191673161 236030659187641578143754871)
        ·
          refine ⟨354045988781462367215632307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236030659187641578143754871 354045988781462367215632307)
          ·
            refine ⟨531068983172193550823448461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354045988781462367215632307 531068983172193550823448461)
            ·
              refine ⟨199150868689572581558793173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 531068983172193550823448461 199150868689572581558793173)
              ·
                refine ⟨4667598484911857380284215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 199150868689572581558793173 4667598484911857380284215)
                ·
                  refine ⟨7001397727367786070426323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4667598484911857380284215 7001397727367786070426323)
                  ·
                    refine ⟨10502096591051679105639485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7001397727367786070426323 10502096591051679105639485)
                    ·
                      refine ⟨3938286221644379664614807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10502096591051679105639485 3938286221644379664614807)
                      ·
                        rfl

theorem cell23_7669785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 1, 1, 3].length) (baseStart_7669785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669785 prefixEnd_7669785 := by exact prefixLift 7669785
  have htrace : WordTrace (prefixWord ++ tailWord_7669785) baseStart_7669785 baseEnd_7669785 := by
    simpa [prefixWord, tailWord_7669785, baseEnd_7669785] using wordTrace_append hprefix tailTrace_7669785
  have hstable : (prefixWord ++ tailWord_7669785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669785).length < 2 ^ (prefixWord ++ tailWord_7669785).sum := by decide
  have hdescent : baseEnd_7669785 < baseStart_7669785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669796 : List Nat := [2, 3, 1, 4, 3, 1, 2, 2, 1, 4]
def baseStart_7669796 : Nat := 118140960795 + 7669796 * 2 ^ 59
def prefixEnd_7669796 : Nat := 4983230072969 + 3 ^ 40 * 7669796 * 2
def baseEnd_7669796 : Nat := 1312763956643859707192419

theorem tailTrace_7669796 : CollatzResearch.WordTrace tailWord_7669796 prefixEnd_7669796 1312763956643859707192419 := by
  unfold tailWord_7669796
  simp only [CollatzResearch.WordTrace]
  refine ⟨139870220860823231857846621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186493627814430975810462161 139870220860823231857846621)
  ·
    refine ⟨52451332822808711946692483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139870220860823231857846621 52451332822808711946692483)
    ·
      refine ⟨78676999234213067920038725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52451332822808711946692483 78676999234213067920038725)
      ·
        refine ⟨14751937356414950235007261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78676999234213067920038725 14751937356414950235007261)
        ·
          refine ⟨5531976508655606338127723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14751937356414950235007261 5531976508655606338127723)
          ·
            refine ⟨8297964762983409507191585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5531976508655606338127723 8297964762983409507191585)
            ·
              refine ⟨6223473572237557130393689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8297964762983409507191585 6223473572237557130393689)
              ·
                refine ⟨4667605179178167847795267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6223473572237557130393689 4667605179178167847795267)
                ·
                  refine ⟨7001407768767251771692901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4667605179178167847795267 7001407768767251771692901)
                  ·
                    refine ⟨1312763956643859707192419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7001407768767251771692901 1312763956643859707192419)
                    ·
                      rfl

theorem cell23_7669796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_7669796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669796 prefixEnd_7669796 := by exact prefixLift 7669796
  have htrace : WordTrace (prefixWord ++ tailWord_7669796) baseStart_7669796 baseEnd_7669796 := by
    simpa [prefixWord, tailWord_7669796, baseEnd_7669796] using wordTrace_append hprefix tailTrace_7669796
  have hstable : (prefixWord ++ tailWord_7669796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669796).length < 2 ^ (prefixWord ++ tailWord_7669796).sum := by decide
  have hdescent : baseEnd_7669796 < baseStart_7669796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669801 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 10, 4]
def baseStart_7669801 : Nat := 118140960795 + 7669801 * 2 ^ 59
def prefixEnd_7669801 : Nat := 4983230072969 + 3 ^ 40 * 7669801 * 2
def baseEnd_7669801 : Nat := 1312764812444950534004911

theorem tailTrace_7669801 : CollatzResearch.WordTrace tailWord_7669801 prefixEnd_7669801 1312764812444950534004911 := by
  unfold tailWord_7669801
  simp only [CollatzResearch.WordTrace]
  refine ⟨279740624086628349569625257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186493749391085566379750171 279740624086628349569625257)
  ·
    refine ⟨209805468064971262177218943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279740624086628349569625257 209805468064971262177218943)
    ·
      refine ⟨314708202097456893265828415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209805468064971262177218943 314708202097456893265828415)
      ·
        refine ⟨472062303146185339898742623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314708202097456893265828415 472062303146185339898742623)
        ·
          refine ⟨708093454719278009848113935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472062303146185339898742623 708093454719278009848113935)
          ·
            refine ⟨1062140182078917014772170903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708093454719278009848113935 1062140182078917014772170903)
            ·
              refine ⟨1593210273118375522158256355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062140182078917014772170903 1593210273118375522158256355)
              ·
                refine ⟨2389815409677563283237384533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1593210273118375522158256355 2389815409677563283237384533)
                ·
                  refine ⟨7001412333039736181359525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 2389815409677563283237384533 7001412333039736181359525)
                  ·
                    refine ⟨1312764812444950534004911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7001412333039736181359525 1312764812444950534004911)
                    ·
                      rfl

theorem cell23_7669801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 4].length) (baseStart_7669801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669801 prefixEnd_7669801 := by exact prefixLift 7669801
  have htrace : WordTrace (prefixWord ++ tailWord_7669801) baseStart_7669801 baseEnd_7669801 := by
    simpa [prefixWord, tailWord_7669801, baseEnd_7669801] using wordTrace_append hprefix tailTrace_7669801
  have hstable : (prefixWord ++ tailWord_7669801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669801).length < 2 ^ (prefixWord ++ tailWord_7669801).sum := by decide
  have hdescent : baseEnd_7669801 < baseStart_7669801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669811 : List Nat := [1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 5]
def baseStart_7669811 : Nat := 118140960795 + 7669811 * 2 ^ 59
def prefixEnd_7669811 : Nat := 4983230072969 + 3 ^ 40 * 7669811 * 2
def baseEnd_7669811 : Nat := 3938299572141396562889687

theorem tailTrace_7669811 : CollatzResearch.WordTrace tailWord_7669811 prefixEnd_7669811 3938299572141396562889687 := by
  unfold tailWord_7669811
  simp only [CollatzResearch.WordTrace]
  refine ⟨279740988816592121277489287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186493992544394747518326191 279740988816592121277489287)
  ·
    refine ⟨419611483224888181916233931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279740988816592121277489287 419611483224888181916233931)
    ·
      refine ⟨629417224837332272874350897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419611483224888181916233931 629417224837332272874350897)
      ·
        refine ⟨472062918627999204655763173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629417224837332272874350897 472062918627999204655763173)
        ·
          refine ⟨88511797242749850872955595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 472062918627999204655763173 88511797242749850872955595)
          ·
            refine ⟨132767695864124776309433393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88511797242749850872955595 132767695864124776309433393)
            ·
              refine ⟨99575771898093582232075045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132767695864124776309433393 99575771898093582232075045)
              ·
                refine ⟨18670457230892546668514071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99575771898093582232075045 18670457230892546668514071)
                ·
                  refine ⟨28005685846338820002771107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18670457230892546668514071 28005685846338820002771107)
                  ·
                    refine ⟨42008528769508230004156661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28005685846338820002771107 42008528769508230004156661)
                    ·
                      refine ⟨3938299572141396562889687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42008528769508230004156661 3938299572141396562889687)
                      ·
                        rfl

theorem cell23_7669811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 5].length) (baseStart_7669811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669811 prefixEnd_7669811 := by exact prefixLift 7669811
  have htrace : WordTrace (prefixWord ++ tailWord_7669811) baseStart_7669811 baseEnd_7669811 := by
    simpa [prefixWord, tailWord_7669811, baseEnd_7669811] using wordTrace_append hprefix tailTrace_7669811
  have hstable : (prefixWord ++ tailWord_7669811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669811).length < 2 ^ (prefixWord ++ tailWord_7669811).sum := by decide
  have hdescent : baseEnd_7669811 < baseStart_7669811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669838 : List Nat := [4, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_7669838 : Nat := 118140960795 + 7669838 * 2 ^ 59
def prefixEnd_7669838 : Nat := 4983230072969 + 3 ^ 40 * 7669838 * 2
def baseEnd_7669838 : Nat := 3938313436119067957252063

theorem tailTrace_7669838 : CollatzResearch.WordTrace tailWord_7669838 prefixEnd_7669838 3938313436119067957252063 := by
  unfold tailWord_7669838
  simp only [CollatzResearch.WordTrace]
  refine ⟨34967746698436788111090271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186494649058329536592481445 34967746698436788111090271)
  ·
    refine ⟨52451620047655182166635407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34967746698436788111090271 52451620047655182166635407)
    ·
      refine ⟨78677430071482773249953111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52451620047655182166635407 78677430071482773249953111)
      ·
        refine ⟨118016145107224159874929667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78677430071482773249953111 118016145107224159874929667)
        ·
          refine ⟨177024217660836239812394501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118016145107224159874929667 177024217660836239812394501)
          ·
            refine ⟨33192040811406794964823969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177024217660836239812394501 33192040811406794964823969)
            ·
              refine ⟨24894030608555096223617977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33192040811406794964823969 24894030608555096223617977)
              ·
                refine ⟨18670522956416322167713483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24894030608555096223617977 18670522956416322167713483)
                ·
                  refine ⟨28005784434624483251570225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18670522956416322167713483 28005784434624483251570225)
                  ·
                    refine ⟨21004338325968362438677669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28005784434624483251570225 21004338325968362438677669)
                    ·
                      refine ⟨3938313436119067957252063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21004338325968362438677669 3938313436119067957252063)
                      ·
                        rfl

theorem cell23_7669838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_7669838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669838 prefixEnd_7669838 := by exact prefixLift 7669838
  have htrace : WordTrace (prefixWord ++ tailWord_7669838) baseStart_7669838 baseEnd_7669838 := by
    simpa [prefixWord, tailWord_7669838, baseEnd_7669838] using wordTrace_append hprefix tailTrace_7669838
  have hstable : (prefixWord ++ tailWord_7669838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669838).length < 2 ^ (prefixWord ++ tailWord_7669838).sum := by decide
  have hdescent : baseEnd_7669838 < baseStart_7669838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669845 : List Nat := [1, 3, 2, 2, 1, 4, 1, 3, 1, 2, 3]
def baseStart_7669845 : Nat := 118140960795 + 7669845 * 2 ^ 59
def prefixEnd_7669845 : Nat := 4983230072969 + 3 ^ 40 * 7669845 * 2
def baseEnd_7669845 : Nat := 3938317030483649429864531

theorem tailTrace_7669845 : CollatzResearch.WordTrace tailWord_7669845 prefixEnd_7669845 3938317030483649429864531 := by
  unfold tailWord_7669845
  simp only [CollatzResearch.WordTrace]
  refine ⟨279742228898468945084226989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186494819265645963389484659 279742228898468945084226989)
  ·
    refine ⟨104903335836925854406585121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279742228898468945084226989 104903335836925854406585121)
    ·
      refine ⟨78677501877694390804938841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104903335836925854406585121 78677501877694390804938841)
      ·
        refine ⟨59008126408270793103704131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78677501877694390804938841 59008126408270793103704131)
        ·
          refine ⟨88512189612406189655556197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59008126408270793103704131 88512189612406189655556197)
          ·
            refine ⟨16596035552326160560416787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88512189612406189655556197 16596035552326160560416787)
            ·
              refine ⟨24894053328489240840625181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16596035552326160560416787 24894053328489240840625181)
              ·
                refine ⟨9335269998183465315234443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24894053328489240840625181 9335269998183465315234443)
                ·
                  refine ⟨14002904997275197972851665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9335269998183465315234443 14002904997275197972851665)
                  ·
                    refine ⟨10502178747956398479638749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14002904997275197972851665 10502178747956398479638749)
                    ·
                      refine ⟨3938317030483649429864531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10502178747956398479638749 3938317030483649429864531)
                      ·
                        rfl

theorem cell23_7669845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_7669845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669845 prefixEnd_7669845 := by exact prefixLift 7669845
  have htrace : WordTrace (prefixWord ++ tailWord_7669845) baseStart_7669845 baseEnd_7669845 := by
    simpa [prefixWord, tailWord_7669845, baseEnd_7669845] using wordTrace_append hprefix tailTrace_7669845
  have hstable : (prefixWord ++ tailWord_7669845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669845).length < 2 ^ (prefixWord ++ tailWord_7669845).sum := by decide
  have hdescent : baseEnd_7669845 < baseStart_7669845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669852 : List Nat := [2, 2, 4, 1, 1, 4, 1, 2, 2, 4]
def baseStart_7669852 : Nat := 118140960795 + 7669852 * 2 ^ 59
def prefixEnd_7669852 : Nat := 4983230072969 + 3 ^ 40 * 7669852 * 2
def baseEnd_7669852 : Nat := 1312773541616076967492333

theorem tailTrace_7669852 : CollatzResearch.WordTrace tailWord_7669852 prefixEnd_7669852 1312773541616076967492333 := by
  unfold tailWord_7669852
  simp only [CollatzResearch.WordTrace]
  refine ⟨139871242104721792639865905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186494989472962390186487873 139871242104721792639865905)
  ·
    refine ⟨104903431578541344479899429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139871242104721792639865905 104903431578541344479899429)
    ·
      refine ⟨19669393420976502089981143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104903431578541344479899429 19669393420976502089981143)
      ·
        refine ⟨29504090131464753134971715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19669393420976502089981143 29504090131464753134971715)
        ·
          refine ⟨44256135197197129702457573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29504090131464753134971715 44256135197197129702457573)
          ·
            refine ⟨8298025349474461819210795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44256135197197129702457573 8298025349474461819210795)
            ·
              refine ⟨12447038024211692728816193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8298025349474461819210795 12447038024211692728816193)
              ·
                refine ⟨9335278518158769546612145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12447038024211692728816193 9335278518158769546612145)
                ·
                  refine ⟨7001458888619077159959109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9335278518158769546612145 7001458888619077159959109)
                  ·
                    refine ⟨1312773541616076967492333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7001458888619077159959109 1312773541616076967492333)
                    ·
                      rfl

theorem cell23_7669852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_7669852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669852 prefixEnd_7669852 := by exact prefixLift 7669852
  have htrace : WordTrace (prefixWord ++ tailWord_7669852) baseStart_7669852 baseEnd_7669852 := by
    simpa [prefixWord, tailWord_7669852, baseEnd_7669852] using wordTrace_append hprefix tailTrace_7669852
  have hstable : (prefixWord ++ tailWord_7669852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669852).length < 2 ^ (prefixWord ++ tailWord_7669852).sum := by decide
  have hdescent : baseEnd_7669852 < baseStart_7669852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669915 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 4, 2, 2]
def baseStart_7669915 : Nat := 118140960795 + 7669915 * 2 ^ 59
def prefixEnd_7669915 : Nat := 4983230072969 + 3 ^ 40 * 7669915 * 2
def baseEnd_7669915 : Nat := 3938352974129464155989209

theorem tailTrace_7669915 : CollatzResearch.WordTrace tailWord_7669915 prefixEnd_7669915 3938352974129464155989209 := by
  unfold tailWord_7669915
  simp only [CollatzResearch.WordTrace]
  refine ⟨279744782008215347039275199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186496521338810231359516799 279744782008215347039275199)
  ·
    refine ⟨419617173012323020558912799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279744782008215347039275199 419617173012323020558912799)
    ·
      refine ⟨629425759518484530838369199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419617173012323020558912799 629425759518484530838369199)
      ·
        refine ⟨944138639277726796257553799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629425759518484530838369199 944138639277726796257553799)
        ·
          refine ⟨1416207958916590194386330699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944138639277726796257553799 1416207958916590194386330699)
          ·
            refine ⟨2124311938374885291579496049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416207958916590194386330699 2124311938374885291579496049)
            ·
              refine ⟨1593233953781163968684622037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2124311938374885291579496049 1593233953781163968684622037)
              ·
                refine ⟨37341420791746030516045829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1593233953781163968684622037 37341420791746030516045829)
                ·
                  refine ⟨7001516398452380721758593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37341420791746030516045829 7001516398452380721758593)
                  ·
                    refine ⟨5251137298839285541318945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7001516398452380721758593 5251137298839285541318945)
                    ·
                      refine ⟨3938352974129464155989209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5251137298839285541318945 3938352974129464155989209)
                      ·
                        rfl

theorem cell23_7669915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 2, 2].length) (baseStart_7669915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669915 prefixEnd_7669915 := by exact prefixLift 7669915
  have htrace : WordTrace (prefixWord ++ tailWord_7669915) baseStart_7669915 baseEnd_7669915 := by
    simpa [prefixWord, tailWord_7669915, baseEnd_7669915] using wordTrace_append hprefix tailTrace_7669915
  have hstable : (prefixWord ++ tailWord_7669915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669915).length < 2 ^ (prefixWord ++ tailWord_7669915).sum := by decide
  have hdescent : baseEnd_7669915 < baseStart_7669915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669971 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 8]
def baseStart_7669971 : Nat := 118140960795 + 7669971 * 2 ^ 59
def prefixEnd_7669971 : Nat := 4983230072969 + 3 ^ 40 * 7669971 * 2
def baseEnd_7669971 : Nat := 3938381729046115936888951

theorem tailTrace_7669971 : CollatzResearch.WordTrace tailWord_7669971 prefixEnd_7669971 3938381729046115936888951 := by
  unfold tailWord_7669971
  simp only [CollatzResearch.WordTrace]
  refine ⟨279746824496012468603313767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186497882997341645735542511 279746824496012468603313767)
  ·
    refine ⟨419620236744018702904970651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279746824496012468603313767 419620236744018702904970651)
    ·
      refine ⟨629430355116028054357455977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419620236744018702904970651 629430355116028054357455977)
      ·
        refine ⟨472072766337021040768091983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629430355116028054357455977 472072766337021040768091983)
        ·
          refine ⟨708109149505531561152137975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472072766337021040768091983 708109149505531561152137975)
          ·
            refine ⟨1062163724258297341728206963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708109149505531561152137975 1062163724258297341728206963)
            ·
              refine ⟨1593245586387446012592310445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062163724258297341728206963 1593245586387446012592310445)
              ·
                refine ⟨597467094895292254722116417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1593245586387446012592310445 597467094895292254722116417)
                ·
                  refine ⟨448100321171469191041587313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597467094895292254722116417 448100321171469191041587313)
                  ·
                    refine ⟨336075240878601893281190485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 448100321171469191041587313 336075240878601893281190485)
                    ·
                      refine ⟨3938381729046115936888951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 336075240878601893281190485 3938381729046115936888951)
                      ·
                        rfl

theorem cell23_7669971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_7669971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669971 prefixEnd_7669971 := by exact prefixLift 7669971
  have htrace : WordTrace (prefixWord ++ tailWord_7669971) baseStart_7669971 baseEnd_7669971 := by
    simpa [prefixWord, tailWord_7669971, baseEnd_7669971] using wordTrace_append hprefix tailTrace_7669971
  have hstable : (prefixWord ++ tailWord_7669971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669971).length < 2 ^ (prefixWord ++ tailWord_7669971).sum := by decide
  have hdescent : baseEnd_7669971 < baseStart_7669971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669978 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5]
def baseStart_7669978 : Nat := 118140960795 + 7669978 * 2 ^ 59
def prefixEnd_7669978 : Nat := 4983230072969 + 3 ^ 40 * 7669978 * 2
def baseEnd_7669978 : Nat := 3938385323410697409501419

theorem tailTrace_7669978 : CollatzResearch.WordTrace tailWord_7669978 prefixEnd_7669978 3938385323410697409501419 := by
  unfold tailWord_7669978
  simp only [CollatzResearch.WordTrace]
  refine ⟨69936769951746777199704647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186498053204658072532545725 69936769951746777199704647)
  ·
    refine ⟨104905154927620165799556971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69936769951746777199704647 104905154927620165799556971)
    ·
      refine ⟨157357732391430248699335457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104905154927620165799556971 157357732391430248699335457)
      ·
        refine ⟨118018299293572686524501593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157357732391430248699335457 118018299293572686524501593)
        ·
          refine ⟨88513724470179514893376195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118018299293572686524501593 88513724470179514893376195)
          ·
            refine ⟨132770586705269272340064293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88513724470179514893376195 132770586705269272340064293)
            ·
              refine ⟨24894485007237988563762055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132770586705269272340064293 24894485007237988563762055)
              ·
                refine ⟨37341727510856982845643083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24894485007237988563762055 37341727510856982845643083)
                ·
                  refine ⟨56012591266285474268464625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37341727510856982845643083 56012591266285474268464625)
                  ·
                    refine ⟨42009443449714105701348469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56012591266285474268464625 42009443449714105701348469)
                    ·
                      refine ⟨3938385323410697409501419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42009443449714105701348469 3938385323410697409501419)
                      ·
                        rfl

theorem cell23_7669978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_7669978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669978 prefixEnd_7669978 := by exact prefixLift 7669978
  have htrace : WordTrace (prefixWord ++ tailWord_7669978) baseStart_7669978 baseEnd_7669978 := by
    simpa [prefixWord, tailWord_7669978, baseEnd_7669978] using wordTrace_append hprefix tailTrace_7669978
  have hstable : (prefixWord ++ tailWord_7669978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669978).length < 2 ^ (prefixWord ++ tailWord_7669978).sum := by decide
  have hdescent : baseEnd_7669978 < baseStart_7669978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7669988 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_7669988 : Nat := 118140960795 + 7669988 * 2 ^ 59
def prefixEnd_7669988 : Nat := 4983230072969 + 3 ^ 40 * 7669988 * 2
def baseEnd_7669988 : Nat := 3938390458217242370376373

theorem tailTrace_7669988 : CollatzResearch.WordTrace tailWord_7669988 prefixEnd_7669988 3938390458217242370376373 := by
  unfold tailWord_7669988
  simp only [CollatzResearch.WordTrace]
  refine ⟨139873722268475440253341309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186498296357967253671121745 139873722268475440253341309)
  ·
    refine ⟨52452645850678290095002991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139873722268475440253341309 52452645850678290095002991)
    ·
      refine ⟨78678968776017435142504487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52452645850678290095002991 78678968776017435142504487)
      ·
        refine ⟨118018453164026152713756731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78678968776017435142504487 118018453164026152713756731)
        ·
          refine ⟨177027679746039229070635097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118018453164026152713756731 177027679746039229070635097)
          ·
            refine ⟨132770759809529421802976323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177027679746039229070635097 132770759809529421802976323)
            ·
              refine ⟨199156139714294132704464485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132770759809529421802976323 199156139714294132704464485)
              ·
                refine ⟨37341776196430149882087091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199156139714294132704464485 37341776196430149882087091)
                ·
                  refine ⟨56012664294645224823130637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37341776196430149882087091 56012664294645224823130637)
                  ·
                    refine ⟨21004749110491959308673989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56012664294645224823130637 21004749110491959308673989)
                    ·
                      refine ⟨3938390458217242370376373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21004749110491959308673989 3938390458217242370376373)
                      ·
                        rfl

theorem cell23_7669988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_7669988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7669988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7669988 prefixEnd_7669988 := by exact prefixLift 7669988
  have htrace : WordTrace (prefixWord ++ tailWord_7669988) baseStart_7669988 baseEnd_7669988 := by
    simpa [prefixWord, tailWord_7669988, baseEnd_7669988] using wordTrace_append hprefix tailTrace_7669988
  have hstable : (prefixWord ++ tailWord_7669988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7669988).length < 2 ^ (prefixWord ++ tailWord_7669988).sum := by decide
  have hdescent : baseEnd_7669988 < baseStart_7669988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7669988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670002 : List Nat := [3, 2, 1, 3, 2, 3, 1, 1, 2, 5]
def baseStart_7670002 : Nat := 118140960795 + 7670002 * 2 ^ 59
def prefixEnd_7670002 : Nat := 4983230072969 + 3 ^ 40 * 7670002 * 2
def baseEnd_7670002 : Nat := 1312799215648801771867103

theorem tailTrace_7670002 : CollatzResearch.WordTrace tailWord_7670002 prefixEnd_7670002 1312799215648801771867103 := by
  unfold tailWord_7670002
  simp only [CollatzResearch.WordTrace]
  refine ⟨69936988789725040224423065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186498636772600107265128173 69936988789725040224423065)
  ·
    refine ⟨52452741592293780168317299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69936988789725040224423065 52452741592293780168317299)
    ·
      refine ⟨78679112388440670252475949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52452741592293780168317299 78679112388440670252475949)
      ·
        refine ⟨29504667145665251344678481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78679112388440670252475949 29504667145665251344678481)
        ·
          refine ⟨22128500359248938508508861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29504667145665251344678481 22128500359248938508508861)
          ·
            refine ⟨8298187634718351940690823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22128500359248938508508861 8298187634718351940690823)
            ·
              refine ⟨12447281452077527911036235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8298187634718351940690823 12447281452077527911036235)
              ·
                refine ⟨18670922178116291866554353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12447281452077527911036235 18670922178116291866554353)
                ·
                  refine ⟨14003191633587218899915765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18670922178116291866554353 14003191633587218899915765)
                  ·
                    refine ⟨1312799215648801771867103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14003191633587218899915765 1312799215648801771867103)
                    ·
                      rfl

theorem cell23_7670002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_7670002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670002 prefixEnd_7670002 := by exact prefixLift 7670002
  have htrace : WordTrace (prefixWord ++ tailWord_7670002) baseStart_7670002 baseEnd_7670002 := by
    simpa [prefixWord, tailWord_7670002, baseEnd_7670002] using wordTrace_append hprefix tailTrace_7670002
  have hstable : (prefixWord ++ tailWord_7670002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670002).length < 2 ^ (prefixWord ++ tailWord_7670002).sum := by decide
  have hdescent : baseEnd_7670002 < baseStart_7670002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670028 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 8]
def baseStart_7670028 : Nat := 118140960795 + 7670028 * 2 ^ 59
def prefixEnd_7670028 : Nat := 4983230072969 + 3 ^ 40 * 7670028 * 2
def baseEnd_7670028 : Nat := 437601221938158023764021

theorem tailTrace_7670028 : CollatzResearch.WordTrace tailWord_7670028 prefixEnd_7670028 437601221938158023764021 := by
  unfold tailWord_7670028
  simp only [CollatzResearch.WordTrace]
  refine ⟨139874451728402983669069369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186499268971203978225425825 139874451728402983669069369)
  ·
    refine ⟨104905838796302237751802027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139874451728402983669069369 104905838796302237751802027)
    ·
      refine ⟨157358758194453356627703041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104905838796302237751802027 157358758194453356627703041)
      ·
        refine ⟨118019068645840017470777281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157358758194453356627703041 118019068645840017470777281)
        ·
          refine ⟨88514301484380013103082961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118019068645840017470777281 88514301484380013103082961)
          ·
            refine ⟨66385726113285009827312221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88514301484380013103082961 66385726113285009827312221)
            ·
              refine ⟨24894647292481878685242083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66385726113285009827312221 24894647292481878685242083)
              ·
                refine ⟨37341970938722818027863125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24894647292481878685242083 37341970938722818027863125)
                ·
                  refine ⟨437601221938158023764021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37341970938722818027863125 437601221938158023764021)
                  ·
                    rfl

theorem cell23_7670028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 8].length) (baseStart_7670028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670028 prefixEnd_7670028 := by exact prefixLift 7670028
  have htrace : WordTrace (prefixWord ++ tailWord_7670028) baseStart_7670028 baseEnd_7670028 := by
    simpa [prefixWord, tailWord_7670028, baseEnd_7670028] using wordTrace_append hprefix tailTrace_7670028
  have hstable : (prefixWord ++ tailWord_7670028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670028).length < 2 ^ (prefixWord ++ tailWord_7670028).sum := by decide
  have hdescent : baseEnd_7670028 < baseStart_7670028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
