import V185TrunkScan23Chunk0261

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1550308 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 3, 6]
def baseStart_1550308 : Nat := 118140960795 + 1550308 * 2 ^ 59
def prefixEnd_1550308 : Nat := 4983230072969 + 3 ^ 40 * 1550308 * 2
def baseEnd_1550308 : Nat := 265351055503541882173423

theorem tailTrace_1550308 : CollatzResearch.WordTrace tailWord_1550308 prefixEnd_1550308 265351055503541882173423 := by
  unfold tailWord_1550308
  simp only [CollatzResearch.WordTrace]
  refine ⟨28272189033753181185985789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37696252045004241581314385 28272189033753181185985789)
  ·
    refine ⟨10602070887657442944744671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28272189033753181185985789 10602070887657442944744671)
    ·
      refine ⟨15903106331486164417117007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10602070887657442944744671 15903106331486164417117007)
      ·
        refine ⟨23854659497229246625675511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15903106331486164417117007 23854659497229246625675511)
        ·
          refine ⟨35781989245843869938513267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23854659497229246625675511 35781989245843869938513267)
          ·
            refine ⟨53672983868765804907769901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35781989245843869938513267 53672983868765804907769901)
            ·
              refine ⟨20127368950787176840413713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53672983868765804907769901 20127368950787176840413713)
              ·
                refine ⟨15095526713090382630310285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20127368950787176840413713 15095526713090382630310285)
                ·
                  refine ⟨5660822517408893486366357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15095526713090382630310285 5660822517408893486366357)
                  ·
                    refine ⟨265351055503541882173423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5660822517408893486366357 265351055503541882173423)
                    ·
                      rfl

theorem cell23_1550308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_1550308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550308 prefixEnd_1550308 := by exact prefixLift 1550308
  have htrace : WordTrace (prefixWord ++ tailWord_1550308) baseStart_1550308 baseEnd_1550308 := by
    simpa [prefixWord, tailWord_1550308, baseEnd_1550308] using wordTrace_append hprefix tailTrace_1550308
  have hstable : (prefixWord ++ tailWord_1550308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550308).length < 2 ^ (prefixWord ++ tailWord_1550308).sum := by decide
  have hdescent : baseEnd_1550308 < baseStart_1550308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550328 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 1, 1, 6]
def baseStart_1550328 : Nat := 118140960795 + 1550328 * 2 ^ 59
def prefixEnd_1550328 : Nat := 4983230072969 + 3 ^ 40 * 1550328 * 2
def baseEnd_1550328 : Nat := 796063436123715568270177

theorem tailTrace_1550328 : CollatzResearch.WordTrace tailWord_1550328 prefixEnd_1550328 796063436123715568270177 := by
  unfold tailWord_1550328
  simp only [CollatzResearch.WordTrace]
  refine ⟨28272553763716952893849819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37696738351622603858466425 28272553763716952893849819)
  ·
    refine ⟨42408830645575429340774729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28272553763716952893849819 42408830645575429340774729)
    ·
      refine ⟨31806622984181572005581047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42408830645575429340774729 31806622984181572005581047)
      ·
        refine ⟨47709934476272358008371571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31806622984181572005581047 47709934476272358008371571)
        ·
          refine ⟨71564901714408537012557357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47709934476272358008371571 71564901714408537012557357)
          ·
            refine ⟨26836838142903201379709009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71564901714408537012557357 26836838142903201379709009)
            ·
              refine ⟨20127628607177401034781757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26836838142903201379709009 20127628607177401034781757)
              ·
                refine ⟨7547860727691525388043159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20127628607177401034781757 7547860727691525388043159)
                ·
                  refine ⟨11321791091537288082064739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7547860727691525388043159 11321791091537288082064739)
                  ·
                    refine ⟨16982686637305932123097109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11321791091537288082064739 16982686637305932123097109)
                    ·
                      refine ⟨796063436123715568270177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16982686637305932123097109 796063436123715568270177)
                      ·
                        rfl

theorem cell23_1550328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_1550328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550328 prefixEnd_1550328 := by exact prefixLift 1550328
  have htrace : WordTrace (prefixWord ++ tailWord_1550328) baseStart_1550328 baseEnd_1550328 := by
    simpa [prefixWord, tailWord_1550328, baseEnd_1550328] using wordTrace_append hprefix tailTrace_1550328
  have hstable : (prefixWord ++ tailWord_1550328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550328).length < 2 ^ (prefixWord ++ tailWord_1550328).sum := by decide
  have hdescent : baseEnd_1550328 < baseStart_1550328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550346 : List Nat := [3, 1, 2, 2, 5, 1, 2, 1, 1, 5]
def baseStart_1550346 : Nat := 118140960795 + 1550346 * 2 ^ 59
def prefixEnd_1550346 : Nat := 4983230072969 + 3 ^ 40 * 1550346 * 2
def baseEnd_1550346 : Nat := 265357559591832165948365

theorem tailTrace_1550346 : CollatzResearch.WordTrace tailWord_1550346 prefixEnd_1550346 265357559591832165948365 := by
  unfold tailWord_1550346
  simp only [CollatzResearch.WordTrace]
  refine ⟨14136441010342173715463723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37697176027579129907903261 14136441010342173715463723)
  ·
    refine ⟨21204661515513260573195585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14136441010342173715463723 21204661515513260573195585)
    ·
      refine ⟨15903496136634945429896689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21204661515513260573195585 15903496136634945429896689)
      ·
        refine ⟨11927622102476209072422517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15903496136634945429896689 11927622102476209072422517)
        ·
          refine ⟨1118214572107144600539611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11927622102476209072422517 1118214572107144600539611)
          ·
            refine ⟨1677321858160716900809417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118214572107144600539611 1677321858160716900809417)
            ·
              refine ⟨1257991393620537675607063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1677321858160716900809417 1257991393620537675607063)
              ·
                refine ⟨1886987090430806513410595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1257991393620537675607063 1886987090430806513410595)
                ·
                  refine ⟨2830480635646209770115893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1886987090430806513410595 2830480635646209770115893)
                  ·
                    refine ⟨265357559591832165948365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2830480635646209770115893 265357559591832165948365)
                    ·
                      rfl

theorem cell23_1550346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_1550346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550346 prefixEnd_1550346 := by exact prefixLift 1550346
  have htrace : WordTrace (prefixWord ++ tailWord_1550346) baseStart_1550346 baseEnd_1550346 := by
    simpa [prefixWord, tailWord_1550346, baseEnd_1550346] using wordTrace_append hprefix tailTrace_1550346
  have hstable : (prefixWord ++ tailWord_1550346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550346).length < 2 ^ (prefixWord ++ tailWord_1550346).sum := by decide
  have hdescent : baseEnd_1550346 < baseStart_1550346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550376 : List Nat := [2, 1, 5, 3, 2, 1, 1, 1, 1, 6]
def baseStart_1550376 : Nat := 118140960795 + 1550376 * 2 ^ 59
def prefixEnd_1550376 : Nat := 4983230072969 + 3 ^ 40 * 1550376 * 2
def baseEnd_1550376 : Nat := 265362694398377126823319

theorem tailTrace_1550376 : CollatzResearch.WordTrace tailWord_1550376 prefixEnd_1550376 265362694398377126823319 := by
  unfold tailWord_1550376
  simp only [CollatzResearch.WordTrace]
  refine ⟨28273429115630004992723491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37697905487506673323631321 28273429115630004992723491)
  ·
    refine ⟨42410143673445007489085237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28273429115630004992723491 42410143673445007489085237)
    ·
      refine ⟨3975950969385469452101741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42410143673445007489085237 3975950969385469452101741)
      ·
        refine ⟨1490981613519551044538153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3975950969385469452101741 1490981613519551044538153)
        ·
          refine ⟨1118236210139663283403615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1490981613519551044538153 1118236210139663283403615)
          ·
            refine ⟨1677354315209494925105423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118236210139663283403615 1677354315209494925105423)
            ·
              refine ⟨2516031472814242387658135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1677354315209494925105423 2516031472814242387658135)
              ·
                refine ⟨3774047209221363581487203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2516031472814242387658135 3774047209221363581487203)
                ·
                  refine ⟨5661070813832045372230805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3774047209221363581487203 5661070813832045372230805)
                  ·
                    refine ⟨265362694398377126823319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5661070813832045372230805 265362694398377126823319)
                    ·
                      rfl

theorem cell23_1550376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_1550376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550376 prefixEnd_1550376 := by exact prefixLift 1550376
  have htrace : WordTrace (prefixWord ++ tailWord_1550376) baseStart_1550376 baseEnd_1550376 := by
    simpa [prefixWord, tailWord_1550376, baseEnd_1550376] using wordTrace_append hprefix tailTrace_1550376
  have hstable : (prefixWord ++ tailWord_1550376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550376).length < 2 ^ (prefixWord ++ tailWord_1550376).sum := by decide
  have hdescent : baseEnd_1550376 < baseStart_1550376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550425 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 2, 4, 3]
def baseStart_1550425 : Nat := 118140960795 + 1550425 * 2 ^ 59
def prefixEnd_1550425 : Nat := 4983230072969 + 3 ^ 40 * 1550425 * 2
def baseEnd_1550425 : Nat := 796113243747201688757231

theorem tailTrace_1550425 : CollatzResearch.WordTrace tailWord_1550425 prefixEnd_1550425 796113243747201688757231 := by
  unfold tailWord_1550425
  simp only [CollatzResearch.WordTrace]
  refine ⟨56548645408082491353980729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37699096938721660902653819 56548645408082491353980729)
  ·
    refine ⟨42411484056061868515485547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56548645408082491353980729 42411484056061868515485547)
    ·
      refine ⟨63617226084092802773228321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42411484056061868515485547 63617226084092802773228321)
      ·
        refine ⟨47712919563069602079921241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63617226084092802773228321 47712919563069602079921241)
        ·
          refine ⟨35784689672302201559940931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47712919563069602079921241 35784689672302201559940931)
          ·
            refine ⟨53677034508453302339911397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35784689672302201559940931 53677034508453302339911397)
            ·
              refine ⟨10064443970334994188733387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53677034508453302339911397 10064443970334994188733387)
              ·
                refine ⟨15096665955502491283100081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10064443970334994188733387 15096665955502491283100081)
                ·
                  refine ⟨11322499466626868462325061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15096665955502491283100081 11322499466626868462325061)
                  ·
                    refine ⟨2122968649992537836685949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11322499466626868462325061 2122968649992537836685949)
                    ·
                      refine ⟨796113243747201688757231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2122968649992537836685949 796113243747201688757231)
                      ·
                        rfl

theorem cell23_1550425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_1550425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550425 prefixEnd_1550425 := by exact prefixLift 1550425
  have htrace : WordTrace (prefixWord ++ tailWord_1550425) baseStart_1550425 baseEnd_1550425 := by
    simpa [prefixWord, tailWord_1550425, baseEnd_1550425] using wordTrace_append hprefix tailTrace_1550425
  have hstable : (prefixWord ++ tailWord_1550425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550425).length < 2 ^ (prefixWord ++ tailWord_1550425).sum := by decide
  have hdescent : baseEnd_1550425 < baseStart_1550425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550435 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 4]
def baseStart_1550435 : Nat := 118140960795 + 1550435 * 2 ^ 59
def prefixEnd_1550435 : Nat := 4983230072969 + 3 ^ 40 * 1550435 * 2
def baseEnd_1550435 : Nat := 796118378553746649632185

theorem tailTrace_1550435 : CollatzResearch.WordTrace tailWord_1550435 prefixEnd_1550435 796118378553746649632185 := by
  unfold tailWord_1550435
  simp only [CollatzResearch.WordTrace]
  refine ⟨56549010138046263061844759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37699340092030842041229839 56549010138046263061844759)
  ·
    refine ⟨84823515207069394592767139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56549010138046263061844759 84823515207069394592767139)
    ·
      refine ⟨127235272810604091889150709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84823515207069394592767139 127235272810604091889150709)
      ·
        refine ⟨11928306825994133614607879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127235272810604091889150709 11928306825994133614607879)
        ·
          refine ⟨17892460238991200421911819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11928306825994133614607879 17892460238991200421911819)
          ·
            refine ⟨26838690358486800632867729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17892460238991200421911819 26838690358486800632867729)
            ·
              refine ⟨20129017768865100474650797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26838690358486800632867729 20129017768865100474650797)
              ·
                refine ⟨7548381663324412677994049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20129017768865100474650797 7548381663324412677994049)
                ·
                  refine ⟨5661286247493309508495537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7548381663324412677994049 5661286247493309508495537)
                  ·
                    refine ⟨4245964685619982131371653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5661286247493309508495537 4245964685619982131371653)
                    ·
                      refine ⟨796118378553746649632185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4245964685619982131371653 796118378553746649632185)
                      ·
                        rfl

theorem cell23_1550435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_1550435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550435 prefixEnd_1550435 := by exact prefixLift 1550435
  have htrace : WordTrace (prefixWord ++ tailWord_1550435) baseStart_1550435 baseEnd_1550435 := by
    simpa [prefixWord, tailWord_1550435, baseEnd_1550435] using wordTrace_append hprefix tailTrace_1550435
  have hstable : (prefixWord ++ tailWord_1550435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550435).length < 2 ^ (prefixWord ++ tailWord_1550435).sum := by decide
  have hdescent : baseEnd_1550435 < baseStart_1550435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550445 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 9]
def baseStart_1550445 : Nat := 118140960795 + 1550445 * 2 ^ 59
def prefixEnd_1550445 : Nat := 4983230072969 + 3 ^ 40 * 1550445 * 2
def baseEnd_1550445 : Nat := 88458168151143512278571

theorem tailTrace_1550445 : CollatzResearch.WordTrace tailWord_1550445 prefixEnd_1550445 88458168151143512278571 := by
  unfold tailWord_1550445
  simp only [CollatzResearch.WordTrace]
  refine ⟨56549374868010034769708789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37699583245340023179805859 56549374868010034769708789)
  ·
    refine ⟨5301503893875940759660199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56549374868010034769708789 5301503893875940759660199)
    ·
      refine ⟨7952255840813911139490299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5301503893875940759660199 7952255840813911139490299)
      ·
        refine ⟨11928383761220866709235449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7952255840813911139490299 11928383761220866709235449)
        ·
          refine ⟨8946287820915650031926587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11928383761220866709235449 8946287820915650031926587)
          ·
            refine ⟨13419431731373475047889881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8946287820915650031926587 13419431731373475047889881)
            ·
              refine ⟨10064573798530106285917411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13419431731373475047889881 10064573798530106285917411)
              ·
                refine ⟨15096860697795159428876117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10064573798530106285917411 15096860697795159428876117)
                ·
                  refine ⟨88458168151143512278571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15096860697795159428876117 88458168151143512278571)
                  ·
                    rfl

theorem cell23_1550445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_1550445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550445 prefixEnd_1550445 := by exact prefixLift 1550445
  have htrace : WordTrace (prefixWord ++ tailWord_1550445) baseStart_1550445 baseEnd_1550445 := by
    simpa [prefixWord, tailWord_1550445, baseEnd_1550445] using wordTrace_append hprefix tailTrace_1550445
  have hstable : (prefixWord ++ tailWord_1550445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550445).length < 2 ^ (prefixWord ++ tailWord_1550445).sum := by decide
  have hdescent : baseEnd_1550445 < baseStart_1550445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550485 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_1550485 : Nat := 118140960795 + 1550485 * 2 ^ 59
def prefixEnd_1550485 : Nat := 4983230072969 + 3 ^ 40 * 1550485 * 2
def baseEnd_1550485 : Nat := 796144052586471454006955

theorem tailTrace_1550485 : CollatzResearch.WordTrace tailWord_1550485 prefixEnd_1550485 796144052586471454006955 := by
  unfold tailWord_1550485
  simp only [CollatzResearch.WordTrace]
  refine ⟨56550833787865121601164909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37700555858576747734109939 56550833787865121601164909)
  ·
    refine ⟨21206562670449420600436841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56550833787865121601164909 21206562670449420600436841)
    ·
      refine ⟨15904922002837065450327631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21206562670449420600436841 15904922002837065450327631)
      ·
        refine ⟨23857383004255598175491447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15904922002837065450327631 23857383004255598175491447)
        ·
          refine ⟨35786074506383397263237171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23857383004255598175491447 35786074506383397263237171)
          ·
            refine ⟨53679111759575095894855757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35786074506383397263237171 53679111759575095894855757)
            ·
              refine ⟨20129666909840660960570909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53679111759575095894855757 20129666909840660960570909)
              ·
                refine ⟨7548625091190247860214091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20129666909840660960570909 7548625091190247860214091)
                ·
                  refine ⟨11322937636785371790321137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7548625091190247860214091 11322937636785371790321137)
                  ·
                    refine ⟨8492203227589028842740853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11322937636785371790321137 8492203227589028842740853)
                    ·
                      refine ⟨796144052586471454006955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8492203227589028842740853 796144052586471454006955)
                      ·
                        rfl

theorem cell23_1550485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_1550485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550485 prefixEnd_1550485 := by exact prefixLift 1550485
  have htrace : WordTrace (prefixWord ++ tailWord_1550485) baseStart_1550485 baseEnd_1550485 := by
    simpa [prefixWord, tailWord_1550485, baseEnd_1550485] using wordTrace_append hprefix tailTrace_1550485
  have hstable : (prefixWord ++ tailWord_1550485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550485).length < 2 ^ (prefixWord ++ tailWord_1550485).sum := by decide
  have hdescent : baseEnd_1550485 < baseStart_1550485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550509 : List Nat := [1, 5, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_1550509 : Nat := 118140960795 + 1550509 * 2 ^ 59
def prefixEnd_1550509 : Nat := 4983230072969 + 3 ^ 40 * 1550509 * 2
def baseEnd_1550509 : Nat := 265385458707393120035615

theorem tailTrace_1550509 : CollatzResearch.WordTrace tailWord_1550509 prefixEnd_1550509 265385458707393120035615 := by
  unfold tailWord_1550509
  simp only [CollatzResearch.WordTrace]
  refine ⟨56551709139778173700038581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37701139426518782466692387 56551709139778173700038581)
  ·
    refine ⟨5301722731854203784378617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56551709139778173700038581 5301722731854203784378617)
    ·
      refine ⟨3976292048890652838283963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5301722731854203784378617 3976292048890652838283963)
      ·
        refine ⟨5964438073335979257425945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3976292048890652838283963 5964438073335979257425945)
        ·
          refine ⟨4473328555001984443069459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5964438073335979257425945 4473328555001984443069459)
          ·
            refine ⟨6709992832502976664604189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4473328555001984443069459 6709992832502976664604189)
            ·
              refine ⟨2516247312188616249226571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6709992832502976664604189 2516247312188616249226571)
              ·
                refine ⟨3774370968282924373839857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2516247312188616249226571 3774370968282924373839857)
                ·
                  refine ⟨2830778226212193280379893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3774370968282924373839857 2830778226212193280379893)
                  ·
                    refine ⟨265385458707393120035615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2830778226212193280379893 265385458707393120035615)
                    ·
                      rfl

theorem cell23_1550509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_1550509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550509 prefixEnd_1550509 := by exact prefixLift 1550509
  have htrace : WordTrace (prefixWord ++ tailWord_1550509) baseStart_1550509 baseEnd_1550509 := by
    simpa [prefixWord, tailWord_1550509, baseEnd_1550509] using wordTrace_append hprefix tailTrace_1550509
  have hstable : (prefixWord ++ tailWord_1550509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550509).length < 2 ^ (prefixWord ++ tailWord_1550509).sum := by decide
  have hdescent : baseEnd_1550509 < baseStart_1550509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550512 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 6, 4, 2]
def baseStart_1550512 : Nat := 118140960795 + 1550512 * 2 ^ 59
def prefixEnd_1550512 : Nat := 4983230072969 + 3 ^ 40 * 1550512 * 2
def baseEnd_1550512 : Nat := 796157916564142848369331

theorem tailTrace_1550512 : CollatzResearch.WordTrace tailWord_1550512 prefixEnd_1550512 796157916564142848369331 := by
  unfold tailWord_1550512
  simp only [CollatzResearch.WordTrace]
  refine ⟨28275909279383652606198895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37701212372511536808265193 28275909279383652606198895)
  ·
    refine ⟨42413863919075478909298343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28275909279383652606198895 42413863919075478909298343)
    ·
      refine ⟨63620795878613218363947515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42413863919075478909298343 63620795878613218363947515)
      ·
        refine ⟨95431193817919827545921273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63620795878613218363947515 95431193817919827545921273)
        ·
          refine ⟨71573395363439870659440955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95431193817919827545921273 71573395363439870659440955)
          ·
            refine ⟨107360093045159805989161433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71573395363439870659440955 107360093045159805989161433)
            ·
              refine ⟨80520069783869854491871075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107360093045159805989161433 80520069783869854491871075)
              ·
                refine ⟨120780104675804781737806613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80520069783869854491871075 120780104675804781737806613)
                ·
                  refine ⟨5661567406678349143959685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120780104675804781737806613 5661567406678349143959685)
                  ·
                    refine ⟨1061543888752190464492441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5661567406678349143959685 1061543888752190464492441)
                    ·
                      refine ⟨796157916564142848369331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1061543888752190464492441 796157916564142848369331)
                      ·
                        rfl

theorem cell23_1550512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 6, 4, 2].length) (baseStart_1550512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550512 prefixEnd_1550512 := by exact prefixLift 1550512
  have htrace : WordTrace (prefixWord ++ tailWord_1550512) baseStart_1550512 baseEnd_1550512 := by
    simpa [prefixWord, tailWord_1550512, baseEnd_1550512] using wordTrace_append hprefix tailTrace_1550512
  have hstable : (prefixWord ++ tailWord_1550512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550512).length < 2 ^ (prefixWord ++ tailWord_1550512).sum := by decide
  have hdescent : baseEnd_1550512 < baseStart_1550512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550539 : List Nat := [1, 1, 1, 1, 3, 2, 3, 6, 1, 4]
def baseStart_1550539 : Nat := 118140960795 + 1550539 * 2 ^ 59
def prefixEnd_1550539 : Nat := 4983230072969 + 3 ^ 40 * 1550539 * 2
def baseEnd_1550539 : Nat := 265390593513938080910569

theorem tailTrace_1550539 : CollatzResearch.WordTrace tailWord_1550539 prefixEnd_1550539 265390593513938080910569 := by
  unfold tailWord_1550539
  simp only [CollatzResearch.WordTrace]
  refine ⟨56552803329669488823630671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37701868886446325882420447 56552803329669488823630671)
  ·
    refine ⟨84829204994504233235446007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56552803329669488823630671 84829204994504233235446007)
    ·
      refine ⟨127243807491756349853169011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84829204994504233235446007 127243807491756349853169011)
      ·
        refine ⟨190865711237634524779753517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127243807491756349853169011 190865711237634524779753517)
        ·
          refine ⟨71574641714112946792407569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190865711237634524779753517 71574641714112946792407569)
          ·
            refine ⟨53680981285584710094305677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71574641714112946792407569 53680981285584710094305677)
            ·
              refine ⟨20130367982094266285364629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53680981285584710094305677 20130367982094266285364629)
              ·
                refine ⟨943610999160668732126467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20130367982094266285364629 943610999160668732126467)
                ·
                  refine ⟨1415416498741003098189701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 943610999160668732126467 1415416498741003098189701)
                  ·
                    refine ⟨265390593513938080910569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1415416498741003098189701 265390593513938080910569)
                    ·
                      rfl

theorem cell23_1550539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 1, 4].length) (baseStart_1550539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550539 prefixEnd_1550539 := by exact prefixLift 1550539
  have htrace : WordTrace (prefixWord ++ tailWord_1550539) baseStart_1550539 baseEnd_1550539 := by
    simpa [prefixWord, tailWord_1550539, baseEnd_1550539] using wordTrace_append hprefix tailTrace_1550539
  have hstable : (prefixWord ++ tailWord_1550539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550539).length < 2 ^ (prefixWord ++ tailWord_1550539).sum := by decide
  have hdescent : baseEnd_1550539 < baseStart_1550539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550619 : List Nat := [1, 1, 1, 1, 1, 1, 9, 2, 1, 1, 4]
def baseStart_1550619 : Nat := 118140960795 + 1550619 * 2 ^ 59
def prefixEnd_1550619 : Nat := 4983230072969 + 3 ^ 40 * 1550619 * 2
def baseEnd_1550619 : Nat := 796212858994173929731339

theorem tailTrace_1550619 : CollatzResearch.WordTrace tailWord_1550619 prefixEnd_1550619 796212858994173929731339 := by
  unfold tailWord_1550619
  simp only [CollatzResearch.WordTrace]
  refine ⟨56555721169379662486542911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37703814112919774991028607 56555721169379662486542911)
  ·
    refine ⟨84833581754069493729814367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56555721169379662486542911 84833581754069493729814367)
    ·
      refine ⟨127250372631104240594721551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84833581754069493729814367 127250372631104240594721551)
      ·
        refine ⟨190875558946656360892082327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127250372631104240594721551 190875558946656360892082327)
        ·
          refine ⟨286313338419984541338123491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190875558946656360892082327 286313338419984541338123491)
          ·
            refine ⟨429470007629976812007185237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286313338419984541338123491 429470007629976812007185237)
            ·
              refine ⟨2516425825956895382854601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 429470007629976812007185237 2516425825956895382854601)
              ·
                refine ⟨1887319369467671537140951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2516425825956895382854601 1887319369467671537140951)
                ·
                  refine ⟨2830979054201507305711427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1887319369467671537140951 2830979054201507305711427)
                  ·
                    refine ⟨4246468581302260958567141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2830979054201507305711427 4246468581302260958567141)
                    ·
                      refine ⟨796212858994173929731339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4246468581302260958567141 796212858994173929731339)
                      ·
                        rfl

theorem cell23_1550619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 1, 4].length) (baseStart_1550619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550619 prefixEnd_1550619 := by exact prefixLift 1550619
  have htrace : WordTrace (prefixWord ++ tailWord_1550619) baseStart_1550619 baseEnd_1550619 := by
    simpa [prefixWord, tailWord_1550619, baseEnd_1550619] using wordTrace_append hprefix tailTrace_1550619
  have hstable : (prefixWord ++ tailWord_1550619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550619).length < 2 ^ (prefixWord ++ tailWord_1550619).sum := by decide
  have hdescent : baseEnd_1550619 < baseStart_1550619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550629 : List Nat := [1, 3, 1, 2, 5, 1, 1, 2, 1, 6]
def baseStart_1550629 : Nat := 118140960795 + 1550629 * 2 ^ 59
def prefixEnd_1550629 : Nat := 4983230072969 + 3 ^ 40 * 1550629 * 2
def baseEnd_1550629 : Nat := 265405997933572963535431

theorem tailTrace_1550629 : CollatzResearch.WordTrace tailWord_1550629 prefixEnd_1550629 265405997933572963535431 := by
  unfold tailWord_1550629
  simp only [CollatzResearch.WordTrace]
  refine ⟨56556085899343434194406941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37704057266228956129604627 56556085899343434194406941)
  ·
    refine ⟨21208532212253787822902603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56556085899343434194406941 21208532212253787822902603)
    ·
      refine ⟨31812798318380681734353905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21208532212253787822902603 31812798318380681734353905)
      ·
        refine ⟨23859598738785511300765429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31812798318380681734353905 23859598738785511300765429)
        ·
          refine ⟨2236837381761141684446759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23859598738785511300765429 2236837381761141684446759)
          ·
            refine ⟨3355256072641712526670139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2236837381761141684446759 3355256072641712526670139)
            ·
              refine ⟨5032884108962568790005209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3355256072641712526670139 5032884108962568790005209)
              ·
                refine ⟨3774663081721926592503907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5032884108962568790005209 3774663081721926592503907)
                ·
                  refine ⟨5661994622582889888755861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3774663081721926592503907 5661994622582889888755861)
                  ·
                    refine ⟨265405997933572963535431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5661994622582889888755861 265405997933572963535431)
                    ·
                      rfl

theorem cell23_1550629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_1550629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550629 prefixEnd_1550629 := by exact prefixLift 1550629
  have htrace : WordTrace (prefixWord ++ tailWord_1550629) baseStart_1550629 baseEnd_1550629 := by
    simpa [prefixWord, tailWord_1550629, baseEnd_1550629] using wordTrace_append hprefix tailTrace_1550629
  have hstable : (prefixWord ++ tailWord_1550629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550629).length < 2 ^ (prefixWord ++ tailWord_1550629).sum := by decide
  have hdescent : baseEnd_1550629 < baseStart_1550629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550639 : List Nat := [1, 1, 2, 1, 2, 1, 4, 5, 1, 2, 3]
def baseStart_1550639 : Nat := 118140960795 + 1550639 * 2 ^ 59
def prefixEnd_1550639 : Nat := 4983230072969 + 3 ^ 40 * 1550639 * 2
def baseEnd_1550639 : Nat := 796223128607263851481247

theorem tailTrace_1550639 : CollatzResearch.WordTrace tailWord_1550639 prefixEnd_1550639 796223128607263851481247 := by
  unfold tailWord_1550639
  simp only [CollatzResearch.WordTrace]
  refine ⟨56556450629307205902270971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37704300419538137268180647 56556450629307205902270971)
  ·
    refine ⟨84834675943960808853406457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56556450629307205902270971 84834675943960808853406457)
    ·
      refine ⟨63626006957970606640054843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84834675943960808853406457 63626006957970606640054843)
      ·
        refine ⟨95439010436955909960082265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63626006957970606640054843 95439010436955909960082265)
        ·
          refine ⟨71579257827716932470061699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95439010436955909960082265 71579257827716932470061699)
          ·
            refine ⟨107368886741575398705092549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71579257827716932470061699 107368886741575398705092549)
            ·
              refine ⟨20131666264045387257204853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107368886741575398705092549 20131666264045387257204853)
              ·
                refine ⟨1887343712254255055362955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20131666264045387257204853 1887343712254255055362955)
                ·
                  refine ⟨2831015568381382583044433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1887343712254255055362955 2831015568381382583044433)
                  ·
                    refine ⟨2123261676286036937283325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2831015568381382583044433 2123261676286036937283325)
                    ·
                      refine ⟨796223128607263851481247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2123261676286036937283325 796223128607263851481247)
                      ·
                        rfl

theorem cell23_1550639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 2, 3].length) (baseStart_1550639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550639 prefixEnd_1550639 := by exact prefixLift 1550639
  have htrace : WordTrace (prefixWord ++ tailWord_1550639) baseStart_1550639 baseEnd_1550639 := by
    simpa [prefixWord, tailWord_1550639, baseEnd_1550639] using wordTrace_append hprefix tailTrace_1550639
  have hstable : (prefixWord ++ tailWord_1550639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550639).length < 2 ^ (prefixWord ++ tailWord_1550639).sum := by decide
  have hdescent : baseEnd_1550639 < baseStart_1550639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550642 : List Nat := [3, 2, 1, 1, 5, 11]
def baseStart_1550642 : Nat := 118140960795 + 1550642 * 2 ^ 59
def prefixEnd_1550642 : Nat := 4983230072969 + 3 ^ 40 * 1550642 * 2
def baseEnd_1550642 : Nat := 3276644728597643373431

theorem tailTrace_1550642 : CollatzResearch.WordTrace tailWord_1550642 prefixEnd_1550642 3276644728597643373431 := by
  unfold tailWord_1550642
  simp only [CollatzResearch.WordTrace]
  refine ⟨14139140012074084353657545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37704373365530891609753453 14139140012074084353657545)
  ·
    refine ⟨10604355009055563265243159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14139140012074084353657545 10604355009055563265243159)
    ·
      refine ⟨15906532513583344897864739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10604355009055563265243159 15906532513583344897864739)
      ·
        refine ⟨23859798770375017346797109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15906532513583344897864739 23859798770375017346797109)
        ·
          refine ⟨2236856134722657876262229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23859798770375017346797109 2236856134722657876262229)
          ·
            refine ⟨3276644728597643373431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2236856134722657876262229 3276644728597643373431)
            ·
              rfl

theorem cell23_1550642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 11].length) (baseStart_1550642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550642 prefixEnd_1550642 := by exact prefixLift 1550642
  have htrace : WordTrace (prefixWord ++ tailWord_1550642) baseStart_1550642 baseEnd_1550642 := by
    simpa [prefixWord, tailWord_1550642, baseEnd_1550642] using wordTrace_append hprefix tailTrace_1550642
  have hstable : (prefixWord ++ tailWord_1550642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550642).length < 2 ^ (prefixWord ++ tailWord_1550642).sum := by decide
  have hdescent : baseEnd_1550642 < baseStart_1550642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550682 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5]
def baseStart_1550682 : Nat := 118140960795 + 1550682 * 2 ^ 59
def prefixEnd_1550682 : Nat := 4983230072969 + 3 ^ 40 * 1550682 * 2
def baseEnd_1550682 : Nat := 796245208275407183243549

theorem tailTrace_1550682 : CollatzResearch.WordTrace tailWord_1550682 prefixEnd_1550682 796245208275407183243549 := by
  unfold tailWord_1550682
  simp only [CollatzResearch.WordTrace]
  refine ⟨14139504742037856061521575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37705345978767616164057533 14139504742037856061521575)
  ·
    refine ⟨21209257113056784092282363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14139504742037856061521575 21209257113056784092282363)
    ·
      refine ⟨31813885669585176138423545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21209257113056784092282363 31813885669585176138423545)
      ·
        refine ⟨23860414252188882103817659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31813885669585176138423545 23860414252188882103817659)
        ·
          refine ⟨35790621378283323155726489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23860414252188882103817659 35790621378283323155726489)
          ·
            refine ⟨26842966033712492366794867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35790621378283323155726489 26842966033712492366794867)
            ·
              refine ⟨40264449050568738550192301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26842966033712492366794867 40264449050568738550192301)
              ·
                refine ⟨15099168393963276956322113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40264449050568738550192301 15099168393963276956322113)
                ·
                  refine ⟨11324376295472457717241585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15099168393963276956322113 11324376295472457717241585)
                  ·
                    refine ⟨8493282221604343287931189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11324376295472457717241585 8493282221604343287931189)
                    ·
                      refine ⟨796245208275407183243549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8493282221604343287931189 796245208275407183243549)
                      ·
                        rfl

theorem cell23_1550682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_1550682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550682 prefixEnd_1550682 := by exact prefixLift 1550682
  have htrace : WordTrace (prefixWord ++ tailWord_1550682) baseStart_1550682 baseEnd_1550682 := by
    simpa [prefixWord, tailWord_1550682, baseEnd_1550682] using wordTrace_append hprefix tailTrace_1550682
  have hstable : (prefixWord ++ tailWord_1550682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550682).length < 2 ^ (prefixWord ++ tailWord_1550682).sum := by decide
  have hdescent : baseEnd_1550682 < baseStart_1550682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550690 : List Nat := [3, 3, 2, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_1550690 : Nat := 118140960795 + 1550690 * 2 ^ 59
def prefixEnd_1550690 : Nat := 4983230072969 + 3 ^ 40 * 1550690 * 2
def baseEnd_1550690 : Nat := 796249316120643151943513

theorem tailTrace_1550690 : CollatzResearch.WordTrace tailWord_1550690 prefixEnd_1550690 796249316120643151943513 := by
  unfold tailWord_1550690
  simp only [CollatzResearch.WordTrace]
  refine ⟨14139577688030610403094381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37705540501414961074918349 14139577688030610403094381)
  ·
    refine ⟨5302341633011478901160393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14139577688030610403094381 5302341633011478901160393)
    ·
      refine ⟨3976756224758609175870295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5302341633011478901160393 3976756224758609175870295)
      ·
        refine ⟨5965134337137913763805443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3976756224758609175870295 5965134337137913763805443)
        ·
          refine ⟨8947701505706870645708165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5965134337137913763805443 8947701505706870645708165)
          ·
            refine ⟨1677694032320038246070281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8947701505706870645708165 1677694032320038246070281)
            ·
              refine ⟨1258270524240028684552711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1677694032320038246070281 1258270524240028684552711)
              ·
                refine ⟨1887405786360043026829067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1258270524240028684552711 1887405786360043026829067)
                ·
                  refine ⟨2831108679540064540243601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1887405786360043026829067 2831108679540064540243601)
                  ·
                    refine ⟨2123331509655048405182701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2831108679540064540243601 2123331509655048405182701)
                    ·
                      refine ⟨796249316120643151943513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2123331509655048405182701 796249316120643151943513)
                      ·
                        rfl

theorem cell23_1550690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_1550690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550690 prefixEnd_1550690 := by exact prefixLift 1550690
  have htrace : WordTrace (prefixWord ++ tailWord_1550690) baseStart_1550690 baseEnd_1550690 := by
    simpa [prefixWord, tailWord_1550690, baseEnd_1550690] using wordTrace_append hprefix tailTrace_1550690
  have hstable : (prefixWord ++ tailWord_1550690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550690).length < 2 ^ (prefixWord ++ tailWord_1550690).sum := by decide
  have hdescent : baseEnd_1550690 < baseStart_1550690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550760 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_1550760 : Nat := 118140960795 + 1550760 * 2 ^ 59
def prefixEnd_1550760 : Nat := 4983230072969 + 3 ^ 40 * 1550760 * 2
def baseEnd_1550760 : Nat := 796285259766457878068191

theorem tailTrace_1550760 : CollatzResearch.WordTrace tailWord_1550760 prefixEnd_1550760 796285259766457878068191 := by
  unfold tailWord_1550760
  simp only [CollatzResearch.WordTrace]
  refine ⟨28280431930934421783712867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37707242574579229044950489 28280431930934421783712867)
  ·
    refine ⟨42420647896401632675569301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28280431930934421783712867 42420647896401632675569301)
    ·
      refine ⟨1988467870143826531667311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42420647896401632675569301 1988467870143826531667311)
      ·
        refine ⟨2982701805215739797500967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1988467870143826531667311 2982701805215739797500967)
        ·
          refine ⟨4474052707823609696251451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2982701805215739797500967 4474052707823609696251451)
          ·
            refine ⟨6711079061735414544377177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4474052707823609696251451 6711079061735414544377177)
            ·
              refine ⟨5033309296301560908282883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6711079061735414544377177 5033309296301560908282883)
              ·
                refine ⟨7549963944452341362424325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5033309296301560908282883 7549963944452341362424325)
                ·
                  refine ⟨1415618239584814005454561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7549963944452341362424325 1415618239584814005454561)
                  ·
                    refine ⟨1061713679688610504090921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1415618239584814005454561 1061713679688610504090921)
                    ·
                      refine ⟨796285259766457878068191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1061713679688610504090921 796285259766457878068191)
                      ·
                        rfl

theorem cell23_1550760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_1550760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550760 prefixEnd_1550760 := by exact prefixLift 1550760
  have htrace : WordTrace (prefixWord ++ tailWord_1550760) baseStart_1550760 baseEnd_1550760 := by
    simpa [prefixWord, tailWord_1550760, baseEnd_1550760] using wordTrace_append hprefix tailTrace_1550760
  have hstable : (prefixWord ++ tailWord_1550760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550760).length < 2 ^ (prefixWord ++ tailWord_1550760).sum := by decide
  have hdescent : baseEnd_1550760 < baseStart_1550760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550777 : List Nat := [1, 2, 1, 4, 3, 3, 2, 1, 2, 2, 2]
def baseStart_1550777 : Nat := 118140960795 + 1550777 * 2 ^ 59
def prefixEnd_1550777 : Nat := 4983230072969 + 3 ^ 40 * 1550777 * 2
def baseEnd_1550777 : Nat := 796293988937584311555613

theorem tailTrace_1550777 : CollatzResearch.WordTrace tailWord_1550777 prefixEnd_1550777 796293988937584311555613 := by
  unfold tailWord_1550777
  simp only [CollatzResearch.WordTrace]
  refine ⟨56561483902807255470794585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37707655935204836980529723 56561483902807255470794585)
  ·
    refine ⟨42421112927105441603095939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56561483902807255470794585 42421112927105441603095939)
    ·
      refine ⟨63631669390658162404643909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42421112927105441603095939 63631669390658162404643909)
      ·
        refine ⟨11930938010748405450870733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63631669390658162404643909 11930938010748405450870733)
        ·
          refine ⟨4474101754030652044076525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11930938010748405450870733 4474101754030652044076525)
          ·
            refine ⟨1677788157761494516528697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4474101754030652044076525 1677788157761494516528697)
            ·
              refine ⟨1258341118321120887396523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1677788157761494516528697 1258341118321120887396523)
              ·
                refine ⟨1887511677481681331094785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1258341118321120887396523 1887511677481681331094785)
                ·
                  refine ⟨1415633758111260998321089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1887511677481681331094785 1415633758111260998321089)
                  ·
                    refine ⟨1061725318583445748740817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1415633758111260998321089 1061725318583445748740817)
                    ·
                      refine ⟨796293988937584311555613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1061725318583445748740817 796293988937584311555613)
                      ·
                        rfl

theorem cell23_1550777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_1550777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550777 prefixEnd_1550777 := by exact prefixLift 1550777
  have htrace : WordTrace (prefixWord ++ tailWord_1550777) baseStart_1550777 baseEnd_1550777 := by
    simpa [prefixWord, tailWord_1550777, baseEnd_1550777] using wordTrace_append hprefix tailTrace_1550777
  have hstable : (prefixWord ++ tailWord_1550777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550777).length < 2 ^ (prefixWord ++ tailWord_1550777).sum := by decide
  have hdescent : baseEnd_1550777 < baseStart_1550777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550806 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_1550806 : Nat := 118140960795 + 1550806 * 2 ^ 59
def prefixEnd_1550806 : Nat := 4983230072969 + 3 ^ 40 * 1550806 * 2
def baseEnd_1550806 : Nat := 796308879876564698092979

theorem tailTrace_1550806 : CollatzResearch.WordTrace tailWord_1550806 prefixEnd_1550806 796308879876564698092979 := by
  unfold tailWord_1550806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3535158851231387088975017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37708361079801462282400181 3535158851231387088975017)
  ·
    refine ⟨2651369138423540316731263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3535158851231387088975017 2651369138423540316731263)
    ·
      refine ⟨3977053707635310475096895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2651369138423540316731263 3977053707635310475096895)
      ·
        refine ⟨5965580561452965712645343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3977053707635310475096895 5965580561452965712645343)
        ·
          refine ⟨8948370842179448568968015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5965580561452965712645343 8948370842179448568968015)
          ·
            refine ⟨13422556263269172853452023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8948370842179448568968015 13422556263269172853452023)
            ·
              refine ⟨20133834394903759280178035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13422556263269172853452023 20133834394903759280178035)
              ·
                refine ⟨30200751592355638920267053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20133834394903759280178035 30200751592355638920267053)
                ·
                  refine ⟨11325281847133364595100145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30200751592355638920267053 11325281847133364595100145)
                  ·
                    refine ⟨8493961385350023446325109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11325281847133364595100145 8493961385350023446325109)
                    ·
                      refine ⟨796308879876564698092979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8493961385350023446325109 796308879876564698092979)
                      ·
                        rfl

theorem cell23_1550806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_1550806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550806 prefixEnd_1550806 := by exact prefixLift 1550806
  have htrace : WordTrace (prefixWord ++ tailWord_1550806) baseStart_1550806 baseEnd_1550806 := by
    simpa [prefixWord, tailWord_1550806, baseEnd_1550806] using wordTrace_append hprefix tailTrace_1550806
  have hstable : (prefixWord ++ tailWord_1550806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550806).length < 2 ^ (prefixWord ++ tailWord_1550806).sum := by decide
  have hdescent : baseEnd_1550806 < baseStart_1550806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550816 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 2, 4, 2]
def baseStart_1550816 : Nat := 118140960795 + 1550816 * 2 ^ 59
def prefixEnd_1550816 : Nat := 4983230072969 + 3 ^ 40 * 1550816 * 2
def baseEnd_1550816 : Nat := 796314014683109658967933

theorem tailTrace_1550816 : CollatzResearch.WordTrace tailWord_1550816 prefixEnd_1550816 796314014683109658967933 := by
  unfold tailWord_1550816
  simp only [CollatzResearch.WordTrace]
  refine ⟨28281453174832982565732151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37708604233110643420976201 28281453174832982565732151)
  ·
    refine ⟨42422179762249473848598227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28281453174832982565732151 42422179762249473848598227)
    ·
      refine ⟨63633269643374210772897341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42422179762249473848598227 63633269643374210772897341)
      ·
        refine ⟨23862476116265329039836503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63633269643374210772897341 23862476116265329039836503)
        ·
          refine ⟨35793714174397993559754755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23862476116265329039836503 35793714174397993559754755)
          ·
            refine ⟨53690571261596990339632133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35793714174397993559754755 53690571261596990339632133)
            ·
              refine ⟨10066982111549435688681025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53690571261596990339632133 10066982111549435688681025)
              ·
                refine ⟨7550236583662076766510769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10066982111549435688681025 7550236583662076766510769)
                ·
                  refine ⟨5662677437746557574883077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7550236583662076766510769 5662677437746557574883077)
                  ·
                    refine ⟨1061752019577479545290577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5662677437746557574883077 1061752019577479545290577)
                    ·
                      refine ⟨796314014683109658967933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1061752019577479545290577 796314014683109658967933)
                      ·
                        rfl

theorem cell23_1550816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_1550816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550816 prefixEnd_1550816 := by exact prefixLift 1550816
  have htrace : WordTrace (prefixWord ++ tailWord_1550816) baseStart_1550816 baseEnd_1550816 := by
    simpa [prefixWord, tailWord_1550816, baseEnd_1550816] using wordTrace_append hprefix tailTrace_1550816
  have hstable : (prefixWord ++ tailWord_1550816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550816).length < 2 ^ (prefixWord ++ tailWord_1550816).sum := by decide
  have hdescent : baseEnd_1550816 < baseStart_1550816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550860 : List Nat := [2, 2, 1, 2, 4, 2, 2, 3, 1, 4]
def baseStart_1550860 : Nat := 118140960795 + 1550860 * 2 ^ 59
def prefixEnd_1550860 : Nat := 4983230072969 + 3 ^ 40 * 1550860 * 2
def baseEnd_1550860 : Nat := 265445535943969162272577

theorem tailTrace_1550860 : CollatzResearch.WordTrace tailWord_1550860 prefixEnd_1550860 265445535943969162272577 := by
  unfold tailWord_1550860
  simp only [CollatzResearch.WordTrace]
  refine ⟨28282255580753280323033017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37709674107671040430710689 28282255580753280323033017)
  ·
    refine ⟨21211691685564960242274763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28282255580753280323033017 21211691685564960242274763)
    ·
      refine ⟨31817537528347440363412145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21211691685564960242274763 31817537528347440363412145)
      ·
        refine ⟨23863153146260580272559109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31817537528347440363412145 23863153146260580272559109)
        ·
          refine ⟨4474341214923858801104833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23863153146260580272559109 4474341214923858801104833)
          ·
            refine ⟨3355755911192894100828625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4474341214923858801104833 3355755911192894100828625)
            ·
              refine ⟨2516816933394670575621469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3355755911192894100828625 2516816933394670575621469)
              ·
                refine ⟨943806350023001465858051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2516816933394670575621469 943806350023001465858051)
                ·
                  refine ⟨1415709525034502198787077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 943806350023001465858051 1415709525034502198787077)
                  ·
                    refine ⟨265445535943969162272577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1415709525034502198787077 265445535943969162272577)
                    ·
                      rfl

theorem cell23_1550860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 1, 4].length) (baseStart_1550860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550860 prefixEnd_1550860 := by exact prefixLift 1550860
  have htrace : WordTrace (prefixWord ++ tailWord_1550860) baseStart_1550860 baseEnd_1550860 := by
    simpa [prefixWord, tailWord_1550860, baseEnd_1550860] using wordTrace_append hprefix tailTrace_1550860
  have hstable : (prefixWord ++ tailWord_1550860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550860).length < 2 ^ (prefixWord ++ tailWord_1550860).sum := by decide
  have hdescent : baseEnd_1550860 < baseStart_1550860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550883 : List Nat := [1, 1, 1, 4, 4, 1, 1, 3, 3, 1, 3]
def baseStart_1550883 : Nat := 118140960795 + 1550883 * 2 ^ 59
def prefixEnd_1550883 : Nat := 4983230072969 + 3 ^ 40 * 1550883 * 2
def baseEnd_1550883 : Nat := 796348417886960896830125

theorem tailTrace_1550883 : CollatzResearch.WordTrace tailWord_1550883 prefixEnd_1550883 796348417886960896830125 := by
  unfold tailWord_1550883
  simp only [CollatzResearch.WordTrace]
  refine ⟨56565350040423235574153303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37710233360282157049435535 56565350040423235574153303)
  ·
    refine ⟨84848025060634853361229955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56565350040423235574153303 84848025060634853361229955)
    ·
      refine ⟨127272037590952280041844933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84848025060634853361229955 127272037590952280041844933)
      ·
        refine ⟨23863507048303552507845925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127272037590952280041844933 23863507048303552507845925)
        ·
          refine ⟨4474407571556916095221111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23863507048303552507845925 4474407571556916095221111)
          ·
            refine ⟨6711611357335374142831667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4474407571556916095221111 6711611357335374142831667)
            ·
              refine ⟨10067417036003061214247501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6711611357335374142831667 10067417036003061214247501)
              ·
                refine ⟨3775281388501147955342813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10067417036003061214247501 3775281388501147955342813)
                ·
                  refine ⟨1415730520687930483253555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3775281388501147955342813 1415730520687930483253555)
                  ·
                    refine ⟨2123595781031895724880333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1415730520687930483253555 2123595781031895724880333)
                    ·
                      refine ⟨796348417886960896830125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2123595781031895724880333 796348417886960896830125)
                      ·
                        rfl

theorem cell23_1550883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_1550883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550883 prefixEnd_1550883 := by exact prefixLift 1550883
  have htrace : WordTrace (prefixWord ++ tailWord_1550883) baseStart_1550883 baseEnd_1550883 := by
    simpa [prefixWord, tailWord_1550883, baseEnd_1550883] using wordTrace_append hprefix tailTrace_1550883
  have hstable : (prefixWord ++ tailWord_1550883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550883).length < 2 ^ (prefixWord ++ tailWord_1550883).sum := by decide
  have hdescent : baseEnd_1550883 < baseStart_1550883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550917 : List Nat := [1, 3, 1, 1, 1, 7, 1, 3, 1, 1, 3]
def baseStart_1550917 : Nat := 118140960795 + 1550917 * 2 ^ 59
def prefixEnd_1550917 : Nat := 4983230072969 + 3 ^ 40 * 1550917 * 2
def baseEnd_1550917 : Nat := 796365876229213763804969

theorem tailTrace_1550917 : CollatzResearch.WordTrace tailWord_1550917 prefixEnd_1550917 796365876229213763804969 := by
  unfold tailWord_1550917
  simp only [CollatzResearch.WordTrace]
  refine ⟨56566590122300059380891005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37711060081533372920594003 56566590122300059380891005)
  ·
    refine ⟨21212471295862522267834127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56566590122300059380891005 21212471295862522267834127)
    ·
      refine ⟨31818706943793783401751191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21212471295862522267834127 31818706943793783401751191)
      ·
        refine ⟨47728060415690675102626787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31818706943793783401751191 47728060415690675102626787)
        ·
          refine ⟨71592090623536012653940181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47728060415690675102626787 71592090623536012653940181)
          ·
            refine ⟨1677939623989125296576723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 71592090623536012653940181 1677939623989125296576723)
            ·
              refine ⟨2516909435983687944865085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1677939623989125296576723 2516909435983687944865085)
              ·
                refine ⟨943841038493882979324407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2516909435983687944865085 943841038493882979324407)
                ·
                  refine ⟨1415761557740824468986611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 943841038493882979324407 1415761557740824468986611)
                  ·
                    refine ⟨2123642336611236703479917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1415761557740824468986611 2123642336611236703479917)
                    ·
                      refine ⟨796365876229213763804969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2123642336611236703479917 796365876229213763804969)
                      ·
                        rfl

theorem cell23_1550917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 1, 1, 3].length) (baseStart_1550917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550917 prefixEnd_1550917 := by exact prefixLift 1550917
  have htrace : WordTrace (prefixWord ++ tailWord_1550917) baseStart_1550917 baseEnd_1550917 := by
    simpa [prefixWord, tailWord_1550917, baseEnd_1550917] using wordTrace_append hprefix tailTrace_1550917
  have hstable : (prefixWord ++ tailWord_1550917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550917).length < 2 ^ (prefixWord ++ tailWord_1550917).sum := by decide
  have hdescent : baseEnd_1550917 < baseStart_1550917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550923 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 5, 2, 2]
def baseStart_1550923 : Nat := 118140960795 + 1550923 * 2 ^ 59
def prefixEnd_1550923 : Nat := 4983230072969 + 3 ^ 40 * 1550923 * 2
def baseEnd_1550923 : Nat := 796368957113140740329941

theorem tailTrace_1550923 : CollatzResearch.WordTrace tailWord_1550923 prefixEnd_1550923 796368957113140740329941 := by
  unfold tailWord_1550923
  simp only [CollatzResearch.WordTrace]
  refine ⟨56566808960278322405609423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37711205973518881603739615 56566808960278322405609423)
  ·
    refine ⟨84850213440417483608414135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56566808960278322405609423 84850213440417483608414135)
    ·
      refine ⟨127275320160626225412621203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84850213440417483608414135 127275320160626225412621203)
      ·
        refine ⟨190912980240939338118931805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127275320160626225412621203 190912980240939338118931805)
        ·
          refine ⟨71592367590352251794599427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190912980240939338118931805 71592367590352251794599427)
          ·
            refine ⟨107388551385528377691899141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71592367590352251794599427 107388551385528377691899141)
            ·
              refine ⟨20135353384786570817231089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107388551385528377691899141 20135353384786570817231089)
              ·
                refine ⟨15101515038589928112923317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20135353384786570817231089 15101515038589928112923317)
                ·
                  refine ⟨1415767034867805760586561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15101515038589928112923317 1415767034867805760586561)
                  ·
                    refine ⟨1061825276150854320439921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1415767034867805760586561 1061825276150854320439921)
                    ·
                      refine ⟨796368957113140740329941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1061825276150854320439921 796368957113140740329941)
                      ·
                        rfl

theorem cell23_1550923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 2, 2].length) (baseStart_1550923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550923 prefixEnd_1550923 := by exact prefixLift 1550923
  have htrace : WordTrace (prefixWord ++ tailWord_1550923) baseStart_1550923 baseEnd_1550923 := by
    simpa [prefixWord, tailWord_1550923, baseEnd_1550923] using wordTrace_append hprefix tailTrace_1550923
  have hstable : (prefixWord ++ tailWord_1550923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550923).length < 2 ^ (prefixWord ++ tailWord_1550923).sum := by decide
  have hdescent : baseEnd_1550923 < baseStart_1550923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550926 : List Nat := [4, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_1550926 : Nat := 118140960795 + 1550926 * 2 ^ 59
def prefixEnd_1550926 : Nat := 4983230072969 + 3 ^ 40 * 1550926 * 2
def baseEnd_1550926 : Nat := 796370497555104228592427

theorem tailTrace_1550926 : CollatzResearch.WordTrace tailWord_1550926 prefixEnd_1550926 796370497555104228592427 := by
  unfold tailWord_1550926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7070864797408431739746079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37711278919511635945312421 7070864797408431739746079)
  ·
    refine ⟨10606297196112647609619119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7070864797408431739746079 10606297196112647609619119)
    ·
      refine ⟨15909445794168971414428679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10606297196112647609619119 15909445794168971414428679)
      ·
        refine ⟨23864168691253457121643019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15909445794168971414428679 23864168691253457121643019)
        ·
          refine ⟨35796253036880185682464529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23864168691253457121643019 35796253036880185682464529)
          ·
            refine ⟨26847189777660139261848397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35796253036880185682464529 26847189777660139261848397)
            ·
              refine ⟨10067696166622552223193149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26847189777660139261848397 10067696166622552223193149)
              ·
                refine ⟨3775386062483457083697431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10067696166622552223193149 3775386062483457083697431)
                ·
                  refine ⟨5663079093725185625546147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3775386062483457083697431 5663079093725185625546147)
                  ·
                    refine ⟨8494618640587778438319221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5663079093725185625546147 8494618640587778438319221)
                    ·
                      refine ⟨796370497555104228592427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8494618640587778438319221 796370497555104228592427)
                      ·
                        rfl

theorem cell23_1550926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_1550926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550926 prefixEnd_1550926 := by exact prefixLift 1550926
  have htrace : WordTrace (prefixWord ++ tailWord_1550926) baseStart_1550926 baseEnd_1550926 := by
    simpa [prefixWord, tailWord_1550926, baseEnd_1550926] using wordTrace_append hprefix tailTrace_1550926
  have hstable : (prefixWord ++ tailWord_1550926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550926).length < 2 ^ (prefixWord ++ tailWord_1550926).sum := by decide
  have hdescent : baseEnd_1550926 < baseStart_1550926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550929 : List Nat := [1, 2, 2, 1, 3, 3, 11]
def baseStart_1550929 : Nat := 118140960795 + 1550929 * 2 ^ 59
def prefixEnd_1550929 : Nat := 4983230072969 + 3 ^ 40 * 1550929 * 2
def baseEnd_1550929 : Nat := 9831753555519354529073

theorem tailTrace_1550929 : CollatzResearch.WordTrace tailWord_1550929 prefixEnd_1550929 9831753555519354529073 := by
  unfold tailWord_1550929
  simp only [CollatzResearch.WordTrace]
  refine ⟨56567027798256585430327841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37711351865504390286885227 56567027798256585430327841)
  ·
    refine ⟨42425270848692439072745881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56567027798256585430327841 42425270848692439072745881)
    ·
      refine ⟨31818953136519329304559411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42425270848692439072745881 31818953136519329304559411)
      ·
        refine ⟨47728429704778993956839117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31818953136519329304559411 47728429704778993956839117)
        ·
          refine ⟨17898161139292122733814669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47728429704778993956839117 17898161139292122733814669)
          ·
            refine ⟨6711810427234546025180501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17898161139292122733814669 6711810427234546025180501)
            ·
              refine ⟨9831753555519354529073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6711810427234546025180501 9831753555519354529073)
              ·
                rfl

theorem cell23_1550929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 11].length) (baseStart_1550929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550929 prefixEnd_1550929 := by exact prefixLift 1550929
  have htrace : WordTrace (prefixWord ++ tailWord_1550929) baseStart_1550929 baseEnd_1550929 := by
    simpa [prefixWord, tailWord_1550929, baseEnd_1550929] using wordTrace_append hprefix tailTrace_1550929
  have hstable : (prefixWord ++ tailWord_1550929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550929).length < 2 ^ (prefixWord ++ tailWord_1550929).sum := by decide
  have hdescent : baseEnd_1550929 < baseStart_1550929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551026 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_1551026 : Nat := 118140960795 + 1551026 * 2 ^ 59
def prefixEnd_1551026 : Nat := 4983230072969 + 3 ^ 40 * 1551026 * 2
def baseEnd_1551026 : Nat := 796421845620553837341967

theorem tailTrace_1551026 : CollatzResearch.WordTrace tailWord_1551026 prefixEnd_1551026 796421845620553837341967 := by
  unfold tailWord_1551026
  simp only [CollatzResearch.WordTrace]
  refine ⟨14142641419726292749152233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37713710452603447331072621 14142641419726292749152233)
  ·
    refine ⟨10606981064794719561864175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14142641419726292749152233 10606981064794719561864175)
    ·
      refine ⟨15910471597192079342796263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10606981064794719561864175 15910471597192079342796263)
      ·
        refine ⟨23865707395788119014194395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15910471597192079342796263 23865707395788119014194395)
        ·
          refine ⟨35798561093682178521291593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23865707395788119014194395 35798561093682178521291593)
          ·
            refine ⟨26848920820261633890968695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35798561093682178521291593 26848920820261633890968695)
            ·
              refine ⟨40273381230392450836453043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26848920820261633890968695 40273381230392450836453043)
              ·
                refine ⟨60410071845588676254679565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40273381230392450836453043 60410071845588676254679565)
                ·
                  refine ⟨22653776942095753595504837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60410071845588676254679565 22653776942095753595504837)
                  ·
                    refine ⟨4247583176642953799157157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22653776942095753595504837 4247583176642953799157157)
                    ·
                      refine ⟨796421845620553837341967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4247583176642953799157157 796421845620553837341967)
                      ·
                        rfl

theorem cell23_1551026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_1551026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551026 prefixEnd_1551026 := by exact prefixLift 1551026
  have htrace : WordTrace (prefixWord ++ tailWord_1551026) baseStart_1551026 baseEnd_1551026 := by
    simpa [prefixWord, tailWord_1551026, baseEnd_1551026] using wordTrace_append hprefix tailTrace_1551026
  have hstable : (prefixWord ++ tailWord_1551026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551026).length < 2 ^ (prefixWord ++ tailWord_1551026).sum := by decide
  have hdescent : baseEnd_1551026 < baseStart_1551026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551036 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 9]
def baseStart_1551036 : Nat := 118140960795 + 1551036 * 2 ^ 59
def prefixEnd_1551036 : Nat := 4983230072969 + 3 ^ 40 * 1551036 * 2
def baseEnd_1551036 : Nat := 88491886714122088690769

theorem tailTrace_1551036 : CollatzResearch.WordTrace tailWord_1551036 prefixEnd_1551036 88491886714122088690769 := by
  unfold tailWord_1551036
  simp only [CollatzResearch.WordTrace]
  refine ⟨28285465204434471352236481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37713953605912628469648641 28285465204434471352236481)
  ·
    refine ⟨21214098903325853514177361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28285465204434471352236481 21214098903325853514177361)
    ·
      refine ⟨15910574177494390135633021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21214098903325853514177361 15910574177494390135633021)
      ·
        refine ⟨5966465316560396300862383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15910574177494390135633021 5966465316560396300862383)
        ·
          refine ⟨8949697974840594451293575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5966465316560396300862383 8949697974840594451293575)
          ·
            refine ⟨13424546962260891676940363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8949697974840594451293575 13424546962260891676940363)
            ·
              refine ⟨20136820443391337515410545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13424546962260891676940363 20136820443391337515410545)
              ·
                refine ⟨15102615332543503136557909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20136820443391337515410545 15102615332543503136557909)
                ·
                  refine ⟨88491886714122088690769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15102615332543503136557909 88491886714122088690769)
                  ·
                    rfl

theorem cell23_1551036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 9].length) (baseStart_1551036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551036 prefixEnd_1551036 := by exact prefixLift 1551036
  have htrace : WordTrace (prefixWord ++ tailWord_1551036) baseStart_1551036 baseEnd_1551036 := by
    simpa [prefixWord, tailWord_1551036, baseEnd_1551036] using wordTrace_append hprefix tailTrace_1551036
  have hstable : (prefixWord ++ tailWord_1551036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551036).length < 2 ^ (prefixWord ++ tailWord_1551036).sum := by decide
  have hdescent : baseEnd_1551036 < baseStart_1551036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551041 : List Nat := [1, 2, 6, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1551041 : Nat := 118140960795 + 1551041 * 2 ^ 59
def prefixEnd_1551041 : Nat := 4983230072969 + 3 ^ 40 * 1551041 * 2
def baseEnd_1551041 : Nat := 796429547830371278654399

theorem tailTrace_1551041 : CollatzResearch.WordTrace tailWord_1551041 prefixEnd_1551041 796429547830371278654399 := by
  unfold tailWord_1551041
  simp only [CollatzResearch.WordTrace]
  refine ⟨56571112773850828558404977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37714075182567219038936651 56571112773850828558404977)
  ·
    refine ⟨42428334580388121418803733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56571112773850828558404977 42428334580388121418803733)
    ·
      refine ⟨1988828183455693191506425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42428334580388121418803733 1988828183455693191506425)
      ·
        refine ⟨1491621137591769893629819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1988828183455693191506425 1491621137591769893629819)
        ·
          refine ⟨2237431706387654840444729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1491621137591769893629819 2237431706387654840444729)
          ·
            refine ⟨1678073779790741130333547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2237431706387654840444729 1678073779790741130333547)
            ·
              refine ⟨2517110669686111695500321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678073779790741130333547 2517110669686111695500321)
              ·
                refine ⟨1887833002264583771625241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2517110669686111695500321 1887833002264583771625241)
                ·
                  refine ⟨1415874751698437828718931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1887833002264583771625241 1415874751698437828718931)
                  ·
                    refine ⟨2123812127547656743078397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1415874751698437828718931 2123812127547656743078397)
                    ·
                      refine ⟨796429547830371278654399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2123812127547656743078397 796429547830371278654399)
                      ·
                        rfl

theorem cell23_1551041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1551041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551041 prefixEnd_1551041 := by exact prefixLift 1551041
  have htrace : WordTrace (prefixWord ++ tailWord_1551041) baseStart_1551041 baseEnd_1551041 := by
    simpa [prefixWord, tailWord_1551041, baseEnd_1551041] using wordTrace_append hprefix tailTrace_1551041
  have hstable : (prefixWord ++ tailWord_1551041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551041).length < 2 ^ (prefixWord ++ tailWord_1551041).sum := by decide
  have hdescent : baseEnd_1551041 < baseStart_1551041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551063 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 3]
def baseStart_1551063 : Nat := 118140960795 + 1551063 * 2 ^ 59
def prefixEnd_1551063 : Nat := 4983230072969 + 3 ^ 40 * 1551063 * 2
def baseEnd_1551063 : Nat := 796440844404770192579297

theorem tailTrace_1551063 : CollatzResearch.WordTrace tailWord_1551063 prefixEnd_1551063 796440844404770192579297 := by
  unfold tailWord_1551063
  simp only [CollatzResearch.WordTrace]
  refine ⟨56571915179771126315705843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37714610119847417543803895 56571915179771126315705843)
  ·
    refine ⟨84857872769656689473558765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56571915179771126315705843 84857872769656689473558765)
    ·
      refine ⟨31821702288621258552584537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84857872769656689473558765 31821702288621258552584537)
      ·
        refine ⟨23866276716465943914438403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31821702288621258552584537 23866276716465943914438403)
        ·
          refine ⟨35799415074698915871657605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23866276716465943914438403 35799415074698915871657605)
          ·
            refine ⟨6712390326506046725935801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35799415074698915871657605 6712390326506046725935801)
            ·
              refine ⟨5034292744879535044451851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6712390326506046725935801 5034292744879535044451851)
              ·
                refine ⟨7551439117319302566677777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5034292744879535044451851 7551439117319302566677777)
                ·
                  refine ⟨5663579337989476925008333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7551439117319302566677777 5663579337989476925008333)
                  ·
                    refine ⟨2123842251746053846878125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5663579337989476925008333 2123842251746053846878125)
                    ·
                      refine ⟨796440844404770192579297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2123842251746053846878125 796440844404770192579297)
                      ·
                        rfl

theorem cell23_1551063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_1551063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551063 prefixEnd_1551063 := by exact prefixLift 1551063
  have htrace : WordTrace (prefixWord ++ tailWord_1551063) baseStart_1551063 baseEnd_1551063 := by
    simpa [prefixWord, tailWord_1551063, baseEnd_1551063] using wordTrace_append hprefix tailTrace_1551063
  have hstable : (prefixWord ++ tailWord_1551063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551063).length < 2 ^ (prefixWord ++ tailWord_1551063).sum := by decide
  have hdescent : baseEnd_1551063 < baseStart_1551063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551064 : List Nat := [2, 1, 2, 2, 3, 3, 3, 1, 2, 2, 2]
def baseStart_1551064 : Nat := 118140960795 + 1551064 * 2 ^ 59
def prefixEnd_1551064 : Nat := 4983230072969 + 3 ^ 40 * 1551064 * 2
def baseEnd_1551064 : Nat := 796441357885424688666793

theorem tailTrace_1551064 : CollatzResearch.WordTrace tailWord_1551064 prefixEnd_1551064 796441357885424688666793 := by
  unfold tailWord_1551064
  simp only [CollatzResearch.WordTrace]
  refine ⟨28285975826383751743246123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37714634435178335657661497 28285975826383751743246123)
  ·
    refine ⟨42428963739575627614869185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28285975826383751743246123 42428963739575627614869185)
    ·
      refine ⟨31821722804681720711151889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42428963739575627614869185 31821722804681720711151889)
      ·
        refine ⟨23866292103511290533363917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31821722804681720711151889 23866292103511290533363917)
        ·
          refine ⟨8949859538816733950011469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23866292103511290533363917 8949859538816733950011469)
          ·
            refine ⟨3356197327056275231254301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8949859538816733950011469 3356197327056275231254301)
            ·
              refine ⟨1258573997646103211720363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3356197327056275231254301 1258573997646103211720363)
              ·
                refine ⟨1887860996469154817580545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1258573997646103211720363 1887860996469154817580545)
                ·
                  refine ⟨1415895747351866113185409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1887860996469154817580545 1415895747351866113185409)
                  ·
                    refine ⟨1061921810513899584889057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1415895747351866113185409 1061921810513899584889057)
                    ·
                      refine ⟨796441357885424688666793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1061921810513899584889057 796441357885424688666793)
                      ·
                        rfl

theorem cell23_1551064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_1551064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551064 prefixEnd_1551064 := by exact prefixLift 1551064
  have htrace : WordTrace (prefixWord ++ tailWord_1551064) baseStart_1551064 baseEnd_1551064 := by
    simpa [prefixWord, tailWord_1551064, baseEnd_1551064] using wordTrace_append hprefix tailTrace_1551064
  have hstable : (prefixWord ++ tailWord_1551064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551064).length < 2 ^ (prefixWord ++ tailWord_1551064).sum := by decide
  have hdescent : baseEnd_1551064 < baseStart_1551064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551066 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 3, 7]
def baseStart_1551066 : Nat := 118140960795 + 1551066 * 2 ^ 59
def prefixEnd_1551066 : Nat := 4983230072969 + 3 ^ 40 * 1551066 * 2
def baseEnd_1551066 : Nat := 265480794948911226947261

theorem tailTrace_1551066 : CollatzResearch.WordTrace tailWord_1551066 prefixEnd_1551066 265480794948911226947261 := by
  unfold tailWord_1551066
  simp only [CollatzResearch.WordTrace]
  refine ⟨14143006149690064457016263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37714683065840171885376701 14143006149690064457016263)
  ·
    refine ⟨21214509224535096685524395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14143006149690064457016263 21214509224535096685524395)
    ·
      refine ⟨31821763836802645028286593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21214509224535096685524395 31821763836802645028286593)
      ·
        refine ⟨23866322877601983771214945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31821763836802645028286593 23866322877601983771214945)
        ·
          refine ⟨17899742158201487828411209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23866322877601983771214945 17899742158201487828411209)
          ·
            refine ⟨13424806618651115871308407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17899742158201487828411209 13424806618651115871308407)
            ·
              refine ⟨20137209927976673806962611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13424806618651115871308407 20137209927976673806962611)
              ·
                refine ⟨30205814891965010710443917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20137209927976673806962611 30205814891965010710443917)
                ·
                  refine ⟨11327180584486879016416469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30205814891965010710443917 11327180584486879016416469)
                  ·
                    refine ⟨265480794948911226947261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11327180584486879016416469 265480794948911226947261)
                    ·
                      rfl

theorem cell23_1551066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_1551066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551066 prefixEnd_1551066 := by exact prefixLift 1551066
  have htrace : WordTrace (prefixWord ++ tailWord_1551066) baseStart_1551066 baseEnd_1551066 := by
    simpa [prefixWord, tailWord_1551066, baseEnd_1551066] using wordTrace_append hprefix tailTrace_1551066
  have hstable : (prefixWord ++ tailWord_1551066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551066).length < 2 ^ (prefixWord ++ tailWord_1551066).sum := by decide
  have hdescent : baseEnd_1551066 < baseStart_1551066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551123 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 3]
def baseStart_1551123 : Nat := 118140960795 + 1551123 * 2 ^ 59
def prefixEnd_1551123 : Nat := 4983230072969 + 3 ^ 40 * 1551123 * 2
def baseEnd_1551123 : Nat := 796471653244039957829021

theorem tailTrace_1551123 : CollatzResearch.WordTrace tailWord_1551123 prefixEnd_1551123 796471653244039957829021 := by
  unfold tailWord_1551123
  simp only [CollatzResearch.WordTrace]
  refine ⟨56574103559553756562890023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37716069039702504375260015 56574103559553756562890023)
  ·
    refine ⟨84861155339330634844335035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56574103559553756562890023 84861155339330634844335035)
    ·
      refine ⟨127291733008995952266502553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84861155339330634844335035 127291733008995952266502553)
      ·
        refine ⟨95468799756746964199876915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127291733008995952266502553 95468799756746964199876915)
        ·
          refine ⟨143203199635120446299815373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95468799756746964199876915 143203199635120446299815373)
          ·
            refine ⟨53701199863170167362430765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143203199635120446299815373 53701199863170167362430765)
            ·
              refine ⟨20137949948688812760911537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53701199863170167362430765 20137949948688812760911537)
              ·
                refine ⟨15103462461516609570683653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20137949948688812760911537 15103462461516609570683653)
                ·
                  refine ⟨2831899211534364294503185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15103462461516609570683653 2831899211534364294503185)
                  ·
                    refine ⟨2123924408650773220877389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2831899211534364294503185 2123924408650773220877389)
                    ·
                      refine ⟨796471653244039957829021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2123924408650773220877389 796471653244039957829021)
                      ·
                        rfl

theorem cell23_1551123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 3].length) (baseStart_1551123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551123 prefixEnd_1551123 := by exact prefixLift 1551123
  have htrace : WordTrace (prefixWord ++ tailWord_1551123) baseStart_1551123 baseEnd_1551123 := by
    simpa [prefixWord, tailWord_1551123, baseEnd_1551123] using wordTrace_append hprefix tailTrace_1551123
  have hstable : (prefixWord ++ tailWord_1551123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551123).length < 2 ^ (prefixWord ++ tailWord_1551123).sum := by decide
  have hdescent : baseEnd_1551123 < baseStart_1551123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551204 : List Nat := [2, 3, 1, 1, 4, 1, 1, 5, 1, 1, 3]
def baseStart_1551204 : Nat := 118140960795 + 1551204 * 2 ^ 59
def prefixEnd_1551204 : Nat := 4983230072969 + 3 ^ 40 * 1551204 * 2
def baseEnd_1551204 : Nat := 796513245177054140916149

theorem tailTrace_1551204 : CollatzResearch.WordTrace tailWord_1551204 prefixEnd_1551204 796513245177054140916149 := by
  unfold tailWord_1551204
  simp only [CollatzResearch.WordTrace]
  refine ⟨28288528936130153698294333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37718038581506871597725777 28288528936130153698294333)
  ·
    refine ⟨10608198351048807636860375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28288528936130153698294333 10608198351048807636860375)
    ·
      refine ⟨15912297526573211455290563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10608198351048807636860375 15912297526573211455290563)
      ·
        refine ⟨23868446289859817182935845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15912297526573211455290563 23868446289859817182935845)
        ·
          refine ⟨4475333679348715721800471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23868446289859817182935845 4475333679348715721800471)
          ·
            refine ⟨6713000519023073582700707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4475333679348715721800471 6713000519023073582700707)
            ·
              refine ⟨10069500778534610374051061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6713000519023073582700707 10069500778534610374051061)
              ·
                refine ⟨944015697987619722567287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10069500778534610374051061 944015697987619722567287)
                ·
                  refine ⟨1416023546981429583850931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 944015697987619722567287 1416023546981429583850931)
                  ·
                    refine ⟨2124035320472144375776397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1416023546981429583850931 2124035320472144375776397)
                    ·
                      refine ⟨796513245177054140916149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2124035320472144375776397 796513245177054140916149)
                      ·
                        rfl

theorem cell23_1551204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 1, 1, 3].length) (baseStart_1551204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551204 prefixEnd_1551204 := by exact prefixLift 1551204
  have htrace : WordTrace (prefixWord ++ tailWord_1551204) baseStart_1551204 baseEnd_1551204 := by
    simpa [prefixWord, tailWord_1551204, baseEnd_1551204] using wordTrace_append hprefix tailTrace_1551204
  have hstable : (prefixWord ++ tailWord_1551204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551204).length < 2 ^ (prefixWord ++ tailWord_1551204).sum := by decide
  have hdescent : baseEnd_1551204 < baseStart_1551204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551207 : List Nat := [1, 1, 5, 1, 2, 2, 4, 1, 1, 5]
def baseStart_1551207 : Nat := 118140960795 + 1551207 * 2 ^ 59
def prefixEnd_1551207 : Nat := 4983230072969 + 3 ^ 40 * 1551207 * 2
def baseEnd_1551207 : Nat := 265504928539672543059545

theorem tailTrace_1551207 : CollatzResearch.WordTrace tailWord_1551207 prefixEnd_1551207 265504928539672543059545 := by
  unfold tailWord_1551207
  simp only [CollatzResearch.WordTrace]
  refine ⟨56577167291249438908947875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37718111527499625939298583 56577167291249438908947875)
  ·
    refine ⟨84865750936874158363421813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56577167291249438908947875 84865750936874158363421813)
    ·
      refine ⟨7956164150331952346570795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84865750936874158363421813 7956164150331952346570795)
      ·
        refine ⟨11934246225497928519856193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7956164150331952346570795 11934246225497928519856193)
        ·
          refine ⟨8950684669123446389892145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11934246225497928519856193 8950684669123446389892145)
          ·
            refine ⟨6713013501842584792419109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8950684669123446389892145 6713013501842584792419109)
            ·
              refine ⟨1258690031595484648578583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6713013501842584792419109 1258690031595484648578583)
              ·
                refine ⟨1888035047393226972867875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1258690031595484648578583 1888035047393226972867875)
                ·
                  refine ⟨2832052571089840459301813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888035047393226972867875 2832052571089840459301813)
                  ·
                    refine ⟨265504928539672543059545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2832052571089840459301813 265504928539672543059545)
                    ·
                      rfl

theorem cell23_1551207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_1551207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551207 prefixEnd_1551207 := by exact prefixLift 1551207
  have htrace : WordTrace (prefixWord ++ tailWord_1551207) baseStart_1551207 baseEnd_1551207 := by
    simpa [prefixWord, tailWord_1551207, baseEnd_1551207] using wordTrace_append hprefix tailTrace_1551207
  have hstable : (prefixWord ++ tailWord_1551207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551207).length < 2 ^ (prefixWord ++ tailWord_1551207).sum := by decide
  have hdescent : baseEnd_1551207 < baseStart_1551207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551223 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 4]
def baseStart_1551223 : Nat := 118140960795 + 1551223 * 2 ^ 59
def prefixEnd_1551223 : Nat := 4983230072969 + 3 ^ 40 * 1551223 * 2
def baseEnd_1551223 : Nat := 796523001309489566578561

theorem tailTrace_1551223 : CollatzResearch.WordTrace tailWord_1551223 prefixEnd_1551223 796523001309489566578561 := by
  unfold tailWord_1551223
  simp only [CollatzResearch.WordTrace]
  refine ⟨56577750859191473641530323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37718500572794315761020215 56577750859191473641530323)
  ·
    refine ⟨84866626288787210462295485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56577750859191473641530323 84866626288787210462295485)
    ·
      refine ⟨31824984858295203923360807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84866626288787210462295485 31824984858295203923360807)
      ·
        refine ⟨47737477287442805885041211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31824984858295203923360807 47737477287442805885041211)
        ·
          refine ⟨71606215931164208827561817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47737477287442805885041211 71606215931164208827561817)
          ·
            refine ⟨53704661948373156620671363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71606215931164208827561817 53704661948373156620671363)
            ·
              refine ⟨80556992922559734931007045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53704661948373156620671363 80556992922559734931007045)
              ·
                refine ⟨15104436172979950299563821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80556992922559734931007045 15104436172979950299563821)
                ·
                  refine ⟨5664163564867481362336433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15104436172979950299563821 5664163564867481362336433)
                  ·
                    refine ⟨4248122673650611021752325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5664163564867481362336433 4248122673650611021752325)
                    ·
                      refine ⟨796523001309489566578561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4248122673650611021752325 796523001309489566578561)
                      ·
                        rfl

theorem cell23_1551223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_1551223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551223 prefixEnd_1551223 := by exact prefixLift 1551223
  have htrace : WordTrace (prefixWord ++ tailWord_1551223) baseStart_1551223 baseEnd_1551223 := by
    simpa [prefixWord, tailWord_1551223, baseEnd_1551223] using wordTrace_append hprefix tailTrace_1551223
  have hstable : (prefixWord ++ tailWord_1551223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551223).length < 2 ^ (prefixWord ++ tailWord_1551223).sum := by decide
  have hdescent : baseEnd_1551223 < baseStart_1551223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551227 : List Nat := [1, 1, 1, 1, 1, 5, 3, 3, 3, 2, 2]
def baseStart_1551227 : Nat := 118140960795 + 1551227 * 2 ^ 59
def prefixEnd_1551227 : Nat := 4983230072969 + 3 ^ 40 * 1551227 * 2
def baseEnd_1551227 : Nat := 796525055232107550928543

theorem tailTrace_1551227 : CollatzResearch.WordTrace tailWord_1551227 prefixEnd_1551227 796525055232107550928543 := by
  unfold tailWord_1551227
  simp only [CollatzResearch.WordTrace]
  refine ⟨56577896751176982324675935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37718597834117988216450623 56577896751176982324675935)
  ·
    refine ⟨84866845126765473487013903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56577896751176982324675935 84866845126765473487013903)
    ·
      refine ⟨127300267690148210230520855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84866845126765473487013903 127300267690148210230520855)
      ·
        refine ⟨190950401535222315345781283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127300267690148210230520855 190950401535222315345781283)
        ·
          refine ⟨286425602302833473018671925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190950401535222315345781283 286425602302833473018671925)
          ·
            refine ⟨26852400215890638095500493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 286425602302833473018671925 26852400215890638095500493)
            ·
              refine ⟨10069650080958989285812685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26852400215890638095500493 10069650080958989285812685)
              ·
                refine ⟨3776118780359620982179757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10069650080958989285812685 3776118780359620982179757)
                ·
                  refine ⟨1416044542634857868317409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3776118780359620982179757 1416044542634857868317409)
                  ·
                    refine ⟨1062033406976143401238057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1416044542634857868317409 1062033406976143401238057)
                    ·
                      refine ⟨796525055232107550928543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1062033406976143401238057 796525055232107550928543)
                      ·
                        rfl

theorem cell23_1551227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 2, 2].length) (baseStart_1551227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551227 prefixEnd_1551227 := by exact prefixLift 1551227
  have htrace : WordTrace (prefixWord ++ tailWord_1551227) baseStart_1551227 baseEnd_1551227 := by
    simpa [prefixWord, tailWord_1551227, baseEnd_1551227] using wordTrace_append hprefix tailTrace_1551227
  have hstable : (prefixWord ++ tailWord_1551227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551227).length < 2 ^ (prefixWord ++ tailWord_1551227).sum := by decide
  have hdescent : baseEnd_1551227 < baseStart_1551227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551240 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_1551240 : Nat := 118140960795 + 1551240 * 2 ^ 59
def prefixEnd_1551240 : Nat := 4983230072969 + 3 ^ 40 * 1551240 * 2
def baseEnd_1551240 : Nat := 796531730480616000065983

theorem tailTrace_1551240 : CollatzResearch.WordTrace tailWord_1551240 prefixEnd_1551240 796531730480616000065983 := by
  unfold tailWord_1551240
  simp only [CollatzResearch.WordTrace]
  refine ⟨28289185450064942772449587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37718913933419923696599449 28289185450064942772449587)
  ·
    refine ⟨42433778175097414158674381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28289185450064942772449587 42433778175097414158674381)
    ·
      refine ⟨15912666815661530309502893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42433778175097414158674381 15912666815661530309502893)
      ·
        refine ⟨5967250055873073866063585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15912666815661530309502893 5967250055873073866063585)
        ·
          refine ⟨4475437541904805399547689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5967250055873073866063585 4475437541904805399547689)
          ·
            refine ⟨3356578156428604049660767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4475437541904805399547689 3356578156428604049660767)
            ·
              refine ⟨5034867234642906074491151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3356578156428604049660767 5034867234642906074491151)
              ·
                refine ⟨7552300851964359111736727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5034867234642906074491151 7552300851964359111736727)
                ·
                  refine ⟨11328451277946538667605091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7552300851964359111736727 11328451277946538667605091)
                  ·
                    refine ⟨16992676916919808001407637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11328451277946538667605091 16992676916919808001407637)
                    ·
                      refine ⟨796531730480616000065983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16992676916919808001407637 796531730480616000065983)
                      ·
                        rfl

theorem cell23_1551240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_1551240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551240 prefixEnd_1551240 := by exact prefixLift 1551240
  have htrace : WordTrace (prefixWord ++ tailWord_1551240) baseStart_1551240 baseEnd_1551240 := by
    simpa [prefixWord, tailWord_1551240, baseEnd_1551240] using wordTrace_append hprefix tailTrace_1551240
  have hstable : (prefixWord ++ tailWord_1551240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551240).length < 2 ^ (prefixWord ++ tailWord_1551240).sum := by decide
  have hdescent : baseEnd_1551240 < baseStart_1551240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551273 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 2, 2, 5]
def baseStart_1551273 : Nat := 118140960795 + 1551273 * 2 ^ 59
def prefixEnd_1551273 : Nat := 4983230072969 + 3 ^ 40 * 1551273 * 2
def baseEnd_1551273 : Nat := 796548675342214370953331

theorem tailTrace_1551273 : CollatzResearch.WordTrace tailWord_1551273 prefixEnd_1551273 796548675342214370953331 := by
  unfold tailWord_1551273
  simp only [CollatzResearch.WordTrace]
  refine ⟨56579574509010332180850473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37719716339340221453900315 56579574509010332180850473)
  ·
    refine ⟨42434680881757749135637855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56579574509010332180850473 42434680881757749135637855)
    ·
      refine ⟨63652021322636623703456783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42434680881757749135637855 63652021322636623703456783)
      ·
        refine ⟨95478031983954935555185175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63652021322636623703456783 95478031983954935555185175)
        ·
          refine ⟨143217047975932403332777763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95478031983954935555185175 143217047975932403332777763)
          ·
            refine ⟨214825571963898604999166645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143217047975932403332777763 214825571963898604999166645)
            ·
              refine ⟨20139897371615494218671873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 214825571963898604999166645 20139897371615494218671873)
              ·
                refine ⟨15104923028711620664003905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20139897371615494218671873 15104923028711620664003905)
                ·
                  refine ⟨11328692271533715498002929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15104923028711620664003905 11328692271533715498002929)
                  ·
                    refine ⟨8496519203650286623502197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11328692271533715498002929 8496519203650286623502197)
                    ·
                      refine ⟨796548675342214370953331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8496519203650286623502197 796548675342214370953331)
                      ·
                        rfl

theorem cell23_1551273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_1551273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551273 prefixEnd_1551273 := by exact prefixLift 1551273
  have htrace : WordTrace (prefixWord ++ tailWord_1551273) baseStart_1551273 baseEnd_1551273 := by
    simpa [prefixWord, tailWord_1551273, baseEnd_1551273] using wordTrace_append hprefix tailTrace_1551273
  have hstable : (prefixWord ++ tailWord_1551273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551273).length < 2 ^ (prefixWord ++ tailWord_1551273).sum := by decide
  have hdescent : baseEnd_1551273 < baseStart_1551273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551294 : List Nat := [4, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_1551294 : Nat := 118140960795 + 1551294 * 2 ^ 59
def prefixEnd_1551294 : Nat := 4983230072969 + 3 ^ 40 * 1551294 * 2
def baseEnd_1551294 : Nat := 796559458435958788790735

theorem tailTrace_1551294 : CollatzResearch.WordTrace tailWord_1551294 prefixEnd_1551294 796559458435958788790735 := by
  unfold tailWord_1551294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7072542555241781595920617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37720226961289501844909957 7072542555241781595920617)
  ·
    refine ⟨5304406916431336196940463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7072542555241781595920617 5304406916431336196940463)
    ·
      refine ⟨7956610374647004295410695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5304406916431336196940463 7956610374647004295410695)
      ·
        refine ⟨11934915561970506443116043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7956610374647004295410695 11934915561970506443116043)
        ·
          refine ⟨17902373342955759664674065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11934915561970506443116043 17902373342955759664674065)
          ·
            refine ⟨13426780007216819748505549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17902373342955759664674065 13426780007216819748505549)
            ·
              refine ⟨5035042502706307405689581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13426780007216819748505549 5035042502706307405689581)
              ·
                refine ⟨1888140938514865277133593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5035042502706307405689581 1888140938514865277133593)
                ·
                  refine ⟨1416105703886148957850195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1888140938514865277133593 1416105703886148957850195)
                  ·
                    refine ⟨2124158555829223436775293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1416105703886148957850195 2124158555829223436775293)
                    ·
                      refine ⟨796559458435958788790735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2124158555829223436775293 796559458435958788790735)
                      ·
                        rfl

theorem cell23_1551294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_1551294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551294 prefixEnd_1551294 := by exact prefixLift 1551294
  have htrace : WordTrace (prefixWord ++ tailWord_1551294) baseStart_1551294 baseEnd_1551294 := by
    simpa [prefixWord, tailWord_1551294, baseEnd_1551294] using wordTrace_append hprefix tailTrace_1551294
  have hstable : (prefixWord ++ tailWord_1551294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551294).length < 2 ^ (prefixWord ++ tailWord_1551294).sum := by decide
  have hdescent : baseEnd_1551294 < baseStart_1551294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551304 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 3, 3, 2]
def baseStart_1551304 : Nat := 118140960795 + 1551304 * 2 ^ 59
def prefixEnd_1551304 : Nat := 4983230072969 + 3 ^ 40 * 1551304 * 2
def baseEnd_1551304 : Nat := 796564593242503749665689

theorem tailTrace_1551304 : CollatzResearch.WordTrace tailWord_1551304 prefixEnd_1551304 796564593242503749665689 := by
  unfold tailWord_1551304
  simp only [CollatzResearch.WordTrace]
  refine ⟨28290352585949012237614483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37720470114598682983485977 28290352585949012237614483)
  ·
    refine ⟨42435528878923518356421725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28290352585949012237614483 42435528878923518356421725)
    ·
      refine ⟨15913323329596319383658147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42435528878923518356421725 15913323329596319383658147)
      ·
        refine ⟨23869984994394479075487221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15913323329596319383658147 23869984994394479075487221)
        ·
          refine ⟨2237811093224482413326927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23869984994394479075487221 2237811093224482413326927)
          ·
            refine ⟨3356716639836723619990391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2237811093224482413326927 3356716639836723619990391)
            ·
              refine ⟨5035074959755085429985587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3356716639836723619990391 5035074959755085429985587)
              ·
                refine ⟨7552612439632628144978381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5035074959755085429985587 7552612439632628144978381)
                ·
                  refine ⟨2832229664862235554366893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7552612439632628144978381 2832229664862235554366893)
                  ·
                    refine ⟨1062086124323338332887585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2832229664862235554366893 1062086124323338332887585)
                    ·
                      refine ⟨796564593242503749665689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1062086124323338332887585 796564593242503749665689)
                      ·
                        rfl

theorem cell23_1551304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_1551304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551304 prefixEnd_1551304 := by exact prefixLift 1551304
  have htrace : WordTrace (prefixWord ++ tailWord_1551304) baseStart_1551304 baseEnd_1551304 := by
    simpa [prefixWord, tailWord_1551304, baseEnd_1551304] using wordTrace_append hprefix tailTrace_1551304
  have hstable : (prefixWord ++ tailWord_1551304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551304).length < 2 ^ (prefixWord ++ tailWord_1551304).sum := by decide
  have hdescent : baseEnd_1551304 < baseStart_1551304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551320 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 2, 1, 5]
def baseStart_1551320 : Nat := 118140960795 + 1551320 * 2 ^ 59
def prefixEnd_1551320 : Nat := 4983230072969 + 3 ^ 40 * 1551320 * 2
def baseEnd_1551320 : Nat := 796572808932975687065615

theorem tailTrace_1551320 : CollatzResearch.WordTrace tailWord_1551320 prefixEnd_1551320 796572808932975687065615 := by
  unfold tailWord_1551320
  simp only [CollatzResearch.WordTrace]
  refine ⟨28290644369920029603905707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37720859159893372805207609 28290644369920029603905707)
  ·
    refine ⟨42435966554880044405858561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28290644369920029603905707 42435966554880044405858561)
    ·
      refine ⟨31826974916160033304393921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42435966554880044405858561 31826974916160033304393921)
      ·
        refine ⟨23870231187120024978295441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31826974916160033304393921 23870231187120024978295441)
        ·
          refine ⟨17902673390340018733721581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23870231187120024978295441 17902673390340018733721581)
          ·
            refine ⟨6713502521377507025145593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17902673390340018733721581 6713502521377507025145593)
            ·
              refine ⟨5035126891033130268859195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6713502521377507025145593 5035126891033130268859195)
              ·
                refine ⟨7552690336549695403288793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5035126891033130268859195 7552690336549695403288793)
                ·
                  refine ⟨5664517752412271552466595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7552690336549695403288793 5664517752412271552466595)
                  ·
                    refine ⟨8496776628618407328699893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5664517752412271552466595 8496776628618407328699893)
                    ·
                      refine ⟨796572808932975687065615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8496776628618407328699893 796572808932975687065615)
                      ·
                        rfl

theorem cell23_1551320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_1551320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551320 prefixEnd_1551320 := by exact prefixLift 1551320
  have htrace : WordTrace (prefixWord ++ tailWord_1551320) baseStart_1551320 baseEnd_1551320 := by
    simpa [prefixWord, tailWord_1551320, baseEnd_1551320] using wordTrace_append hprefix tailTrace_1551320
  have hstable : (prefixWord ++ tailWord_1551320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551320).length < 2 ^ (prefixWord ++ tailWord_1551320).sum := by decide
  have hdescent : baseEnd_1551320 < baseStart_1551320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551321 : List Nat := [1, 2, 1, 2, 5, 2, 3, 1, 1, 3, 2]
def baseStart_1551321 : Nat := 118140960795 + 1551321 * 2 ^ 59
def prefixEnd_1551321 : Nat := 4983230072969 + 3 ^ 40 * 1551321 * 2
def baseEnd_1551321 : Nat := 796573322413630183153111

theorem tailTrace_1551321 : CollatzResearch.WordTrace tailWord_1551321 prefixEnd_1551321 796573322413630183153111 := by
  unfold tailWord_1551321
  simp only [CollatzResearch.WordTrace]
  refine ⟨56581325212836436378597817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37720883475224290919065211 56581325212836436378597817)
  ·
    refine ⟨42435993909627327283948363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56581325212836436378597817 42435993909627327283948363)
    ·
      refine ⟨63653990864440990925922545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42435993909627327283948363 63653990864440990925922545)
      ·
        refine ⟨47740493148330743194441909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63653990864440990925922545 47740493148330743194441909)
        ·
          refine ⟨4475671232656007174478929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47740493148330743194441909 4475671232656007174478929)
          ·
            refine ⟨3356753424492005380859197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4475671232656007174478929 3356753424492005380859197)
            ·
              refine ⟨1258782534184502017822199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3356753424492005380859197 1258782534184502017822199)
              ·
                refine ⟨1888173801276753026733299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1258782534184502017822199 1888173801276753026733299)
                ·
                  refine ⟨2832260701915129540099949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888173801276753026733299 2832260701915129540099949)
                  ·
                    refine ⟨1062097763218173577537481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2832260701915129540099949 1062097763218173577537481)
                    ·
                      refine ⟨796573322413630183153111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1062097763218173577537481 796573322413630183153111)
                      ·
                        rfl

theorem cell23_1551321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 1, 3, 2].length) (baseStart_1551321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551321 prefixEnd_1551321 := by exact prefixLift 1551321
  have htrace : WordTrace (prefixWord ++ tailWord_1551321) baseStart_1551321 baseEnd_1551321 := by
    simpa [prefixWord, tailWord_1551321, baseEnd_1551321] using wordTrace_append hprefix tailTrace_1551321
  have hstable : (prefixWord ++ tailWord_1551321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551321).length < 2 ^ (prefixWord ++ tailWord_1551321).sum := by decide
  have hdescent : baseEnd_1551321 < baseStart_1551321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551374 : List Nat := [4, 1, 1, 2, 2, 3, 2, 3, 5]
def baseStart_1551374 : Nat := 118140960795 + 1551374 * 2 ^ 59
def prefixEnd_1551374 : Nat := 4983230072969 + 3 ^ 40 * 1551374 * 2
def baseEnd_1551374 : Nat := 88511170765368719532263

theorem tailTrace_1551374 : CollatzResearch.WordTrace tailWord_1551374 prefixEnd_1551374 88511170765368719532263 := by
  unfold tailWord_1551374
  simp only [CollatzResearch.WordTrace]
  refine ⟨7072907285205553303784647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37722172187762950953518117 7072907285205553303784647)
  ·
    refine ⟨10609360927808329955676971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7072907285205553303784647 10609360927808329955676971)
    ·
      refine ⟨15914041391712494933515457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10609360927808329955676971 15914041391712494933515457)
      ·
        refine ⟨11935531043784371200136593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15914041391712494933515457 11935531043784371200136593)
        ·
          refine ⟨8951648282838278400102445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11935531043784371200136593 8951648282838278400102445)
          ·
            refine ⟨3356868106064354400038417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8951648282838278400102445 3356868106064354400038417)
            ·
              refine ⟨2517651079548265800028813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3356868106064354400038417 2517651079548265800028813)
              ·
                refine ⟨944119154830599675010805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2517651079548265800028813 944119154830599675010805)
                ·
                  refine ⟨88511170765368719532263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 944119154830599675010805 88511170765368719532263)
                  ·
                    rfl

theorem cell23_1551374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_1551374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551374 prefixEnd_1551374 := by exact prefixLift 1551374
  have htrace : WordTrace (prefixWord ++ tailWord_1551374) baseStart_1551374 baseEnd_1551374 := by
    simpa [prefixWord, tailWord_1551374, baseEnd_1551374] using wordTrace_append hprefix tailTrace_1551374
  have hstable : (prefixWord ++ tailWord_1551374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551374).length < 2 ^ (prefixWord ++ tailWord_1551374).sum := by decide
  have hdescent : baseEnd_1551374 < baseStart_1551374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551427 : List Nat := [1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 3]
def baseStart_1551427 : Nat := 118140960795 + 1551427 * 2 ^ 59
def prefixEnd_1551427 : Nat := 4983230072969 + 3 ^ 40 * 1551427 * 2
def baseEnd_1551427 : Nat := 796627751363006768427623

theorem tailTrace_1551427 : CollatzResearch.WordTrace tailWord_1551427 prefixEnd_1551427 796627751363006768427623 := by
  unfold tailWord_1551427
  simp only [CollatzResearch.WordTrace]
  refine ⟨56585191350452416481956535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37723460900301610987971023 56585191350452416481956535)
  ·
    refine ⟨84877787025678624722934803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56585191350452416481956535 84877787025678624722934803)
    ·
      refine ⟨127316680538517937084402205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84877787025678624722934803 127316680538517937084402205)
      ·
        refine ⟨47743755201944226406650827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127316680538517937084402205 47743755201944226406650827)
        ·
          refine ⟨71615632802916339609976241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47743755201944226406650827 71615632802916339609976241)
          ·
            refine ⟨53711724602187254707482181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71615632802916339609976241 53711724602187254707482181)
            ·
              refine ⟨10070948362910110257652909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53711724602187254707482181 10070948362910110257652909)
              ·
                refine ⟨3776605636091291346619841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10070948362910110257652909 3776605636091291346619841)
                ·
                  refine ⟨2832454227068468509964881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3776605636091291346619841 2832454227068468509964881)
                  ·
                    refine ⟨2124340670301351382473661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2832454227068468509964881 2124340670301351382473661)
                    ·
                      refine ⟨796627751363006768427623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2124340670301351382473661 796627751363006768427623)
                      ·
                        rfl

theorem cell23_1551427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_1551427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551427 prefixEnd_1551427 := by exact prefixLift 1551427
  have htrace : WordTrace (prefixWord ++ tailWord_1551427) baseStart_1551427 baseEnd_1551427 := by
    simpa [prefixWord, tailWord_1551427, baseEnd_1551427] using wordTrace_append hprefix tailTrace_1551427
  have hstable : (prefixWord ++ tailWord_1551427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551427).length < 2 ^ (prefixWord ++ tailWord_1551427).sum := by decide
  have hdescent : baseEnd_1551427 < baseStart_1551427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551450 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6]
def baseStart_1551450 : Nat := 118140960795 + 1551450 * 2 ^ 59
def prefixEnd_1551450 : Nat := 4983230072969 + 3 ^ 40 * 1551450 * 2
def baseEnd_1551450 : Nat := 796639561418060178440017

theorem tailTrace_1551450 : CollatzResearch.WordTrace tailWord_1551450 prefixEnd_1551450 796639561418060178440017 := by
  unfold tailWord_1551450
  simp only [CollatzResearch.WordTrace]
  refine ⟨14146507557342272852510951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37724020152912727606695869 14146507557342272852510951)
  ·
    refine ⟨21219761336013409278766427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14146507557342272852510951 21219761336013409278766427)
    ·
      refine ⟨31829642004020113918149641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21219761336013409278766427 31829642004020113918149641)
      ·
        refine ⟨23872231503015085438612231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31829642004020113918149641 23872231503015085438612231)
        ·
          refine ⟨35808347254522628157918347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23872231503015085438612231 35808347254522628157918347)
          ·
            refine ⟨53712520881783942236877521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35808347254522628157918347 53712520881783942236877521)
            ·
              refine ⟨40284390661337956677658141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53712520881783942236877521 40284390661337956677658141)
              ·
                refine ⟨15106646498001733754121803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40284390661337956677658141 15106646498001733754121803)
                ·
                  refine ⟨22659969747002600631182705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15106646498001733754121803 22659969747002600631182705)
                  ·
                    refine ⟨16994977310251950473387029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22659969747002600631182705 16994977310251950473387029)
                    ·
                      refine ⟨796639561418060178440017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16994977310251950473387029 796639561418060178440017)
                      ·
                        rfl

theorem cell23_1551450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_1551450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551450 prefixEnd_1551450 := by exact prefixLift 1551450
  have htrace : WordTrace (prefixWord ++ tailWord_1551450) baseStart_1551450 baseEnd_1551450 := by
    simpa [prefixWord, tailWord_1551450, baseEnd_1551450] using wordTrace_append hprefix tailTrace_1551450
  have hstable : (prefixWord ++ tailWord_1551450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551450).length < 2 ^ (prefixWord ++ tailWord_1551450).sum := by decide
  have hdescent : baseEnd_1551450 < baseStart_1551450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551460 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 2, 9]
def baseStart_1551460 : Nat := 118140960795 + 1551460 * 2 ^ 59
def prefixEnd_1551460 : Nat := 4983230072969 + 3 ^ 40 * 1551460 * 2
def baseEnd_1551460 : Nat := 265548232074868379771657

theorem tailTrace_1551460 : CollatzResearch.WordTrace tailWord_1551460 prefixEnd_1551460 265548232074868379771657 := by
  unfold tailWord_1551460
  simp only [CollatzResearch.WordTrace]
  refine ⟨28293197479666431558953917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37724263306221908745271889 28293197479666431558953917)
  ·
    refine ⟨10609949054874911834607719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28293197479666431558953917 10609949054874911834607719)
    ·
      refine ⟨15914923582312367751911579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10609949054874911834607719 15914923582312367751911579)
      ·
        refine ⟨23872385373468551627867369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15914923582312367751911579 23872385373468551627867369)
        ·
          refine ⟨17904289030101413720900527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23872385373468551627867369 17904289030101413720900527)
          ·
            refine ⟨26856433545152120581350791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17904289030101413720900527 26856433545152120581350791)
            ·
              refine ⟨40284650317728180872026187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26856433545152120581350791 40284650317728180872026187)
              ·
                refine ⟨60426975476592271308039281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40284650317728180872026187 60426975476592271308039281)
                ·
                  refine ⟨45320231607444203481029461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60426975476592271308039281 45320231607444203481029461)
                  ·
                    refine ⟨265548232074868379771657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 45320231607444203481029461 265548232074868379771657)
                    ·
                      rfl

theorem cell23_1551460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_1551460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551460 prefixEnd_1551460 := by exact prefixLift 1551460
  have htrace : WordTrace (prefixWord ++ tailWord_1551460) baseStart_1551460 baseEnd_1551460 := by
    simpa [prefixWord, tailWord_1551460, baseEnd_1551460] using wordTrace_append hprefix tailTrace_1551460
  have hstable : (prefixWord ++ tailWord_1551460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551460).length < 2 ^ (prefixWord ++ tailWord_1551460).sum := by decide
  have hdescent : baseEnd_1551460 < baseStart_1551460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551474 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 5, 1, 3]
def baseStart_1551474 : Nat := 118140960795 + 1551474 * 2 ^ 59
def prefixEnd_1551474 : Nat := 4983230072969 + 3 ^ 40 * 1551474 * 2
def baseEnd_1551474 : Nat := 796651884953768084539907

theorem tailTrace_1551474 : CollatzResearch.WordTrace tailWord_1551474 prefixEnd_1551474 796651884953768084539907 := by
  unfold tailWord_1551474
  simp only [CollatzResearch.WordTrace]
  refine ⟨14146726395320535877229369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37724603720854762339278317 14146726395320535877229369)
  ·
    refine ⟨10610044796490401907922027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14146726395320535877229369 10610044796490401907922027)
    ·
      refine ⟨15915067194735602861883041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10610044796490401907922027 15915067194735602861883041)
      ·
        refine ⟨11936300396051702146412281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15915067194735602861883041 11936300396051702146412281)
        ·
          refine ⟨8952225297038776609809211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11936300396051702146412281 8952225297038776609809211)
          ·
            refine ⟨13428337945558164914713817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8952225297038776609809211 13428337945558164914713817)
            ·
              refine ⟨10071253459168623686035363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13428337945558164914713817 10071253459168623686035363)
              ·
                refine ⟨15106880188752935529053045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10071253459168623686035363 15106880188752935529053045)
                ·
                  refine ⟨1416270017695587705848723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15106880188752935529053045 1416270017695587705848723)
                  ·
                    refine ⟨2124405026543381558773085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1416270017695587705848723 2124405026543381558773085)
                    ·
                      refine ⟨796651884953768084539907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2124405026543381558773085 796651884953768084539907)
                      ·
                        rfl

theorem cell23_1551474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_1551474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551474 prefixEnd_1551474 := by exact prefixLift 1551474
  have htrace : WordTrace (prefixWord ++ tailWord_1551474) baseStart_1551474 baseEnd_1551474 := by
    simpa [prefixWord, tailWord_1551474, baseEnd_1551474] using wordTrace_append hprefix tailTrace_1551474
  have hstable : (prefixWord ++ tailWord_1551474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551474).length < 2 ^ (prefixWord ++ tailWord_1551474).sum := by decide
  have hdescent : baseEnd_1551474 < baseStart_1551474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551491 : List Nat := [1, 1, 1, 3, 3, 2, 2, 5, 1, 1, 3]
def baseStart_1551491 : Nat := 118140960795 + 1551491 * 2 ^ 59
def prefixEnd_1551491 : Nat := 4983230072969 + 3 ^ 40 * 1551491 * 2
def baseEnd_1551491 : Nat := 796660614124894518027329

theorem tailTrace_1551491 : CollatzResearch.WordTrace tailWord_1551491 prefixEnd_1551491 796660614124894518027329 := by
  unfold tailWord_1551491
  simp only [CollatzResearch.WordTrace]
  refine ⟨56587525622220555412286327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37725017081480370274857551 56587525622220555412286327)
  ·
    refine ⟨84881288433330833118429491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56587525622220555412286327 84881288433330833118429491)
    ·
      refine ⟨127321932649996249677644237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84881288433330833118429491 127321932649996249677644237)
      ·
        refine ⟨47745724743748593629116589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127321932649996249677644237 47745724743748593629116589)
        ·
          refine ⟨17904646778905722610918721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47745724743748593629116589 17904646778905722610918721)
          ·
            refine ⟨13428485084179291958189041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17904646778905722610918721 13428485084179291958189041)
            ·
              refine ⟨10071363813134468968641781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13428485084179291958189041 10071363813134468968641781)
              ·
                refine ⟨944190357481356465810167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10071363813134468968641781 944190357481356465810167)
                ·
                  refine ⟨1416285536222034698715251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 944190357481356465810167 1416285536222034698715251)
                  ·
                    refine ⟨2124428304333052048072877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1416285536222034698715251 2124428304333052048072877)
                    ·
                      refine ⟨796660614124894518027329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2124428304333052048072877 796660614124894518027329)
                      ·
                        rfl

theorem cell23_1551491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 1, 1, 3].length) (baseStart_1551491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551491 prefixEnd_1551491 := by exact prefixLift 1551491
  have htrace : WordTrace (prefixWord ++ tailWord_1551491) baseStart_1551491 baseEnd_1551491 := by
    simpa [prefixWord, tailWord_1551491, baseEnd_1551491] using wordTrace_append hprefix tailTrace_1551491
  have hstable : (prefixWord ++ tailWord_1551491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551491).length < 2 ^ (prefixWord ++ tailWord_1551491).sum := by decide
  have hdescent : baseEnd_1551491 < baseStart_1551491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551507 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 4, 4]
def baseStart_1551507 : Nat := 118140960795 + 1551507 * 2 ^ 59
def prefixEnd_1551507 : Nat := 4983230072969 + 3 ^ 40 * 1551507 * 2
def baseEnd_1551507 : Nat := 265556276605122151809085

theorem tailTrace_1551507 : CollatzResearch.WordTrace tailWord_1551507 prefixEnd_1551507 265556276605122151809085 := by
  unfold tailWord_1551507
  simp only [CollatzResearch.WordTrace]
  refine ⟨56588109190162590144868775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37725406126775060096579183 56588109190162590144868775)
  ·
    refine ⟨84882163785243885217303163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56588109190162590144868775 84882163785243885217303163)
    ·
      refine ⟨127323245677865827825954745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84882163785243885217303163 127323245677865827825954745)
      ·
        refine ⟨95492434258399370869466059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127323245677865827825954745 95492434258399370869466059)
        ·
          refine ⟨143238651387599056304199089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95492434258399370869466059 143238651387599056304199089)
          ·
            refine ⟨107428988540699292228149317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143238651387599056304199089 107428988540699292228149317)
            ·
              refine ⟨20142935351381117292777997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107428988540699292228149317 20142935351381117292777997)
              ·
                refine ⟨7553600756767918984791749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20142935351381117292777997 7553600756767918984791749)
                ·
                  refine ⟨1416300141893984809648453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7553600756767918984791749 1416300141893984809648453)
                  ·
                    refine ⟨265556276605122151809085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1416300141893984809648453 265556276605122151809085)
                    ·
                      rfl

theorem cell23_1551507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 4].length) (baseStart_1551507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551507 prefixEnd_1551507 := by exact prefixLift 1551507
  have htrace : WordTrace (prefixWord ++ tailWord_1551507) baseStart_1551507 baseEnd_1551507 := by
    simpa [prefixWord, tailWord_1551507, baseEnd_1551507] using wordTrace_append hprefix tailTrace_1551507
  have hstable : (prefixWord ++ tailWord_1551507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551507).length < 2 ^ (prefixWord ++ tailWord_1551507).sum := by decide
  have hdescent : baseEnd_1551507 < baseStart_1551507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551514 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1551514 : Nat := 118140960795 + 1551514 * 2 ^ 59
def prefixEnd_1551514 : Nat := 4983230072969 + 3 ^ 40 * 1551514 * 2
def baseEnd_1551514 : Nat := 796672424179947928039723

theorem tailTrace_1551514 : CollatzResearch.WordTrace tailWord_1551514 prefixEnd_1551514 796672424179947928039723 := by
  unfold tailWord_1551514
  simp only [CollatzResearch.WordTrace]
  refine ⟨14147091125284307585093399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37725576334091486893582397 14147091125284307585093399)
  ·
    refine ⟨21220636687926461377640099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14147091125284307585093399 21220636687926461377640099)
    ·
      refine ⟨31830955031889692066460149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21220636687926461377640099 31830955031889692066460149)
      ·
        refine ⟨2984152034239658631230639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31830955031889692066460149 2984152034239658631230639)
        ·
          refine ⟨4476228051359487946845959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2984152034239658631230639 4476228051359487946845959)
          ·
            refine ⟨6714342077039231920268939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4476228051359487946845959 6714342077039231920268939)
            ·
              refine ⟨10071513115558847880403409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6714342077039231920268939 10071513115558847880403409)
              ·
                refine ⟨7553634836669135910302557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10071513115558847880403409 7553634836669135910302557)
                ·
                  refine ⟨2832613063750925966363459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7553634836669135910302557 2832613063750925966363459)
                  ·
                    refine ⟨4248919595626388949545189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2832613063750925966363459 4248919595626388949545189)
                    ·
                      refine ⟨796672424179947928039723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4248919595626388949545189 796672424179947928039723)
                      ·
                        rfl

theorem cell23_1551514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1551514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551514 prefixEnd_1551514 := by exact prefixLift 1551514
  have htrace : WordTrace (prefixWord ++ tailWord_1551514) baseStart_1551514 baseEnd_1551514 := by
    simpa [prefixWord, tailWord_1551514, baseEnd_1551514] using wordTrace_append hprefix tailTrace_1551514
  have hstable : (prefixWord ++ tailWord_1551514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551514).length < 2 ^ (prefixWord ++ tailWord_1551514).sum := by decide
  have hdescent : baseEnd_1551514 < baseStart_1551514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551517 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_1551517 : Nat := 118140960795 + 1551517 * 2 ^ 59
def prefixEnd_1551517 : Nat := 4983230072969 + 3 ^ 40 * 1551517 * 2
def baseEnd_1551517 : Nat := 796673964621911416302209

theorem tailTrace_1551517 : CollatzResearch.WordTrace tailWord_1551517 prefixEnd_1551517 796673964621911416302209 := by
  unfold tailWord_1551517
  simp only [CollatzResearch.WordTrace]
  refine ⟨56588473920126361852732805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37725649280084241235155203 56588473920126361852732805)
  ·
    refine ⟨10610338860023692847387401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56588473920126361852732805 10610338860023692847387401)
    ·
      refine ⟨7957754145017769635540551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10610338860023692847387401 7957754145017769635540551)
      ·
        refine ⟨11936631217526654453310827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7957754145017769635540551 11936631217526654453310827)
        ·
          refine ⟨17904946826289981679966241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11936631217526654453310827 17904946826289981679966241)
          ·
            refine ⟨13428710119717486259974681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17904946826289981679966241 13428710119717486259974681)
            ·
              refine ⟨10071532589788114694981011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13428710119717486259974681 10071532589788114694981011)
              ·
                refine ⟨15107298884682172042471517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10071532589788114694981011 15107298884682172042471517)
                ·
                  refine ⟨5665237081755814515926819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15107298884682172042471517 5665237081755814515926819)
                  ·
                    refine ⟨8497855622633721773890229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5665237081755814515926819 8497855622633721773890229)
                    ·
                      refine ⟨796673964621911416302209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8497855622633721773890229 796673964621911416302209)
                      ·
                        rfl

theorem cell23_1551517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_1551517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551517 prefixEnd_1551517 := by exact prefixLift 1551517
  have htrace : WordTrace (prefixWord ++ tailWord_1551517) baseStart_1551517 baseEnd_1551517 := by
    simpa [prefixWord, tailWord_1551517, baseEnd_1551517] using wordTrace_append hprefix tailTrace_1551517
  have hstable : (prefixWord ++ tailWord_1551517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551517).length < 2 ^ (prefixWord ++ tailWord_1551517).sum := by decide
  have hdescent : baseEnd_1551517 < baseStart_1551517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551524 : List Nat := [2, 3, 1, 2, 3, 2, 2, 1, 1, 6]
def baseStart_1551524 : Nat := 118140960795 + 1551524 * 2 ^ 59
def prefixEnd_1551524 : Nat := 4983230072969 + 3 ^ 40 * 1551524 * 2
def baseEnd_1551524 : Nat := 265559186328830962971559

theorem tailTrace_1551524 : CollatzResearch.WordTrace tailWord_1551524 prefixEnd_1551524 265559186328830962971559 := by
  unfold tailWord_1551524
  simp only [CollatzResearch.WordTrace]
  refine ⟨28294364615550501024118813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37725819487400668032158417 28294364615550501024118813)
  ·
    refine ⟨10610386730831437884044555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28294364615550501024118813 10610386730831437884044555)
    ·
      refine ⟨15915580096247156826066833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10610386730831437884044555 15915580096247156826066833)
      ·
        refine ⟨11936685072185367619550125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15915580096247156826066833 11936685072185367619550125)
        ·
          refine ⟨4476256902069512857331297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11936685072185367619550125 4476256902069512857331297)
          ·
            refine ⟨3357192676552134642998473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4476256902069512857331297 3357192676552134642998473)
            ·
              refine ⟨2517894507414100982248855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3357192676552134642998473 2517894507414100982248855)
              ·
                refine ⟨3776841761121151473373283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2517894507414100982248855 3776841761121151473373283)
                ·
                  refine ⟨5665262641681727210059925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3776841761121151473373283 5665262641681727210059925)
                  ·
                    refine ⟨265559186328830962971559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5665262641681727210059925 265559186328830962971559)
                    ·
                      rfl

theorem cell23_1551524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_1551524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551524 prefixEnd_1551524 := by exact prefixLift 1551524
  have htrace : WordTrace (prefixWord ++ tailWord_1551524) baseStart_1551524 baseEnd_1551524 := by
    simpa [prefixWord, tailWord_1551524, baseEnd_1551524] using wordTrace_append hprefix tailTrace_1551524
  have hstable : (prefixWord ++ tailWord_1551524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551524).length < 2 ^ (prefixWord ++ tailWord_1551524).sum := by decide
  have hdescent : baseEnd_1551524 < baseStart_1551524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551547 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 3]
def baseStart_1551547 : Nat := 118140960795 + 1551547 * 2 ^ 59
def prefixEnd_1551547 : Nat := 4983230072969 + 3 ^ 40 * 1551547 * 2
def baseEnd_1551547 : Nat := 796689369041546298927071

theorem tailTrace_1551547 : CollatzResearch.WordTrace tailWord_1551547 prefixEnd_1551547 796689369041546298927071 := by
  unfold tailWord_1551547
  simp only [CollatzResearch.WordTrace]
  refine ⟨56589568110017676976324895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37726378740011784650883263 56589568110017676976324895)
  ·
    refine ⟨84884352165026515464487343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56589568110017676976324895 84884352165026515464487343)
    ·
      refine ⟨127326528247539773196731015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84884352165026515464487343 127326528247539773196731015)
      ·
        refine ⟨190989792371309659795096523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127326528247539773196731015 190989792371309659795096523)
        ·
          refine ⟨286484688556964489692644785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190989792371309659795096523 286484688556964489692644785)
          ·
            refine ⟨214863516417723367269483589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286484688556964489692644785 214863516417723367269483589)
            ·
              refine ⟨40286909328323131363028173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 214863516417723367269483589 40286909328323131363028173)
              ·
                refine ⟨15107590998121174261135565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40286909328323131363028173 15107590998121174261135565)
                ·
                  refine ⟨5665346624295440347925837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15107590998121174261135565 5665346624295440347925837)
                  ·
                    refine ⟨2124504984110790130472189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5665346624295440347925837 2124504984110790130472189)
                    ·
                      refine ⟨796689369041546298927071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2124504984110790130472189 796689369041546298927071)
                      ·
                        rfl

theorem cell23_1551547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 3].length) (baseStart_1551547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551547 prefixEnd_1551547 := by exact prefixLift 1551547
  have htrace : WordTrace (prefixWord ++ tailWord_1551547) baseStart_1551547 baseEnd_1551547 := by
    simpa [prefixWord, tailWord_1551547, baseEnd_1551547] using wordTrace_append hprefix tailTrace_1551547
  have hstable : (prefixWord ++ tailWord_1551547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551547).length < 2 ^ (prefixWord ++ tailWord_1551547).sum := by decide
  have hdescent : baseEnd_1551547 < baseStart_1551547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551548 : List Nat := [2, 2, 2, 3, 2, 3, 2, 1, 1, 1, 4]
def baseStart_1551548 : Nat := 118140960795 + 1551548 * 2 ^ 59
def prefixEnd_1551548 : Nat := 4983230072969 + 3 ^ 40 * 1551548 * 2
def baseEnd_1551548 : Nat := 796689882522200795014567

theorem tailTrace_1551548 : CollatzResearch.WordTrace tailWord_1551548 prefixEnd_1551548 796689882522200795014567 := by
  unfold tailWord_1551548
  simp only [CollatzResearch.WordTrace]
  refine ⟨28294802291507027073555649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37726403055342702764740865 28294802291507027073555649)
  ·
    refine ⟨21221101718630270305166737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28294802291507027073555649 21221101718630270305166737)
    ·
      refine ⟨15915826288972702728875053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21221101718630270305166737 15915826288972702728875053)
      ·
        refine ⟨5968434858364763523328145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15915826288972702728875053 5968434858364763523328145)
        ·
          refine ⟨4476326143773572642496109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5968434858364763523328145 4476326143773572642496109)
          ·
            refine ⟨1678622303915089740936041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4476326143773572642496109 1678622303915089740936041)
            ·
              refine ⟨1258966727936317305702031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1678622303915089740936041 1258966727936317305702031)
              ·
                refine ⟨1888450091904475958553047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1258966727936317305702031 1888450091904475958553047)
                ·
                  refine ⟨2832675137856713937829571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888450091904475958553047 2832675137856713937829571)
                  ·
                    refine ⟨4249012706785070906744357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2832675137856713937829571 4249012706785070906744357)
                    ·
                      refine ⟨796689882522200795014567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4249012706785070906744357 796689882522200795014567)
                      ·
                        rfl

theorem cell23_1551548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_1551548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551548 prefixEnd_1551548 := by exact prefixLift 1551548
  have htrace : WordTrace (prefixWord ++ tailWord_1551548) baseStart_1551548 baseEnd_1551548 := by
    simpa [prefixWord, tailWord_1551548, baseEnd_1551548] using wordTrace_append hprefix tailTrace_1551548
  have hstable : (prefixWord ++ tailWord_1551548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551548).length < 2 ^ (prefixWord ++ tailWord_1551548).sum := by decide
  have hdescent : baseEnd_1551548 < baseStart_1551548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551551 : List Nat := [1, 1, 2, 2, 2, 2, 6, 1, 1, 2, 3]
def baseStart_1551551 : Nat := 118140960795 + 1551551 * 2 ^ 59
def prefixEnd_1551551 : Nat := 4983230072969 + 3 ^ 40 * 1551551 * 2
def baseEnd_1551551 : Nat := 796691422964164283277053

theorem tailTrace_1551551 : CollatzResearch.WordTrace tailWord_1551551 prefixEnd_1551551 796691422964164283277053 := by
  unfold tailWord_1551551
  simp only [CollatzResearch.WordTrace]
  refine ⟨56589714002003185659470507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37726476001335457106313671 56589714002003185659470507)
  ·
    refine ⟨84884571003004778489205761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56589714002003185659470507 84884571003004778489205761)
    ·
      refine ⟨63663428252253583866904321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84884571003004778489205761 63663428252253583866904321)
      ·
        refine ⟨47747571189190187900178241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63663428252253583866904321 47747571189190187900178241)
        ·
          refine ⟨35810678391892640925133681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47747571189190187900178241 35810678391892640925133681)
          ·
            refine ⟨26858008793919480693850261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35810678391892640925133681 26858008793919480693850261)
            ·
              refine ⟨1258969162214975657524231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26858008793919480693850261 1258969162214975657524231)
              ·
                refine ⟨1888453743322463486286347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1258969162214975657524231 1888453743322463486286347)
                ·
                  refine ⟨2832680614983695229429521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888453743322463486286347 2832680614983695229429521)
                  ·
                    refine ⟨2124510461237771422072141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2832680614983695229429521 2124510461237771422072141)
                    ·
                      refine ⟨796691422964164283277053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2124510461237771422072141 796691422964164283277053)
                      ·
                        rfl

theorem cell23_1551551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 1, 2, 3].length) (baseStart_1551551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551551 prefixEnd_1551551 := by exact prefixLift 1551551
  have htrace : WordTrace (prefixWord ++ tailWord_1551551) baseStart_1551551 baseEnd_1551551 := by
    simpa [prefixWord, tailWord_1551551, baseEnd_1551551] using wordTrace_append hprefix tailTrace_1551551
  have hstable : (prefixWord ++ tailWord_1551551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551551).length < 2 ^ (prefixWord ++ tailWord_1551551).sum := by decide
  have hdescent : baseEnd_1551551 < baseStart_1551551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551607 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 5]
def baseStart_1551607 : Nat := 118140960795 + 1551607 * 2 ^ 59
def prefixEnd_1551607 : Nat := 4983230072969 + 3 ^ 40 * 1551607 * 2
def baseEnd_1551607 : Nat := 796720177880816064176795

theorem tailTrace_1551607 : CollatzResearch.WordTrace tailWord_1551607 prefixEnd_1551607 796720177880816064176795 := by
  unfold tailWord_1551607
  simp only [CollatzResearch.WordTrace]
  refine ⟨56591756489800307223509075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37727837659866871482339383 56591756489800307223509075)
  ·
    refine ⟨84887634734700460835263613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56591756489800307223509075 84887634734700460835263613)
    ·
      refine ⟨31832863025512672813223855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84887634734700460835263613 31832863025512672813223855)
      ·
        refine ⟨47749294538269009219835783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31832863025512672813223855 47749294538269009219835783)
        ·
          refine ⟨71623941807403513829753675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47749294538269009219835783 71623941807403513829753675)
          ·
            refine ⟨107435912711105270744630513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71623941807403513829753675 107435912711105270744630513)
            ·
              refine ⟨80576934533328953058472885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107435912711105270744630513 80576934533328953058472885)
              ·
                refine ⟨7554087612499589349231833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80576934533328953058472885 7554087612499589349231833)
                ·
                  refine ⟨5665565709374692011923875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7554087612499589349231833 5665565709374692011923875)
                  ·
                    refine ⟨8498348564062038017885813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5665565709374692011923875 8498348564062038017885813)
                    ·
                      refine ⟨796720177880816064176795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8498348564062038017885813 796720177880816064176795)
                      ·
                        rfl

theorem cell23_1551607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_1551607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551607 prefixEnd_1551607 := by exact prefixLift 1551607
  have htrace : WordTrace (prefixWord ++ tailWord_1551607) baseStart_1551607 baseEnd_1551607 := by
    simpa [prefixWord, tailWord_1551607, baseEnd_1551607] using wordTrace_append hprefix tailTrace_1551607
  have hstable : (prefixWord ++ tailWord_1551607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551607).length < 2 ^ (prefixWord ++ tailWord_1551607).sum := by decide
  have hdescent : baseEnd_1551607 < baseStart_1551607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551621 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 4, 2, 2]
def baseStart_1551621 : Nat := 118140960795 + 1551621 * 2 ^ 59
def prefixEnd_1551621 : Nat := 4983230072969 + 3 ^ 40 * 1551621 * 2
def baseEnd_1551621 : Nat := 796727366609979009401731

theorem tailTrace_1551621 : CollatzResearch.WordTrace tailWord_1551621 prefixEnd_1551621 796727366609979009401731 := by
  unfold tailWord_1551621
  simp only [CollatzResearch.WordTrace]
  refine ⟨56592267111749587614518717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37728178074499725076345811 56592267111749587614518717)
  ·
    refine ⟨21222100166906095355444519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56592267111749587614518717 21222100166906095355444519)
    ·
      refine ⟨31833150250359143033166779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21222100166906095355444519 31833150250359143033166779)
      ·
        refine ⟨47749725375538714549750169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31833150250359143033166779 47749725375538714549750169)
        ·
          refine ⟨35812294031654035912312627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47749725375538714549750169 35812294031654035912312627)
          ·
            refine ⟨53718441047481053868468941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35812294031654035912312627 53718441047481053868468941)
            ·
              refine ⟨20144415392805395200675853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53718441047481053868468941 20144415392805395200675853)
              ·
                refine ⟨7554155772302023200253445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20144415392805395200675853 7554155772302023200253445)
                ·
                  refine ⟨1416404207306629350047521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7554155772302023200253445 1416404207306629350047521)
                  ·
                    refine ⟨1062303155479972012535641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1416404207306629350047521 1062303155479972012535641)
                    ·
                      refine ⟨796727366609979009401731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1062303155479972012535641 796727366609979009401731)
                      ·
                        rfl

theorem cell23_1551621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 2, 2].length) (baseStart_1551621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551621 prefixEnd_1551621 := by exact prefixLift 1551621
  have htrace : WordTrace (prefixWord ++ tailWord_1551621) baseStart_1551621 baseEnd_1551621 := by
    simpa [prefixWord, tailWord_1551621, baseEnd_1551621] using wordTrace_append hprefix tailTrace_1551621
  have hstable : (prefixWord ++ tailWord_1551621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551621).length < 2 ^ (prefixWord ++ tailWord_1551621).sum := by decide
  have hdescent : baseEnd_1551621 < baseStart_1551621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551674 : List Nat := [3, 1, 1, 1, 4, 1, 1, 4, 2, 5]
def baseStart_1551674 : Nat := 118140960795 + 1551674 * 2 ^ 59
def prefixEnd_1551674 : Nat := 4983230072969 + 3 ^ 40 * 1551674 * 2
def baseEnd_1551674 : Nat := 265584860361555767346329

theorem tailTrace_1551674 : CollatzResearch.WordTrace tailWord_1551674 prefixEnd_1551674 265584860361555767346329 := by
  unfold tailWord_1551674
  simp only [CollatzResearch.WordTrace]
  refine ⟨14148550045139394416549519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37729466787038385110798717 14148550045139394416549519)
  ·
    refine ⟨21222825067709091624824279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14148550045139394416549519 21222825067709091624824279)
    ·
      refine ⟨31834237601563637437236419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21222825067709091624824279 31834237601563637437236419)
      ·
        refine ⟨47751356402345456155854629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31834237601563637437236419 47751356402345456155854629)
        ·
          refine ⟨8953379325439773029222743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47751356402345456155854629 8953379325439773029222743)
          ·
            refine ⟨13430068988159659543834115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8953379325439773029222743 13430068988159659543834115)
            ·
              refine ⟨20145103482239489315751173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13430068988159659543834115 20145103482239489315751173)
              ·
                refine ⟨3777206902919904246703345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20145103482239489315751173 3777206902919904246703345)
                ·
                  refine ⟨2832905177189928185027509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3777206902919904246703345 2832905177189928185027509)
                  ·
                    refine ⟨265584860361555767346329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2832905177189928185027509 265584860361555767346329)
                    ·
                      rfl

theorem cell23_1551674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_1551674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551674 prefixEnd_1551674 := by exact prefixLift 1551674
  have htrace : WordTrace (prefixWord ++ tailWord_1551674) baseStart_1551674 baseEnd_1551674 := by
    simpa [prefixWord, tailWord_1551674, baseEnd_1551674] using wordTrace_append hprefix tailTrace_1551674
  have hstable : (prefixWord ++ tailWord_1551674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551674).length < 2 ^ (prefixWord ++ tailWord_1551674).sum := by decide
  have hdescent : baseEnd_1551674 < baseStart_1551674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551694 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_1551694 : Nat := 118140960795 + 1551694 * 2 ^ 59
def prefixEnd_1551694 : Nat := 4983230072969 + 3 ^ 40 * 1551694 * 2
def baseEnd_1551694 : Nat := 796764850697757223788895

theorem tailTrace_1551694 : CollatzResearch.WordTrace tailWord_1551694 prefixEnd_1551694 796764850697757223788895 := by
  unfold tailWord_1551694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7074366205060640135240767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37729953093656747387950757 7074366205060640135240767)
  ·
    refine ⟨10611549307590960202861151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7074366205060640135240767 10611549307590960202861151)
    ·
      refine ⟨15917323961386440304291727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10611549307590960202861151 15917323961386440304291727)
      ·
        refine ⟨23875985942079660456437591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15917323961386440304291727 23875985942079660456437591)
        ·
          refine ⟨35813978913119490684656387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23875985942079660456437591 35813978913119490684656387)
          ·
            refine ⟨53720968369679236026984581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35813978913119490684656387 53720968369679236026984581)
            ·
              refine ⟨10072681569314856755059609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53720968369679236026984581 10072681569314856755059609)
              ·
                refine ⟨7554511176986142566294707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10072681569314856755059609 7554511176986142566294707)
                ·
                  refine ⟨11331766765479213849442061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7554511176986142566294707 11331766765479213849442061)
                  ·
                    refine ⟨4249412537054705193540773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11331766765479213849442061 4249412537054705193540773)
                    ·
                      refine ⟨796764850697757223788895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4249412537054705193540773 796764850697757223788895)
                      ·
                        rfl

theorem cell23_1551694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_1551694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551694 prefixEnd_1551694 := by exact prefixLift 1551694
  have htrace : WordTrace (prefixWord ++ tailWord_1551694) baseStart_1551694 baseEnd_1551694 := by
    simpa [prefixWord, tailWord_1551694, baseEnd_1551694] using wordTrace_append hprefix tailTrace_1551694
  have hstable : (prefixWord ++ tailWord_1551694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551694).length < 2 ^ (prefixWord ++ tailWord_1551694).sum := by decide
  have hdescent : baseEnd_1551694 < baseStart_1551694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551724 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 6]
def baseStart_1551724 : Nat := 118140960795 + 1551724 * 2 ^ 59
def prefixEnd_1551724 : Nat := 4983230072969 + 3 ^ 40 * 1551724 * 2
def baseEnd_1551724 : Nat := 796780255117392106413757

theorem tailTrace_1551724 : CollatzResearch.WordTrace tailWord_1551724 prefixEnd_1551724 796780255117392106413757 := by
  unfold tailWord_1551724
  simp only [CollatzResearch.WordTrace]
  refine ⟨28298011915188218102759113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37730682553584290803678817 28298011915188218102759113)
  ·
    refine ⟨21223508936391163577069335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28298011915188218102759113 21223508936391163577069335)
    ·
      refine ⟨31835263404586745365604003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21223508936391163577069335 31835263404586745365604003)
      ·
        refine ⟨47752895106880118048406005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31835263404586745365604003 47752895106880118048406005)
        ·
          refine ⟨4476833916270011067038063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47752895106880118048406005 4476833916270011067038063)
          ·
            refine ⟨6715250874405016600557095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4476833916270011067038063 6715250874405016600557095)
            ·
              refine ⟨10072876311607524900835643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6715250874405016600557095 10072876311607524900835643)
              ·
                refine ⟨15109314467411287351253465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10072876311607524900835643 15109314467411287351253465)
                ·
                  refine ⟨11331985850558465513440099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15109314467411287351253465 11331985850558465513440099)
                  ·
                    refine ⟨16997978775837698270160149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11331985850558465513440099 16997978775837698270160149)
                    ·
                      refine ⟨796780255117392106413757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16997978775837698270160149 796780255117392106413757)
                      ·
                        rfl

theorem cell23_1551724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_1551724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551724 prefixEnd_1551724 := by exact prefixLift 1551724
  have htrace : WordTrace (prefixWord ++ tailWord_1551724) baseStart_1551724 baseEnd_1551724 := by
    simpa [prefixWord, tailWord_1551724, baseEnd_1551724] using wordTrace_append hprefix tailTrace_1551724
  have hstable : (prefixWord ++ tailWord_1551724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551724).length < 2 ^ (prefixWord ++ tailWord_1551724).sum := by decide
  have hdescent : baseEnd_1551724 < baseStart_1551724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551794 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 5, 6]
def baseStart_1551794 : Nat := 118140960795 + 1551794 * 2 ^ 59
def prefixEnd_1551794 : Nat := 4983230072969 + 3 ^ 40 * 1551794 * 2
def baseEnd_1551794 : Nat := 265605399587735610846145

theorem tailTrace_1551794 : CollatzResearch.WordTrace tailWord_1551794 prefixEnd_1551794 265605399587735610846145 := by
  unfold tailWord_1551794
  simp only [CollatzResearch.WordTrace]
  refine ⟨14149644235030709540141609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37732384626748558773710957 14149644235030709540141609)
  ·
    refine ⟨10612233176273032155106207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14149644235030709540141609 10612233176273032155106207)
    ·
      refine ⟨15918349764409548232659311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10612233176273032155106207 15918349764409548232659311)
      ·
        refine ⟨23877524646614322348988967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15918349764409548232659311 23877524646614322348988967)
        ·
          refine ⟨35816286969921483523483451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23877524646614322348988967 35816286969921483523483451)
          ·
            refine ⟨53724430454882225285225177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35816286969921483523483451 53724430454882225285225177)
            ·
              refine ⟨40293322841161668963918883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53724430454882225285225177 40293322841161668963918883)
              ·
                refine ⟨60439984261742503445878325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40293322841161668963918883 60439984261742503445878325)
                ·
                  refine ⟨5666248524538359698051093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60439984261742503445878325 5666248524538359698051093)
                  ·
                    refine ⟨265605399587735610846145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5666248524538359698051093 265605399587735610846145)
                    ·
                      rfl

theorem cell23_1551794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_1551794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551794 prefixEnd_1551794 := by exact prefixLift 1551794
  have htrace : WordTrace (prefixWord ++ tailWord_1551794) baseStart_1551794 baseEnd_1551794 := by
    simpa [prefixWord, tailWord_1551794, baseEnd_1551794] using wordTrace_append hprefix tailTrace_1551794
  have hstable : (prefixWord ++ tailWord_1551794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551794).length < 2 ^ (prefixWord ++ tailWord_1551794).sum := by decide
  have hdescent : baseEnd_1551794 < baseStart_1551794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551818 : List Nat := [3, 1, 2, 1, 2, 3, 3, 2, 1, 1, 4]
def baseStart_1551818 : Nat := 118140960795 + 1551818 * 2 ^ 59
def prefixEnd_1551818 : Nat := 4983230072969 + 3 ^ 40 * 1551818 * 2
def baseEnd_1551818 : Nat := 796828522298914738638325

theorem tailTrace_1551818 : CollatzResearch.WordTrace tailWord_1551818 prefixEnd_1551818 796828522298914738638325 := by
  unfold tailWord_1551818
  simp only [CollatzResearch.WordTrace]
  refine ⟨14149863073008972564860027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37732968194690593506293405 14149863073008972564860027)
  ·
    refine ⟨21224794609513458847290041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14149863073008972564860027 21224794609513458847290041)
    ·
      refine ⟨15918595957135094135467531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21224794609513458847290041 15918595957135094135467531)
      ·
        refine ⟨23877893935702641203201297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15918595957135094135467531 23877893935702641203201297)
        ·
          refine ⟨17908420451776980902400973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23877893935702641203201297 17908420451776980902400973)
          ·
            refine ⟨6715657669416367838400365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17908420451776980902400973 6715657669416367838400365)
            ·
              refine ⟨2518371626031137939400137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6715657669416367838400365 2518371626031137939400137)
              ·
                refine ⟨1888778719523353454550103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2518371626031137939400137 1888778719523353454550103)
                ·
                  refine ⟨2833168079285030181825155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888778719523353454550103 2833168079285030181825155)
                  ·
                    refine ⟨4249752118927545272737733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2833168079285030181825155 4249752118927545272737733)
                    ·
                      refine ⟨796828522298914738638325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4249752118927545272737733 796828522298914738638325)
                      ·
                        rfl

theorem cell23_1551818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_1551818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551818 prefixEnd_1551818 := by exact prefixLift 1551818
  have htrace : WordTrace (prefixWord ++ tailWord_1551818) baseStart_1551818 baseEnd_1551818 := by
    simpa [prefixWord, tailWord_1551818, baseEnd_1551818] using wordTrace_append hprefix tailTrace_1551818
  have hstable : (prefixWord ++ tailWord_1551818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551818).length < 2 ^ (prefixWord ++ tailWord_1551818).sum := by decide
  have hdescent : baseEnd_1551818 < baseStart_1551818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551828 : List Nat := [2, 4, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_1551828 : Nat := 118140960795 + 1551828 * 2 ^ 59
def prefixEnd_1551828 : Nat := 4983230072969 + 3 ^ 40 * 1551828 * 2
def baseEnd_1551828 : Nat := 265611219035153233171093

theorem tailTrace_1551828 : CollatzResearch.WordTrace tailWord_1551828 prefixEnd_1551828 265611219035153233171093 := by
  unfold tailWord_1551828
  simp only [CollatzResearch.WordTrace]
  refine ⟨28299908510999830983652069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37733211347999774644869425 28299908510999830983652069)
  ·
    refine ⟨5306232845812468309434763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28299908510999830983652069 5306232845812468309434763)
    ·
      refine ⟨7959349268718702464152145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5306232845812468309434763 7959349268718702464152145)
      ·
        refine ⟨5969511951539026848114109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7959349268718702464152145 5969511951539026848114109)
        ·
          refine ⟨2238566981827135068042791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5969511951539026848114109 2238566981827135068042791)
          ·
            refine ⟨3357850472740702602064187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2238566981827135068042791 3357850472740702602064187)
            ·
              refine ⟨5036775709111053903096281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3357850472740702602064187 5036775709111053903096281)
              ·
                refine ⟨3777581781833290427322211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5036775709111053903096281 3777581781833290427322211)
                ·
                  refine ⟨5666372672749935640983317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3777581781833290427322211 5666372672749935640983317)
                  ·
                    refine ⟨265611219035153233171093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5666372672749935640983317 265611219035153233171093)
                    ·
                      rfl

theorem cell23_1551828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_1551828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551828 prefixEnd_1551828 := by exact prefixLift 1551828
  have htrace : WordTrace (prefixWord ++ tailWord_1551828) baseStart_1551828 baseEnd_1551828 := by
    simpa [prefixWord, tailWord_1551828, baseEnd_1551828] using wordTrace_append hprefix tailTrace_1551828
  have hstable : (prefixWord ++ tailWord_1551828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551828).length < 2 ^ (prefixWord ++ tailWord_1551828).sum := by decide
  have hdescent : baseEnd_1551828 < baseStart_1551828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551845 : List Nat := [1, 3, 1, 5, 1, 2, 2, 2, 2, 4]
def baseStart_1551845 : Nat := 118140960795 + 1551845 * 2 ^ 59
def prefixEnd_1551845 : Nat := 4983230072969 + 3 ^ 40 * 1551845 * 2
def baseEnd_1551845 : Nat := 265614128758862044333567

theorem tailTrace_1551845 : CollatzResearch.WordTrace tailWord_1551845 prefixEnd_1551845 265614128758862044333567 := by
  unfold tailWord_1551845
  simp only [CollatzResearch.WordTrace]
  refine ⟨56600437062938073870672989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37733624708625382580448659 56600437062938073870672989)
  ·
    refine ⟨21225163898601777701502371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56600437062938073870672989 21225163898601777701502371)
    ·
      refine ⟨31837745847902666552253557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21225163898601777701502371 31837745847902666552253557)
      ·
        refine ⟨2984788673240874989273771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31837745847902666552253557 2984788673240874989273771)
        ·
          refine ⟨4477183009861312483910657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2984788673240874989273771 4477183009861312483910657)
          ·
            refine ⟨3357887257395984362932993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4477183009861312483910657 3357887257395984362932993)
            ·
              refine ⟨2518415443046988272199745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3357887257395984362932993 2518415443046988272199745)
              ·
                refine ⟨1888811582285241204149809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2518415443046988272199745 1888811582285241204149809)
                ·
                  refine ⟨1416608686713930903112357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1888811582285241204149809 1416608686713930903112357)
                  ·
                    refine ⟨265614128758862044333567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1416608686713930903112357 265614128758862044333567)
                    ·
                      rfl

theorem cell23_1551845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_1551845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551845 prefixEnd_1551845 := by exact prefixLift 1551845
  have htrace : WordTrace (prefixWord ++ tailWord_1551845) baseStart_1551845 baseEnd_1551845 := by
    simpa [prefixWord, tailWord_1551845, baseEnd_1551845] using wordTrace_append hprefix tailTrace_1551845
  have hstable : (prefixWord ++ tailWord_1551845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551845).length < 2 ^ (prefixWord ++ tailWord_1551845).sum := by decide
  have hdescent : baseEnd_1551845 < baseStart_1551845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551858 : List Nat := [3, 2, 1, 4, 1, 3, 1, 8]
def baseStart_1551858 : Nat := 118140960795 + 1551858 * 2 ^ 59
def prefixEnd_1551858 : Nat := 4983230072969 + 3 ^ 40 * 1551858 * 2
def baseEnd_1551858 : Nat := 29512928204633132671783

theorem tailTrace_1551858 : CollatzResearch.WordTrace tailWord_1551858 prefixEnd_1551858 29512928204633132671783 := by
  unfold tailWord_1551858
  simp only [CollatzResearch.WordTrace]
  refine ⟨14150227802972744272724057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37733940807927318060597485 14150227802972744272724057)
  ·
    refine ⟨10612670852229558204543043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14150227802972744272724057 10612670852229558204543043)
    ·
      refine ⟨15919006278344337306814565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10612670852229558204543043 15919006278344337306814565)
      ·
        refine ⟨2984813677189563245027731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15919006278344337306814565 2984813677189563245027731)
        ·
          refine ⟨4477220515784344867541597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2984813677189563245027731 4477220515784344867541597)
          ·
            refine ⟨1678957693419129325328099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4477220515784344867541597 1678957693419129325328099)
            ·
              refine ⟨2518436540128693987992149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678957693419129325328099 2518436540128693987992149)
              ·
                refine ⟨29512928204633132671783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2518436540128693987992149 29512928204633132671783)
                ·
                  rfl

theorem cell23_1551858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 8].length) (baseStart_1551858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551858 prefixEnd_1551858 := by exact prefixLift 1551858
  have htrace : WordTrace (prefixWord ++ tailWord_1551858) baseStart_1551858 baseEnd_1551858 := by
    simpa [prefixWord, tailWord_1551858, baseEnd_1551858] using wordTrace_append hprefix tailTrace_1551858
  have hstable : (prefixWord ++ tailWord_1551858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551858).length < 2 ^ (prefixWord ++ tailWord_1551858).sum := by decide
  have hdescent : baseEnd_1551858 < baseStart_1551858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551901 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 4, 6]
def baseStart_1551901 : Nat := 118140960795 + 1551901 * 2 ^ 59
def prefixEnd_1551901 : Nat := 4983230072969 + 3 ^ 40 * 1551901 * 2
def baseEnd_1551901 : Nat := 265623713731079304633481

theorem tailTrace_1551901 : CollatzResearch.WordTrace tailWord_1551901 prefixEnd_1551901 265623713731079304633481 := by
  unfold tailWord_1551901
  simp only [CollatzResearch.WordTrace]
  refine ⟨56602479550735195434711557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37734986367156796956474371 56602479550735195434711557)
  ·
    refine ⟨10612964915762849144008417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56602479550735195434711557 10612964915762849144008417)
    ·
      refine ⟨7959723686822136858006313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10612964915762849144008417 7959723686822136858006313)
      ·
        refine ⟨5969792765116602643504735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7959723686822136858006313 5969792765116602643504735)
        ·
          refine ⟨8954689147674903965257103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5969792765116602643504735 8954689147674903965257103)
          ·
            refine ⟨13432033721512355947885655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8954689147674903965257103 13432033721512355947885655)
            ·
              refine ⟨20148050582268533921828483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13432033721512355947885655 20148050582268533921828483)
              ·
                refine ⟨30222075873402800882742725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20148050582268533921828483 30222075873402800882742725)
                ·
                  refine ⟨5666639226263025165514261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30222075873402800882742725 5666639226263025165514261)
                  ·
                    refine ⟨265623713731079304633481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5666639226263025165514261 265623713731079304633481)
                    ·
                      rfl

theorem cell23_1551901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_1551901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551901 prefixEnd_1551901 := by exact prefixLift 1551901
  have htrace : WordTrace (prefixWord ++ tailWord_1551901) baseStart_1551901 baseEnd_1551901 := by
    simpa [prefixWord, tailWord_1551901, baseEnd_1551901] using wordTrace_append hprefix tailTrace_1551901
  have hstable : (prefixWord ++ tailWord_1551901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551901).length < 2 ^ (prefixWord ++ tailWord_1551901).sum := by decide
  have hdescent : baseEnd_1551901 < baseStart_1551901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551918 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 2, 6]
def baseStart_1551918 : Nat := 118140960795 + 1551918 * 2 ^ 59
def prefixEnd_1551918 : Nat := 4983230072969 + 3 ^ 40 * 1551918 * 2
def baseEnd_1551918 : Nat := 265626623454788115795955

theorem tailTrace_1551918 : CollatzResearch.WordTrace tailWord_1551918 prefixEnd_1551918 265626623454788115795955 := by
  unfold tailWord_1551918
  simp only [CollatzResearch.WordTrace]
  refine ⟨7075387448959200917260051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37735399727782404892053605 7075387448959200917260051)
  ·
    refine ⟨10613081173438801375890077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7075387448959200917260051 10613081173438801375890077)
    ·
      refine ⟨3979905440039550515958779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10613081173438801375890077 3979905440039550515958779)
      ·
        refine ⟨5969858160059325773938169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3979905440039550515958779 5969858160059325773938169)
        ·
          refine ⟨4477393620044494330453627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5969858160059325773938169 4477393620044494330453627)
          ·
            refine ⟨6716090430066741495680441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4477393620044494330453627 6716090430066741495680441)
            ·
              refine ⟨5037067822550056121760331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6716090430066741495680441 5037067822550056121760331)
              ·
                refine ⟨7555601733825084182640497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5037067822550056121760331 7555601733825084182640497)
                ·
                  refine ⟨5666701300368813136980373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7555601733825084182640497 5666701300368813136980373)
                  ·
                    refine ⟨265626623454788115795955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5666701300368813136980373 265626623454788115795955)
                    ·
                      rfl

theorem cell23_1551918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_1551918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551918 prefixEnd_1551918 := by exact prefixLift 1551918
  have htrace : WordTrace (prefixWord ++ tailWord_1551918) baseStart_1551918 baseEnd_1551918 := by
    simpa [prefixWord, tailWord_1551918, baseEnd_1551918] using wordTrace_append hprefix tailTrace_1551918
  have hstable : (prefixWord ++ tailWord_1551918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551918).length < 2 ^ (prefixWord ++ tailWord_1551918).sum := by decide
  have hdescent : baseEnd_1551918 < baseStart_1551918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551925 : List Nat := [1, 3, 3, 1, 1, 3, 3, 1, 1, 4, 2]
def baseStart_1551925 : Nat := 118140960795 + 1551925 * 2 ^ 59
def prefixEnd_1551925 : Nat := 4983230072969 + 3 ^ 40 * 1551925 * 2
def baseEnd_1551925 : Nat := 796883464728945820000333

theorem tailTrace_1551925 : CollatzResearch.WordTrace tailWord_1551925 prefixEnd_1551925 796883464728945820000333 := by
  unfold tailWord_1551925
  simp only [CollatzResearch.WordTrace]
  refine ⟨56603354902648247533585229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37735569935098831689056819 56603354902648247533585229)
  ·
    refine ⟨21226258088493092825094461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56603354902648247533585229 21226258088493092825094461)
    ·
      refine ⟨7959846783184909809410423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21226258088493092825094461 7959846783184909809410423)
      ·
        refine ⟨11939770174777364714115635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7959846783184909809410423 11939770174777364714115635)
        ·
          refine ⟨17909655262166047071173453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11939770174777364714115635 17909655262166047071173453)
          ·
            refine ⟨6716120723312267651690045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17909655262166047071173453 6716120723312267651690045)
            ·
              refine ⟨2518545271242100369383767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6716120723312267651690045 2518545271242100369383767)
              ·
                refine ⟨3777817906863150554075651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2518545271242100369383767 3777817906863150554075651)
                ·
                  refine ⟨5666726860294725831113477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3777817906863150554075651 5666726860294725831113477)
                  ·
                    refine ⟨1062511286305261093333777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5666726860294725831113477 1062511286305261093333777)
                    ·
                      refine ⟨796883464728945820000333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1062511286305261093333777 796883464728945820000333)
                      ·
                        rfl

theorem cell23_1551925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_1551925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551925 prefixEnd_1551925 := by exact prefixLift 1551925
  have htrace : WordTrace (prefixWord ++ tailWord_1551925) baseStart_1551925 baseEnd_1551925 := by
    simpa [prefixWord, tailWord_1551925, baseEnd_1551925] using wordTrace_append hprefix tailTrace_1551925
  have hstable : (prefixWord ++ tailWord_1551925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551925).length < 2 ^ (prefixWord ++ tailWord_1551925).sum := by decide
  have hdescent : baseEnd_1551925 < baseStart_1551925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551968 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 2, 5, 2]
def baseStart_1551968 : Nat := 118140960795 + 1551968 * 2 ^ 59
def prefixEnd_1551968 : Nat := 4983230072969 + 3 ^ 40 * 1551968 * 2
def baseEnd_1551968 : Nat := 796905544397089151762635

theorem tailTrace_1551968 : CollatzResearch.WordTrace tailWord_1551968 prefixEnd_1551968 796905544397089151762635 := by
  unfold tailWord_1551968
  simp only [CollatzResearch.WordTrace]
  refine ⟨28302461620746232938700279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37736615494328310584933705 28302461620746232938700279)
  ·
    refine ⟨42453692431119349408050419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28302461620746232938700279 42453692431119349408050419)
    ·
      refine ⟨63680538646679024112075629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42453692431119349408050419 63680538646679024112075629)
      ·
        refine ⟨23880201992504634042028361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63680538646679024112075629 23880201992504634042028361)
        ·
          refine ⟨17910151494378475531521271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23880201992504634042028361 17910151494378475531521271)
          ·
            refine ⟨26865227241567713297281907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17910151494378475531521271 26865227241567713297281907)
            ·
              refine ⟨40297840862351569945922861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26865227241567713297281907 40297840862351569945922861)
              ·
                refine ⟨15111690323381838729721073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40297840862351569945922861 15111690323381838729721073)
                ·
                  refine ⟨11333767742536379047290805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15111690323381838729721073 11333767742536379047290805)
                  ·
                    refine ⟨1062540725862785535683513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11333767742536379047290805 1062540725862785535683513)
                    ·
                      refine ⟨796905544397089151762635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1062540725862785535683513 796905544397089151762635)
                      ·
                        rfl

theorem cell23_1551968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_1551968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551968 prefixEnd_1551968 := by exact prefixLift 1551968
  have htrace : WordTrace (prefixWord ++ tailWord_1551968) baseStart_1551968 baseEnd_1551968 := by
    simpa [prefixWord, tailWord_1551968, baseEnd_1551968] using wordTrace_append hprefix tailTrace_1551968
  have hstable : (prefixWord ++ tailWord_1551968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551968).length < 2 ^ (prefixWord ++ tailWord_1551968).sum := by decide
  have hdescent : baseEnd_1551968 < baseStart_1551968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551971 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 7]
def baseStart_1551971 : Nat := 118140960795 + 1551971 * 2 ^ 59
def prefixEnd_1551971 : Nat := 4983230072969 + 3 ^ 40 * 1551971 * 2
def baseEnd_1551971 : Nat := 796907084839052640025121

theorem tailTrace_1551971 : CollatzResearch.WordTrace tailWord_1551971 prefixEnd_1551971 796907084839052640025121 := by
  unfold tailWord_1551971
  simp only [CollatzResearch.WordTrace]
  refine ⟨56605032660481597389759767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37736688440321064926506511 56605032660481597389759767)
  ·
    refine ⟨84907548990722396084639651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56605032660481597389759767 84907548990722396084639651)
    ·
      refine ⟨127361323486083594126959477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84907548990722396084639651 127361323486083594126959477)
      ·
        refine ⟨11940124076820336949402451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127361323486083594126959477 11940124076820336949402451)
        ·
          refine ⟨17910186115230505424103677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11940124076820336949402451 17910186115230505424103677)
          ·
            refine ⟨6716319793211439534038879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17910186115230505424103677 6716319793211439534038879)
            ·
              refine ⟨10074479689817159301058319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6716319793211439534038879 10074479689817159301058319)
              ·
                refine ⟨15111719534725738951587479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10074479689817159301058319 15111719534725738951587479)
                ·
                  refine ⟨22667579302088608427381219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15111719534725738951587479 22667579302088608427381219)
                  ·
                    refine ⟨34001368953132912641071829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22667579302088608427381219 34001368953132912641071829)
                    ·
                      refine ⟨796907084839052640025121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34001368953132912641071829 796907084839052640025121)
                      ·
                        rfl

theorem cell23_1551971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_1551971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551971 prefixEnd_1551971 := by exact prefixLift 1551971
  have htrace : WordTrace (prefixWord ++ tailWord_1551971) baseStart_1551971 baseEnd_1551971 := by
    simpa [prefixWord, tailWord_1551971, baseEnd_1551971] using wordTrace_append hprefix tailTrace_1551971
  have hstable : (prefixWord ++ tailWord_1551971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551971).length < 2 ^ (prefixWord ++ tailWord_1551971).sum := by decide
  have hdescent : baseEnd_1551971 < baseStart_1551971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551976 : List Nat := [2, 1, 4, 3, 1, 3, 2, 1, 2, 2, 2]
def baseStart_1551976 : Nat := 118140960795 + 1551976 * 2 ^ 59
def prefixEnd_1551976 : Nat := 4983230072969 + 3 ^ 40 * 1551976 * 2
def baseEnd_1551976 : Nat := 796909652242325120462599

theorem tailTrace_1551976 : CollatzResearch.WordTrace tailWord_1551976 prefixEnd_1551976 796909652242325120462599 := by
  unfold tailWord_1551976
  simp only [CollatzResearch.WordTrace]
  refine ⟨28302607512731741621845891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37736810016975655495794521 28302607512731741621845891)
  ·
    refine ⟨42453911269097612432768837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28302607512731741621845891 42453911269097612432768837)
    ·
      refine ⟨7960108362955802331144157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42453911269097612432768837 7960108362955802331144157)
      ·
        refine ⟨2985040636108425874179059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7960108362955802331144157 2985040636108425874179059)
        ·
          refine ⟨4477560954162638811268589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2985040636108425874179059 4477560954162638811268589)
          ·
            refine ⟨1679085357810989554225721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4477560954162638811268589 1679085357810989554225721)
            ·
              refine ⟨1259314018358242165669291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1679085357810989554225721 1259314018358242165669291)
              ·
                refine ⟨1888971027537363248503937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259314018358242165669291 1888971027537363248503937)
                ·
                  refine ⟨1416728270653022436377953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1888971027537363248503937 1416728270653022436377953)
                  ·
                    refine ⟨1062546202989766827283465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1416728270653022436377953 1062546202989766827283465)
                    ·
                      refine ⟨796909652242325120462599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1062546202989766827283465 796909652242325120462599)
                      ·
                        rfl

theorem cell23_1551976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_1551976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1551976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1551976 prefixEnd_1551976 := by exact prefixLift 1551976
  have htrace : WordTrace (prefixWord ++ tailWord_1551976) baseStart_1551976 baseEnd_1551976 := by
    simpa [prefixWord, tailWord_1551976, baseEnd_1551976] using wordTrace_append hprefix tailTrace_1551976
  have hstable : (prefixWord ++ tailWord_1551976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551976).length < 2 ^ (prefixWord ++ tailWord_1551976).sum := by decide
  have hdescent : baseEnd_1551976 < baseStart_1551976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552011 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 6]
def baseStart_1552011 : Nat := 118140960795 + 1552011 * 2 ^ 59
def prefixEnd_1552011 : Nat := 4983230072969 + 3 ^ 40 * 1552011 * 2
def baseEnd_1552011 : Nat := 796927624065232483524937

theorem tailTrace_1552011 : CollatzResearch.WordTrace tailWord_1552011 prefixEnd_1552011 796927624065232483524937 := by
  unfold tailWord_1552011
  simp only [CollatzResearch.WordTrace]
  refine ⟨56606491580336684221215887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37737661053557789480810591 56606491580336684221215887)
  ·
    refine ⟨84909737370505026331823831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56606491580336684221215887 84909737370505026331823831)
    ·
      refine ⟨127364606055757539497735747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84909737370505026331823831 127364606055757539497735747)
      ·
        refine ⟨191046909083636309246603621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127364606055757539497735747 191046909083636309246603621)
        ·
          refine ⟨35821295453181807983738179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191046909083636309246603621 35821295453181807983738179)
          ·
            refine ⟨53731943179772711975607269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35821295453181807983738179 53731943179772711975607269)
            ·
              refine ⟨10074739346207383495426363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53731943179772711975607269 10074739346207383495426363)
              ·
                refine ⟨15112109019311075243139545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10074739346207383495426363 15112109019311075243139545)
                ·
                  refine ⟨11334081764483306432354659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15112109019311075243139545 11334081764483306432354659)
                  ·
                    refine ⟨17001122646724959648531989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11334081764483306432354659 17001122646724959648531989)
                    ·
                      refine ⟨796927624065232483524937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17001122646724959648531989 796927624065232483524937)
                      ·
                        rfl

theorem cell23_1552011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 6].length) (baseStart_1552011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552011 prefixEnd_1552011 := by exact prefixLift 1552011
  have htrace : WordTrace (prefixWord ++ tailWord_1552011) baseStart_1552011 baseEnd_1552011 := by
    simpa [prefixWord, tailWord_1552011, baseEnd_1552011] using wordTrace_append hprefix tailTrace_1552011
  have hstable : (prefixWord ++ tailWord_1552011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552011).length < 2 ^ (prefixWord ++ tailWord_1552011).sum := by decide
  have hdescent : baseEnd_1552011 < baseStart_1552011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552021 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 8]
def baseStart_1552021 : Nat := 118140960795 + 1552021 * 2 ^ 59
def prefixEnd_1552021 : Nat := 4983230072969 + 3 ^ 40 * 1552021 * 2
def baseEnd_1552021 : Nat := 88548084319086382711099

theorem tailTrace_1552021 : CollatzResearch.WordTrace tailWord_1552021 prefixEnd_1552021 88548084319086382711099 := by
  unfold tailWord_1552021
  simp only [CollatzResearch.WordTrace]
  refine ⟨56606856310300455929079917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37737904206866970619386611 56606856310300455929079917)
  ·
    refine ⟨21227571116362670973404969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56606856310300455929079917 21227571116362670973404969)
    ·
      refine ⟨15920678337272003230053727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21227571116362670973404969 15920678337272003230053727)
      ·
        refine ⟨23881017505908004845080591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15920678337272003230053727 23881017505908004845080591)
        ·
          refine ⟨35821526258862007267620887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23881017505908004845080591 35821526258862007267620887)
          ·
            refine ⟨53732289388293010901431331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35821526258862007267620887 53732289388293010901431331)
            ·
              refine ⟨80598434082439516352146997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53732289388293010901431331 80598434082439516352146997)
              ·
                refine ⟨7556103195228704658013781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80598434082439516352146997 7556103195228704658013781)
                ·
                  refine ⟨88548084319086382711099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7556103195228704658013781 88548084319086382711099)
                  ·
                    rfl

theorem cell23_1552021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 8].length) (baseStart_1552021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552021 prefixEnd_1552021 := by exact prefixLift 1552021
  have htrace : WordTrace (prefixWord ++ tailWord_1552021) baseStart_1552021 baseEnd_1552021 := by
    simpa [prefixWord, tailWord_1552021, baseEnd_1552021] using wordTrace_append hprefix tailTrace_1552021
  have hstable : (prefixWord ++ tailWord_1552021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552021).length < 2 ^ (prefixWord ++ tailWord_1552021).sum := by decide
  have hdescent : baseEnd_1552021 < baseStart_1552021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552075 : List Nat := [1, 1, 1, 1, 3, 2, 1, 6, 2, 3, 2]
def baseStart_1552075 : Nat := 118140960795 + 1552075 * 2 ^ 59
def prefixEnd_1552075 : Nat := 4983230072969 + 3 ^ 40 * 1552075 * 2
def baseEnd_1552075 : Nat := 796960486827120233124643

theorem tailTrace_1552075 : CollatzResearch.WordTrace tailWord_1552075 prefixEnd_1552075 796960486827120233124643 := by
  unfold tailWord_1552075
  simp only [CollatzResearch.WordTrace]
  refine ⟨56608825852104823151545679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37739217234736548767697119 56608825852104823151545679)
  ·
    refine ⟨84913238778157234727318519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56608825852104823151545679 84913238778157234727318519)
    ·
      refine ⟨127369858167235852090977779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84913238778157234727318519 127369858167235852090977779)
      ·
        refine ⟨191054787250853778136466669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127369858167235852090977779 191054787250853778136466669)
        ·
          refine ⟨71645545219070166801175001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191054787250853778136466669 71645545219070166801175001)
          ·
            refine ⟨53734158914302625100881251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71645545219070166801175001 53734158914302625100881251)
            ·
              refine ⟨80601238371453937651321877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53734158914302625100881251 80601238371453937651321877)
              ·
                refine ⟨3778183048661903327405713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80601238371453937651321877 3778183048661903327405713)
                ·
                  refine ⟨2833637286496427495554285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3778183048661903327405713 2833637286496427495554285)
                  ·
                    refine ⟨1062613982436160310832857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2833637286496427495554285 1062613982436160310832857)
                    ·
                      refine ⟨796960486827120233124643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1062613982436160310832857 796960486827120233124643)
                      ·
                        rfl

theorem cell23_1552075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 3, 2].length) (baseStart_1552075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552075 prefixEnd_1552075 := by exact prefixLift 1552075
  have htrace : WordTrace (prefixWord ++ tailWord_1552075) baseStart_1552075 baseEnd_1552075 := by
    simpa [prefixWord, tailWord_1552075, baseEnd_1552075] using wordTrace_append hprefix tailTrace_1552075
  have hstable : (prefixWord ++ tailWord_1552075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552075).length < 2 ^ (prefixWord ++ tailWord_1552075).sum := by decide
  have hdescent : baseEnd_1552075 < baseStart_1552075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552082 : List Nat := [3, 2, 2, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_1552082 : Nat := 118140960795 + 1552082 * 2 ^ 59
def prefixEnd_1552082 : Nat := 4983230072969 + 3 ^ 40 * 1552082 * 2
def baseEnd_1552082 : Nat := 796964081191701705737111

theorem tailTrace_1552082 : CollatzResearch.WordTrace tailWord_1552082 prefixEnd_1552082 796964081191701705737111 := by
  unfold tailWord_1552082
  simp only [CollatzResearch.WordTrace]
  refine ⟨14152270290769865836762625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37739387442052975564700333 14152270290769865836762625)
  ·
    refine ⟨10614202718077399377571969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14152270290769865836762625 10614202718077399377571969)
    ·
      refine ⟨7960652038558049533178977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10614202718077399377571969 7960652038558049533178977)
      ·
        refine ⟨5970489028918537149884233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7960652038558049533178977 5970489028918537149884233)
        ·
          refine ⟨4477866771688902862413175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5970489028918537149884233 4477866771688902862413175)
          ·
            refine ⟨6716800157533354293619763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4477866771688902862413175 6716800157533354293619763)
            ·
              refine ⟨10075200236300031440429645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6716800157533354293619763 10075200236300031440429645)
              ·
                refine ⟨3778200088612511790161117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10075200236300031440429645 3778200088612511790161117)
                ·
                  refine ⟨1416825033229691921310419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3778200088612511790161117 1416825033229691921310419)
                  ·
                    refine ⟨2125237549844537881965629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1416825033229691921310419 2125237549844537881965629)
                    ·
                      refine ⟨796964081191701705737111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2125237549844537881965629 796964081191701705737111)
                      ·
                        rfl

theorem cell23_1552082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_1552082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552082 prefixEnd_1552082 := by exact prefixLift 1552082
  have htrace : WordTrace (prefixWord ++ tailWord_1552082) baseStart_1552082 baseEnd_1552082 := by
    simpa [prefixWord, tailWord_1552082, baseEnd_1552082] using wordTrace_append hprefix tailTrace_1552082
  have hstable : (prefixWord ++ tailWord_1552082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552082).length < 2 ^ (prefixWord ++ tailWord_1552082).sum := by decide
  have hdescent : baseEnd_1552082 < baseStart_1552082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552139 : List Nat := [1, 1, 1, 1, 5, 1, 2, 6, 1, 2, 2]
def baseStart_1552139 : Nat := 118140960795 + 1552139 * 2 ^ 59
def prefixEnd_1552139 : Nat := 4983230072969 + 3 ^ 40 * 1552139 * 2
def baseEnd_1552139 : Nat := 796993349589007982724349

theorem tailTrace_1552139 : CollatzResearch.WordTrace tailWord_1552139 prefixEnd_1552139 796993349589007982724349 := by
  unfold tailWord_1552139
  simp only [CollatzResearch.WordTrace]
  refine ⟨56611160123872962081875471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37740773415915308054583647 56611160123872962081875471)
  ·
    refine ⟨84916740185809443122813207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56611160123872962081875471 84916740185809443122813207)
    ·
      refine ⟨127375110278714164684219811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84916740185809443122813207 127375110278714164684219811)
      ·
        refine ⟨191062665418071247026329717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127375110278714164684219811 191062665418071247026329717)
        ·
          refine ⟨17912124882944179408718411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191062665418071247026329717 17912124882944179408718411)
          ·
            refine ⟨26868187324416269113077617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17912124882944179408718411 26868187324416269113077617)
            ·
              refine ⟨20151140493312201834808213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26868187324416269113077617 20151140493312201834808213)
              ·
                refine ⟨944584710624009461006635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20151140493312201834808213 944584710624009461006635)
                ·
                  refine ⟨1416877065936014191509953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 944584710624009461006635 1416877065936014191509953)
                  ·
                    refine ⟨1062657799452010643632465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1416877065936014191509953 1062657799452010643632465)
                    ·
                      refine ⟨796993349589007982724349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1062657799452010643632465 796993349589007982724349)
                      ·
                        rfl

theorem cell23_1552139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 1, 2, 2].length) (baseStart_1552139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552139 prefixEnd_1552139 := by exact prefixLift 1552139
  have htrace : WordTrace (prefixWord ++ tailWord_1552139) baseStart_1552139 baseEnd_1552139 := by
    simpa [prefixWord, tailWord_1552139, baseEnd_1552139] using wordTrace_append hprefix tailTrace_1552139
  have hstable : (prefixWord ++ tailWord_1552139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552139).length < 2 ^ (prefixWord ++ tailWord_1552139).sum := by decide
  have hdescent : baseEnd_1552139 < baseStart_1552139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552149 : List Nat := [1, 3, 2, 1, 2, 5, 2, 1, 2, 4]
def baseStart_1552149 : Nat := 118140960795 + 1552149 * 2 ^ 59
def prefixEnd_1552149 : Nat := 4983230072969 + 3 ^ 40 * 1552149 * 2
def baseEnd_1552149 : Nat := 265666161465184314533101

theorem tailTrace_1552149 : CollatzResearch.WordTrace tailWord_1552149 prefixEnd_1552149 265666161465184314533101 := by
  unfold tailWord_1552149
  simp only [CollatzResearch.WordTrace]
  refine ⟨56611524853836733789739501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37741016569224489193159667 56611524853836733789739501)
  ·
    refine ⟨21229321820188775171152313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56611524853836733789739501 21229321820188775171152313)
    ·
      refine ⟨15921991365141581378364235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21229321820188775171152313 15921991365141581378364235)
      ·
        refine ⟨23882987047712372067546353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15921991365141581378364235 23882987047712372067546353)
        ·
          refine ⟨17912240285784279050659765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23882987047712372067546353 17912240285784279050659765)
          ·
            refine ⟨1679272526792276160999353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17912240285784279050659765 1679272526792276160999353)
            ·
              refine ⟨1259454395094207120749515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1679272526792276160999353 1259454395094207120749515)
              ·
                refine ⟨1889181592641310681124273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259454395094207120749515 1889181592641310681124273)
                ·
                  refine ⟨1416886194480983010843205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1889181592641310681124273 1416886194480983010843205)
                  ·
                    refine ⟨265666161465184314533101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1416886194480983010843205 265666161465184314533101)
                    ·
                      rfl

theorem cell23_1552149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_1552149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552149 prefixEnd_1552149 := by exact prefixLift 1552149
  have htrace : WordTrace (prefixWord ++ tailWord_1552149) baseStart_1552149 baseEnd_1552149 := by
    simpa [prefixWord, tailWord_1552149, baseEnd_1552149] using wordTrace_append hprefix tailTrace_1552149
  have hstable : (prefixWord ++ tailWord_1552149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552149).length < 2 ^ (prefixWord ++ tailWord_1552149).sum := by decide
  have hdescent : baseEnd_1552149 < baseStart_1552149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552189 : List Nat := [1, 4, 1, 4, 1, 1, 1, 4, 2, 1, 3]
def baseStart_1552189 : Nat := 118140960795 + 1552189 * 2 ^ 59
def prefixEnd_1552189 : Nat := 4983230072969 + 3 ^ 40 * 1552189 * 2
def baseEnd_1552189 : Nat := 797019023621732787099119

theorem tailTrace_1552189 : CollatzResearch.WordTrace tailWord_1552189 prefixEnd_1552189 797019023621732787099119 := by
  unfold tailWord_1552189
  simp only [CollatzResearch.WordTrace]
  refine ⟨56612983773691820621195621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37741989182461213747463747 56612983773691820621195621)
  ·
    refine ⟨10614934457567216366474179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56612983773691820621195621 10614934457567216366474179)
    ·
      refine ⟨15922401686350824549711269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10614934457567216366474179 15922401686350824549711269)
      ·
        refine ⟨2985450316190779603070863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15922401686350824549711269 2985450316190779603070863)
        ·
          refine ⟨4478175474286169404606295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2985450316190779603070863 4478175474286169404606295)
          ·
            refine ⟨6717263211429254106909443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4478175474286169404606295 6717263211429254106909443)
            ·
              refine ⟨10075894817143881160364165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6717263211429254106909443 10075894817143881160364165)
              ·
                refine ⟨1889230278214477717568281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10075894817143881160364165 1889230278214477717568281)
                ·
                  refine ⟨1416922708660858288176211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1889230278214477717568281 1416922708660858288176211)
                  ·
                    refine ⟨2125384062991287432264317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1416922708660858288176211 2125384062991287432264317)
                    ·
                      refine ⟨797019023621732787099119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2125384062991287432264317 797019023621732787099119)
                      ·
                        rfl

theorem cell23_1552189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_1552189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552189 prefixEnd_1552189 := by exact prefixLift 1552189
  have htrace : WordTrace (prefixWord ++ tailWord_1552189) baseStart_1552189 baseEnd_1552189 := by
    simpa [prefixWord, tailWord_1552189, baseEnd_1552189] using wordTrace_append hprefix tailTrace_1552189
  have hstable : (prefixWord ++ tailWord_1552189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552189).length < 2 ^ (prefixWord ++ tailWord_1552189).sum := by decide
  have hdescent : baseEnd_1552189 < baseStart_1552189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552190 : List Nat := [4, 2, 1, 2, 2, 3, 2, 2, 1, 2, 2]
def baseStart_1552190 : Nat := 118140960795 + 1552190 * 2 ^ 59
def prefixEnd_1552190 : Nat := 4983230072969 + 3 ^ 40 * 1552190 * 2
def baseEnd_1552190 : Nat := 797019537102387283186615

theorem tailTrace_1552190 : CollatzResearch.WordTrace tailWord_1552190 prefixEnd_1552190 797019537102387283186615 := by
  unfold tailWord_1552190
  simp only [CollatzResearch.WordTrace]
  refine ⟨7076627530836024723997753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37742013497792131861321349 7076627530836024723997753)
  ·
    refine ⟨5307470648127018542998315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7076627530836024723997753 5307470648127018542998315)
    ·
      refine ⟨7961205972190527814497473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5307470648127018542998315 7961205972190527814497473)
      ·
        refine ⟨5970904479142895860873105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7961205972190527814497473 5970904479142895860873105)
        ·
          refine ⟨4478178359357171895654829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5970904479142895860873105 4478178359357171895654829)
          ·
            refine ⟨1679316884758939460870561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4478178359357171895654829 1679316884758939460870561)
            ·
              refine ⟨1259487663569204595652921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1679316884758939460870561 1259487663569204595652921)
              ·
                refine ⟨944615747676903446739691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1259487663569204595652921 944615747676903446739691)
                ·
                  refine ⟨1416923621515355170109537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 944615747676903446739691 1416923621515355170109537)
                  ·
                    refine ⟨1062692716136516377582153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1416923621515355170109537 1062692716136516377582153)
                    ·
                      refine ⟨797019537102387283186615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1062692716136516377582153 797019537102387283186615)
                      ·
                        rfl

theorem cell23_1552190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_1552190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552190 prefixEnd_1552190 := by exact prefixLift 1552190
  have htrace : WordTrace (prefixWord ++ tailWord_1552190) baseStart_1552190 baseEnd_1552190 := by
    simpa [prefixWord, tailWord_1552190, baseEnd_1552190] using wordTrace_append hprefix tailTrace_1552190
  have hstable : (prefixWord ++ tailWord_1552190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552190).length < 2 ^ (prefixWord ++ tailWord_1552190).sum := by decide
  have hdescent : baseEnd_1552190 < baseStart_1552190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552263 : List Nat := [1, 1, 4, 2, 4, 1, 3, 1, 2, 2, 2]
def baseStart_1552263 : Nat := 118140960795 + 1552263 * 2 ^ 59
def prefixEnd_1552263 : Nat := 4983230072969 + 3 ^ 40 * 1552263 * 2
def baseEnd_1552263 : Nat := 797057021190165497573779

theorem tailTrace_1552263 : CollatzResearch.WordTrace tailWord_1552263 prefixEnd_1552263 797057021190165497573779 := by
  unfold tailWord_1552263
  simp only [CollatzResearch.WordTrace]
  refine ⟨56615682775423731259389443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37743788516949154172926295 56615682775423731259389443)
  ·
    refine ⟨84923524163135596889084165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56615682775423731259389443 84923524163135596889084165)
    ·
      refine ⟨15923160780587924416703281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84923524163135596889084165 15923160780587924416703281)
      ·
        refine ⟨11942370585440943312527461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15923160780587924416703281 11942370585440943312527461)
        ·
          refine ⟨2239194484770176871098899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11942370585440943312527461 2239194484770176871098899)
          ·
            refine ⟨3358791727155265306648349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2239194484770176871098899 3358791727155265306648349)
            ·
              refine ⟨1259546897683224489993131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3358791727155265306648349 1259546897683224489993131)
              ·
                refine ⟨1889320346524836734989697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259546897683224489993131 1889320346524836734989697)
                ·
                  refine ⟨1416990259893627551242273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1889320346524836734989697 1416990259893627551242273)
                  ·
                    refine ⟨1062742694920220663431705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1416990259893627551242273 1062742694920220663431705)
                    ·
                      refine ⟨797057021190165497573779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1062742694920220663431705 797057021190165497573779)
                      ·
                        rfl

theorem cell23_1552263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_1552263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552263 prefixEnd_1552263 := by exact prefixLift 1552263
  have htrace : WordTrace (prefixWord ++ tailWord_1552263) baseStart_1552263 baseEnd_1552263 := by
    simpa [prefixWord, tailWord_1552263, baseEnd_1552263] using wordTrace_append hprefix tailTrace_1552263
  have hstable : (prefixWord ++ tailWord_1552263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552263).length < 2 ^ (prefixWord ++ tailWord_1552263).sum := by decide
  have hdescent : baseEnd_1552263 < baseStart_1552263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552359 : List Nat := [1, 1, 5, 2, 3, 1, 2, 2, 6]
def baseStart_1552359 : Nat := 118140960795 + 1552359 * 2 ^ 59
def prefixEnd_1552359 : Nat := 4983230072969 + 3 ^ 40 * 1552359 * 2
def baseEnd_1552359 : Nat := 88567368370333013552593

theorem tailTrace_1552359 : CollatzResearch.WordTrace tailWord_1552359 prefixEnd_1552359 88567368370333013552593 := by
  unfold tailWord_1552359
  simp only [CollatzResearch.WordTrace]
  refine ⟨56619184183075939654884131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37746122788717293103256087 56619184183075939654884131)
  ·
    refine ⟨84928776274613909482326197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56619184183075939654884131 84928776274613909482326197)
    ·
      refine ⟨7962072775745054013968081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84928776274613909482326197 7962072775745054013968081)
      ·
        refine ⟨5971554581808790510476061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7962072775745054013968081 5971554581808790510476061)
        ·
          refine ⟨2239332968178296441428523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5971554581808790510476061 2239332968178296441428523)
          ·
            refine ⟨3358999452267444662142785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2239332968178296441428523 3358999452267444662142785)
            ·
              refine ⟨2519249589200583496607089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3358999452267444662142785 2519249589200583496607089)
              ·
                refine ⟨1889437191900437622455317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2519249589200583496607089 1889437191900437622455317)
                ·
                  refine ⟨88567368370333013552593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1889437191900437622455317 88567368370333013552593)
                  ·
                    rfl

theorem cell23_1552359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 6].length) (baseStart_1552359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552359 prefixEnd_1552359 := by exact prefixLift 1552359
  have htrace : WordTrace (prefixWord ++ tailWord_1552359) baseStart_1552359 baseEnd_1552359 := by
    simpa [prefixWord, tailWord_1552359, baseEnd_1552359] using wordTrace_append hprefix tailTrace_1552359
  have hstable : (prefixWord ++ tailWord_1552359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552359).length < 2 ^ (prefixWord ++ tailWord_1552359).sum := by decide
  have hdescent : baseEnd_1552359 < baseStart_1552359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552390 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_1552390 : Nat := 118140960795 + 1552390 * 2 ^ 59
def prefixEnd_1552390 : Nat := 4983230072969 + 3 ^ 40 * 1552390 * 2
def baseEnd_1552390 : Nat := 797122233233286500685695

theorem tailTrace_1552390 : CollatzResearch.WordTrace tailWord_1552390 prefixEnd_1552390 797122233233286500685695 := by
  unfold tailWord_1552390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1769384838936363498414457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37746876563975754632841749 1769384838936363498414457)
  ·
    refine ⟨1327038629202272623810843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1769384838936363498414457 1327038629202272623810843)
    ·
      refine ⟨1990557943803408935716265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1327038629202272623810843 1990557943803408935716265)
      ·
        refine ⟨1492918457852556701787199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1990557943803408935716265 1492918457852556701787199)
        ·
          refine ⟨2239377686778835052680799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1492918457852556701787199 2239377686778835052680799)
          ·
            refine ⟨3359066530168252579021199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2239377686778835052680799 3359066530168252579021199)
            ·
              refine ⟨5038599795252378868531799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3359066530168252579021199 5038599795252378868531799)
              ·
                refine ⟨7557899692878568302797699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5038599795252378868531799 7557899692878568302797699)
                ·
                  refine ⟨11336849539317852454196549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7557899692878568302797699 11336849539317852454196549)
                  ·
                    refine ⟨2125659288622097335161853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11336849539317852454196549 2125659288622097335161853)
                    ·
                      refine ⟨797122233233286500685695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2125659288622097335161853 797122233233286500685695)
                      ·
                        rfl

theorem cell23_1552390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_1552390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552390 prefixEnd_1552390 := by exact prefixLift 1552390
  have htrace : WordTrace (prefixWord ++ tailWord_1552390) baseStart_1552390 baseEnd_1552390 := by
    simpa [prefixWord, tailWord_1552390, baseEnd_1552390] using wordTrace_append hprefix tailTrace_1552390
  have hstable : (prefixWord ++ tailWord_1552390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552390).length < 2 ^ (prefixWord ++ tailWord_1552390).sum := by decide
  have hdescent : baseEnd_1552390 < baseStart_1552390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552392 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_1552392 : Nat := 118140960795 + 1552392 * 2 ^ 59
def prefixEnd_1552392 : Nat := 4983230072969 + 3 ^ 40 * 1552392 * 2
def baseEnd_1552392 : Nat := 797123260194595492860685

theorem tailTrace_1552392 : CollatzResearch.WordTrace tailWord_1552392 prefixEnd_1552392 797123260194595492860685 := by
  unfold tailWord_1552392
  simp only [CollatzResearch.WordTrace]
  refine ⟨28310193895978193145417715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37746925194637590860556953 28310193895978193145417715)
  ·
    refine ⟨42465290843967289718126573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28310193895978193145417715 42465290843967289718126573)
    ·
      refine ⟨15924484066487733644297465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42465290843967289718126573 15924484066487733644297465)
      ·
        refine ⟨11943363049865800233223099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15924484066487733644297465 11943363049865800233223099)
        ·
          refine ⟨17915044574798700349834649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11943363049865800233223099 17915044574798700349834649)
          ·
            refine ⟨13436283431099025262375987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17915044574798700349834649 13436283431099025262375987)
            ·
              refine ⟨20154425146648537893563981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13436283431099025262375987 20154425146648537893563981)
              ·
                refine ⟨7557909429993201710086493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20154425146648537893563981 7557909429993201710086493)
                ·
                  refine ⟨2834216036247450641282435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7557909429993201710086493 2834216036247450641282435)
                  ·
                    refine ⟨4251324054371175961923653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2834216036247450641282435 4251324054371175961923653)
                    ·
                      refine ⟨797123260194595492860685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4251324054371175961923653 797123260194595492860685)
                      ·
                        rfl

theorem cell23_1552392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_1552392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552392 prefixEnd_1552392 := by exact prefixLift 1552392
  have htrace : WordTrace (prefixWord ++ tailWord_1552392) baseStart_1552392 baseEnd_1552392 := by
    simpa [prefixWord, tailWord_1552392, baseEnd_1552392] using wordTrace_append hprefix tailTrace_1552392
  have hstable : (prefixWord ++ tailWord_1552392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552392).length < 2 ^ (prefixWord ++ tailWord_1552392).sum := by decide
  have hdescent : baseEnd_1552392 < baseStart_1552392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552397 : List Nat := [1, 7, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_1552397 : Nat := 118140960795 + 1552397 * 2 ^ 59
def prefixEnd_1552397 : Nat := 4983230072969 + 3 ^ 40 * 1552397 * 2
def baseEnd_1552397 : Nat := 265708609199289324432721

theorem tailTrace_1552397 : CollatzResearch.WordTrace tailWord_1552397 prefixEnd_1552397 265708609199289324432721 := by
  unfold tailWord_1552397
  simp only [CollatzResearch.WordTrace]
  refine ⟨56620570156938272144767445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37747046771292181429844963 56620570156938272144767445)
  ·
    refine ⟨1327044613053240753392987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 56620570156938272144767445 1327044613053240753392987)
    ·
      refine ⟨1990566919579861130089481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1327044613053240753392987 1990566919579861130089481)
      ·
        refine ⟨1492925189684895847567111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1990566919579861130089481 1492925189684895847567111)
        ·
          refine ⟨2239387784527343771350667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1492925189684895847567111 2239387784527343771350667)
          ·
            refine ⟨3359081676791015657026001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2239387784527343771350667 3359081676791015657026001)
            ·
              refine ⟨2519311257593261742769501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3359081676791015657026001 2519311257593261742769501)
              ·
                refine ⟨944741721597473153538563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2519311257593261742769501 944741721597473153538563)
                ·
                  refine ⟨1417112582396209730307845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 944741721597473153538563 1417112582396209730307845)
                  ·
                    refine ⟨265708609199289324432721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1417112582396209730307845 265708609199289324432721)
                    ·
                      rfl

theorem cell23_1552397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_1552397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552397 prefixEnd_1552397 := by exact prefixLift 1552397
  have htrace : WordTrace (prefixWord ++ tailWord_1552397) baseStart_1552397 baseEnd_1552397 := by
    simpa [prefixWord, tailWord_1552397, baseEnd_1552397] using wordTrace_append hprefix tailTrace_1552397
  have hstable : (prefixWord ++ tailWord_1552397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552397).length < 2 ^ (prefixWord ++ tailWord_1552397).sum := by decide
  have hdescent : baseEnd_1552397 < baseStart_1552397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552409 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 7, 2, 2]
def baseStart_1552409 : Nat := 118140960795 + 1552409 * 2 ^ 59
def prefixEnd_1552409 : Nat := 4983230072969 + 3 ^ 40 * 1552409 * 2
def baseEnd_1552409 : Nat := 797131989365721926348107

theorem tailTrace_1552409 : CollatzResearch.WordTrace tailWord_1552409 prefixEnd_1552409 797131989365721926348107 := by
  unfold tailWord_1552409
  simp only [CollatzResearch.WordTrace]
  refine ⟨56621007832894798194204281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37747338555263198796136187 56621007832894798194204281)
  ·
    refine ⟨42465755874671098645653211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56621007832894798194204281 42465755874671098645653211)
    ·
      refine ⟨63698633812006647968479817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42465755874671098645653211 63698633812006647968479817)
      ·
        refine ⟨47773975359004985976359863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63698633812006647968479817 47773975359004985976359863)
        ·
          refine ⟨71660963038507478964539795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47773975359004985976359863 71660963038507478964539795)
          ·
            refine ⟨107491444557761218446809693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71660963038507478964539795 107491444557761218446809693)
            ·
              refine ⟨40309291709160456917553635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107491444557761218446809693 40309291709160456917553635)
              ·
                refine ⟨60463937563740685376330453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40309291709160456917553635 60463937563740685376330453)
                ·
                  refine ⟨1417123536650172313507745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 60463937563740685376330453 1417123536650172313507745)
                  ·
                    refine ⟨1062842652487629235130809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1417123536650172313507745 1062842652487629235130809)
                    ·
                      refine ⟨797131989365721926348107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1062842652487629235130809 797131989365721926348107)
                      ·
                        rfl

theorem cell23_1552409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 2, 2].length) (baseStart_1552409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552409 prefixEnd_1552409 := by exact prefixLift 1552409
  have htrace : WordTrace (prefixWord ++ tailWord_1552409) baseStart_1552409 baseEnd_1552409 := by
    simpa [prefixWord, tailWord_1552409, baseEnd_1552409] using wordTrace_append hprefix tailTrace_1552409
  have hstable : (prefixWord ++ tailWord_1552409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552409).length < 2 ^ (prefixWord ++ tailWord_1552409).sum := by decide
  have hdescent : baseEnd_1552409 < baseStart_1552409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552415 : List Nat := [1, 1, 2, 4, 1, 2, 12]
def baseStart_1552415 : Nat := 118140960795 + 1552415 * 2 ^ 59
def prefixEnd_1552415 : Nat := 4983230072969 + 3 ^ 40 * 1552415 * 2
def baseEnd_1552415 : Nat := 9841173706785788924359

theorem tailTrace_1552415 : CollatzResearch.WordTrace tailWord_1552415 prefixEnd_1552415 9841173706785788924359 := by
  unfold tailWord_1552415
  simp only [CollatzResearch.WordTrace]
  refine ⟨56621226670873061218922699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37747484447248707479281799 56621226670873061218922699)
  ·
    refine ⟨84931840006309591828384049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56621226670873061218922699 84931840006309591828384049)
    ·
      refine ⟨63698880004732193871288037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84931840006309591828384049 63698880004732193871288037)
      ·
        refine ⟨11943540000887286350866507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63698880004732193871288037 11943540000887286350866507)
        ·
          refine ⟨17915310001330929526299761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11943540000887286350866507 17915310001330929526299761)
          ·
            refine ⟨13436482500998197144724821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17915310001330929526299761 13436482500998197144724821)
            ·
              refine ⟨9841173706785788924359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 13436482500998197144724821 9841173706785788924359)
              ·
                rfl

theorem cell23_1552415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 12].length) (baseStart_1552415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552415 prefixEnd_1552415 := by exact prefixLift 1552415
  have htrace : WordTrace (prefixWord ++ tailWord_1552415) baseStart_1552415 baseEnd_1552415 := by
    simpa [prefixWord, tailWord_1552415, baseEnd_1552415] using wordTrace_append hprefix tailTrace_1552415
  have hstable : (prefixWord ++ tailWord_1552415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552415).length < 2 ^ (prefixWord ++ tailWord_1552415).sum := by decide
  have hdescent : baseEnd_1552415 < baseStart_1552415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552449 : List Nat := [1, 2, 5, 1, 2, 1, 4, 7]
def baseStart_1552449 : Nat := 118140960795 + 1552449 * 2 ^ 59
def prefixEnd_1552449 : Nat := 4983230072969 + 3 ^ 40 * 1552449 * 2
def baseEnd_1552449 : Nat := 29524167725625991475849

theorem tailTrace_1552449 : CollatzResearch.WordTrace tailWord_1552449 prefixEnd_1552449 29524167725625991475849 := by
  unfold tailWord_1552449
  simp only [CollatzResearch.WordTrace]
  refine ⟨56622466752749885025660401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37748311168499923350440267 56622466752749885025660401)
  ·
    refine ⟨42466850064562413769245301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56622466752749885025660401 42466850064562413769245301)
    ·
      refine ⟨3981267193552726290866747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42466850064562413769245301 3981267193552726290866747)
      ·
        refine ⟨5971900790329089436300121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3981267193552726290866747 5971900790329089436300121)
        ·
          refine ⟨4478925592746817077225091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5971900790329089436300121 4478925592746817077225091)
          ·
            refine ⟨6718388389120225615837637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4478925592746817077225091 6718388389120225615837637)
            ·
              refine ⟨1259697822960042302969557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6718388389120225615837637 1259697822960042302969557)
              ·
                refine ⟨29524167725625991475849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1259697822960042302969557 29524167725625991475849)
                ·
                  rfl

theorem cell23_1552449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 7].length) (baseStart_1552449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552449 prefixEnd_1552449 := by exact prefixLift 1552449
  have htrace : WordTrace (prefixWord ++ tailWord_1552449) baseStart_1552449 baseEnd_1552449 := by
    simpa [prefixWord, tailWord_1552449, baseEnd_1552449] using wordTrace_append hprefix tailTrace_1552449
  have hstable : (prefixWord ++ tailWord_1552449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552449).length < 2 ^ (prefixWord ++ tailWord_1552449).sum := by decide
  have hdescent : baseEnd_1552449 < baseStart_1552449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552476 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_1552476 : Nat := 118140960795 + 1552476 * 2 ^ 59
def prefixEnd_1552476 : Nat := 4983230072969 + 3 ^ 40 * 1552476 * 2
def baseEnd_1552476 : Nat := 797166392569573164210299

theorem tailTrace_1552476 : CollatzResearch.WordTrace tailWord_1552476 prefixEnd_1552476 797166392569573164210299 := by
  unfold tailWord_1552476
  simp only [CollatzResearch.WordTrace]
  refine ⟨28311725761826034318446641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37748967682434712424595521 28311725761826034318446641)
  ·
    refine ⟨21233794321369525738834981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28311725761826034318446641 21233794321369525738834981)
    ·
      refine ⟨3981336435256786076031559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21233794321369525738834981 3981336435256786076031559)
      ·
        refine ⟨5972004652885179114047339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3981336435256786076031559 5972004652885179114047339)
        ·
          refine ⟨8958006979327768671071009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5972004652885179114047339 8958006979327768671071009)
          ·
            refine ⟨6718505234495826503303257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8958006979327768671071009 6718505234495826503303257)
            ·
              refine ⟨5038878925871869877477443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6718505234495826503303257 5038878925871869877477443)
              ·
                refine ⟨7558318388807804816216165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5038878925871869877477443 7558318388807804816216165)
                ·
                  refine ⟨1417184697901463403040531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7558318388807804816216165 1417184697901463403040531)
                  ·
                    refine ⟨2125777046852195104560797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1417184697901463403040531 2125777046852195104560797)
                    ·
                      refine ⟨797166392569573164210299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2125777046852195104560797 797166392569573164210299)
                      ·
                        rfl

theorem cell23_1552476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_1552476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552476 prefixEnd_1552476 := by exact prefixLift 1552476
  have htrace : WordTrace (prefixWord ++ tailWord_1552476) baseStart_1552476 baseEnd_1552476 := by
    simpa [prefixWord, tailWord_1552476, baseEnd_1552476] using wordTrace_append hprefix tailTrace_1552476
  have hstable : (prefixWord ++ tailWord_1552476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552476).length < 2 ^ (prefixWord ++ tailWord_1552476).sum := by decide
  have hdescent : baseEnd_1552476 < baseStart_1552476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552503 : List Nat := [1, 1, 3, 1, 1, 7, 1, 2, 1, 3, 2]
def baseStart_1552503 : Nat := 118140960795 + 1552503 * 2 ^ 59
def prefixEnd_1552503 : Nat := 4983230072969 + 3 ^ 40 * 1552503 * 2
def baseEnd_1552503 : Nat := 797180256547244558572675

theorem tailTrace_1552503 : CollatzResearch.WordTrace tailWord_1552503 prefixEnd_1552503 797180256547244558572675 := by
  unfold tailWord_1552503
  simp only [CollatzResearch.WordTrace]
  refine ⟨56624436294554252248126163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37749624196369501498750775 56624436294554252248126163)
  ·
    refine ⟨84936654441831378372189245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56624436294554252248126163 84936654441831378372189245)
    ·
      refine ⟨31851245415686766889570967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84936654441831378372189245 31851245415686766889570967)
      ·
        refine ⟨47776868123530150334356451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31851245415686766889570967 47776868123530150334356451)
        ·
          refine ⟨71665302185295225501534677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47776868123530150334356451 71665302185295225501534677)
          ·
            refine ⟨1679655519967856847692219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 71665302185295225501534677 1679655519967856847692219)
            ·
              refine ⟨2519483279951785271538329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1679655519967856847692219 2519483279951785271538329)
              ·
                refine ⟨1889612459963838953653747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2519483279951785271538329 1889612459963838953653747)
                ·
                  refine ⟨2834418689945758430480621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889612459963838953653747 2834418689945758430480621)
                  ·
                    refine ⟨1062907008729659411430233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2834418689945758430480621 1062907008729659411430233)
                    ·
                      refine ⟨797180256547244558572675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1062907008729659411430233 797180256547244558572675)
                      ·
                        rfl

theorem cell23_1552503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 3, 2].length) (baseStart_1552503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552503 prefixEnd_1552503 := by exact prefixLift 1552503
  have htrace : WordTrace (prefixWord ++ tailWord_1552503) baseStart_1552503 baseEnd_1552503 := by
    simpa [prefixWord, tailWord_1552503, baseEnd_1552503] using wordTrace_append hprefix tailTrace_1552503
  have hstable : (prefixWord ++ tailWord_1552503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552503).length < 2 ^ (prefixWord ++ tailWord_1552503).sum := by decide
  have hdescent : baseEnd_1552503 < baseStart_1552503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552512 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 4]
def baseStart_1552512 : Nat := 118140960795 + 1552512 * 2 ^ 59
def prefixEnd_1552512 : Nat := 4983230072969 + 3 ^ 40 * 1552512 * 2
def baseEnd_1552512 : Nat := 797184877873135023360133

theorem tailTrace_1552512 : CollatzResearch.WordTrace tailWord_1552512 prefixEnd_1552512 797184877873135023360133 := by
  unfold tailWord_1552512
  simp only [CollatzResearch.WordTrace]
  refine ⟨28312382275760823392601895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37749843034347764523469193 28312382275760823392601895)
  ·
    refine ⟨42468573413641235088902843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28312382275760823392601895 42468573413641235088902843)
    ·
      refine ⟨63702860120461852633354265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42468573413641235088902843 63702860120461852633354265)
      ·
        refine ⟨47777145090346389475015699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63702860120461852633354265 47777145090346389475015699)
        ·
          refine ⟨71665717635519584212523549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47777145090346389475015699 71665717635519584212523549)
          ·
            refine ⟨26874644113319844079696331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71665717635519584212523549 26874644113319844079696331)
            ·
              refine ⟨40311966169979766119544497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26874644113319844079696331 40311966169979766119544497)
              ·
                refine ⟨30233974627484824589658373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40311966169979766119544497 30233974627484824589658373)
                ·
                  refine ⟨5668870242653404610560945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30233974627484824589658373 5668870242653404610560945)
                  ·
                    refine ⟨4251652681990053457920709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5668870242653404610560945 4251652681990053457920709)
                    ·
                      refine ⟨797184877873135023360133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4251652681990053457920709 797184877873135023360133)
                      ·
                        rfl

theorem cell23_1552512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_1552512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552512 prefixEnd_1552512 := by exact prefixLift 1552512
  have htrace : WordTrace (prefixWord ++ tailWord_1552512) baseStart_1552512 baseEnd_1552512 := by
    simpa [prefixWord, tailWord_1552512, baseEnd_1552512] using wordTrace_append hprefix tailTrace_1552512
  have hstable : (prefixWord ++ tailWord_1552512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552512).length < 2 ^ (prefixWord ++ tailWord_1552512).sum := by decide
  have hdescent : baseEnd_1552512 < baseStart_1552512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552516 : List Nat := [2, 3, 2, 1, 2, 1, 3, 2, 1, 4, 2]
def baseStart_1552516 : Nat := 118140960795 + 1552516 * 2 ^ 59
def prefixEnd_1552516 : Nat := 4983230072969 + 3 ^ 40 * 1552516 * 2
def baseEnd_1552516 : Nat := 797186931795753007710115

theorem tailTrace_1552516 : CollatzResearch.WordTrace tailWord_1552516 prefixEnd_1552516 797186931795753007710115 := by
  unfold tailWord_1552516
  simp only [CollatzResearch.WordTrace]
  refine ⟨28312455221753577734174701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37749940295671436978899601 28312455221753577734174701)
  ·
    refine ⟨10617170708157591650315513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28312455221753577734174701 10617170708157591650315513)
    ·
      refine ⟨7962878031118193737736635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10617170708157591650315513 7962878031118193737736635)
      ·
        refine ⟨11944317046677290606604953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7962878031118193737736635 11944317046677290606604953)
        ·
          refine ⟨8958237785007967954953715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11944317046677290606604953 8958237785007967954953715)
          ·
            refine ⟨13437356677511951932430573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8958237785007967954953715 13437356677511951932430573)
            ·
              refine ⟨5039008754066981974661465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13437356677511951932430573 5039008754066981974661465)
              ·
                refine ⟨3779256565550236480996099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5039008754066981974661465 3779256565550236480996099)
                ·
                  refine ⟨5668884848325354721494149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3779256565550236480996099 5668884848325354721494149)
                  ·
                    refine ⟨1062915909061004010280153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5668884848325354721494149 1062915909061004010280153)
                    ·
                      refine ⟨797186931795753007710115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1062915909061004010280153 797186931795753007710115)
                      ·
                        rfl

theorem cell23_1552516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_1552516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552516 prefixEnd_1552516 := by exact prefixLift 1552516
  have htrace : WordTrace (prefixWord ++ tailWord_1552516) baseStart_1552516 baseEnd_1552516 := by
    simpa [prefixWord, tailWord_1552516, baseEnd_1552516] using wordTrace_append hprefix tailTrace_1552516
  have hstable : (prefixWord ++ tailWord_1552516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552516).length < 2 ^ (prefixWord ++ tailWord_1552516).sum := by decide
  have hdescent : baseEnd_1552516 < baseStart_1552516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552520 : List Nat := [2, 1, 3, 4, 1, 2, 3, 1, 1, 3, 2]
def baseStart_1552520 : Nat := 118140960795 + 1552520 * 2 ^ 59
def prefixEnd_1552520 : Nat := 4983230072969 + 3 ^ 40 * 1552520 * 2
def baseEnd_1552520 : Nat := 797188985718370992060097

theorem tailTrace_1552520 : CollatzResearch.WordTrace tailWord_1552520 prefixEnd_1552520 797188985718370992060097 := by
  unfold tailWord_1552520
  simp only [CollatzResearch.WordTrace]
  refine ⟨28312528167746332075747507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37750037556995109434330009 28312528167746332075747507)
  ·
    refine ⟨42468792251619498113621261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28312528167746332075747507 42468792251619498113621261)
    ·
      refine ⟨15925797094357311792607973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42468792251619498113621261 15925797094357311792607973)
      ·
        refine ⟨2986086955191995961113995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15925797094357311792607973 2986086955191995961113995)
        ·
          refine ⟨4479130432787993941670993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2986086955191995961113995 4479130432787993941670993)
          ·
            refine ⟨3359347824590995456253245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4479130432787993941670993 3359347824590995456253245)
            ·
              refine ⟨1259755434221623296094967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3359347824590995456253245 1259755434221623296094967)
              ·
                refine ⟨1889633151332434944142451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259755434221623296094967 1889633151332434944142451)
                ·
                  refine ⟨2834449726998652416213677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889633151332434944142451 2834449726998652416213677)
                  ·
                    refine ⟨1062918647624494656080129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2834449726998652416213677 1062918647624494656080129)
                    ·
                      refine ⟨797188985718370992060097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1062918647624494656080129 797188985718370992060097)
                      ·
                        rfl

theorem cell23_1552520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_1552520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552520 prefixEnd_1552520 := by exact prefixLift 1552520
  have htrace : WordTrace (prefixWord ++ tailWord_1552520) baseStart_1552520 baseEnd_1552520 := by
    simpa [prefixWord, tailWord_1552520, baseEnd_1552520] using wordTrace_append hprefix tailTrace_1552520
  have hstable : (prefixWord ++ tailWord_1552520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552520).length < 2 ^ (prefixWord ++ tailWord_1552520).sum := by decide
  have hdescent : baseEnd_1552520 < baseStart_1552520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552533 : List Nat := [1, 3, 2, 1, 1, 1, 6, 2, 2, 2, 2]
def baseStart_1552533 : Nat := 118140960795 + 1552533 * 2 ^ 59
def prefixEnd_1552533 : Nat := 4983230072969 + 3 ^ 40 * 1552533 * 2
def baseEnd_1552533 : Nat := 797195660966879441197537

theorem tailTrace_1552533 : CollatzResearch.WordTrace tailWord_1552533 prefixEnd_1552533 797195660966879441197537 := by
  unfold tailWord_1552533
  simp only [CollatzResearch.WordTrace]
  refine ⟨56625530484445567371718253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37750353656297044914478835 56625530484445567371718253)
  ·
    refine ⟨21234573931667087764394345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56625530484445567371718253 21234573931667087764394345)
    ·
      refine ⟨15925930448750315823295759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21234573931667087764394345 15925930448750315823295759)
      ·
        refine ⟨23888895673125473734943639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15925930448750315823295759 23888895673125473734943639)
        ·
          refine ⟨35833343509688210602415459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23888895673125473734943639 35833343509688210602415459)
          ·
            refine ⟨53750015264532315903623189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35833343509688210602415459 53750015264532315903623189)
            ·
              refine ⟨2519531965524952307982337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53750015264532315903623189 2519531965524952307982337)
              ·
                refine ⟨1889648974143714230986753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2519531965524952307982337 1889648974143714230986753)
                ·
                  refine ⟨1417236730607785673240065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1889648974143714230986753 1417236730607785673240065)
                  ·
                    refine ⟨1062927547955839254930049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1417236730607785673240065 1062927547955839254930049)
                    ·
                      refine ⟨797195660966879441197537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1062927547955839254930049 797195660966879441197537)
                      ·
                        rfl

theorem cell23_1552533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_1552533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552533 prefixEnd_1552533 := by exact prefixLift 1552533
  have htrace : WordTrace (prefixWord ++ tailWord_1552533) baseStart_1552533 baseEnd_1552533 := by
    simpa [prefixWord, tailWord_1552533, baseEnd_1552533] using wordTrace_append hprefix tailTrace_1552533
  have hstable : (prefixWord ++ tailWord_1552533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552533).length < 2 ^ (prefixWord ++ tailWord_1552533).sum := by decide
  have hdescent : baseEnd_1552533 < baseStart_1552533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552546 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_1552546 : Nat := 118140960795 + 1552546 * 2 ^ 59
def prefixEnd_1552546 : Nat := 4983230072969 + 3 ^ 40 * 1552546 * 2
def baseEnd_1552546 : Nat := 797202336215387890334977

theorem tailTrace_1552546 : CollatzResearch.WordTrace tailWord_1552546 prefixEnd_1552546 797202336215387890334977 := by
  unfold tailWord_1552546
  simp only [CollatzResearch.WordTrace]
  refine ⟨14156501158349617647985373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37750669755598980394627661 14156501158349617647985373)
  ·
    refine ⟨5308687934381106617994515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14156501158349617647985373 5308687934381106617994515)
    ·
      refine ⟨7963031901571659926991773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5308687934381106617994515 7963031901571659926991773)
      ·
        refine ⟨2986136963089372472621915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7963031901571659926991773 2986136963089372472621915)
        ·
          refine ⟨4479205444634058708932873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2986136963089372472621915 4479205444634058708932873)
          ·
            refine ⟨3359404083475544031699655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4479205444634058708932873 3359404083475544031699655)
            ·
              refine ⟨5039106125213316047549483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3359404083475544031699655 5039106125213316047549483)
              ·
                refine ⟨7558659187819974071324225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5039106125213316047549483 7558659187819974071324225)
                ·
                  refine ⟨5668994390864980553493169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7558659187819974071324225 5668994390864980553493169)
                  ·
                    refine ⟨4251745793148735415119877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5668994390864980553493169 4251745793148735415119877)
                    ·
                      refine ⟨797202336215387890334977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4251745793148735415119877 797202336215387890334977)
                      ·
                        rfl

theorem cell23_1552546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_1552546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552546 prefixEnd_1552546 := by exact prefixLift 1552546
  have htrace : WordTrace (prefixWord ++ tailWord_1552546) baseStart_1552546 baseEnd_1552546 := by
    simpa [prefixWord, tailWord_1552546, baseEnd_1552546] using wordTrace_append hprefix tailTrace_1552546
  have hstable : (prefixWord ++ tailWord_1552546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552546).length < 2 ^ (prefixWord ++ tailWord_1552546).sum := by decide
  have hdescent : baseEnd_1552546 < baseStart_1552546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552549 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 2, 3, 3]
def baseStart_1552549 : Nat := 118140960795 + 1552549 * 2 ^ 59
def prefixEnd_1552549 : Nat := 4983230072969 + 3 ^ 40 * 1552549 * 2
def baseEnd_1552549 : Nat := 797203876657351378597463

theorem tailTrace_1552549 : CollatzResearch.WordTrace tailWord_1552549 prefixEnd_1552549 797203876657351378597463 := by
  unfold tailWord_1552549
  simp only [CollatzResearch.WordTrace]
  refine ⟨56626114052387602104300701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37750742701591734736200467 56626114052387602104300701)
  ·
    refine ⟨21234792769645350789112763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56626114052387602104300701 21234792769645350789112763)
    ·
      refine ⟨31852189154468026183669145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21234792769645350789112763 31852189154468026183669145)
      ·
        refine ⟨23889141865851019637751859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31852189154468026183669145 23889141865851019637751859)
        ·
          refine ⟨35833712798776529456627789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23889141865851019637751859 35833712798776529456627789)
          ·
            refine ⟨13437642299541198546235421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35833712798776529456627789 13437642299541198546235421)
            ·
              refine ⟨5039115862327949454838283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13437642299541198546235421 5039115862327949454838283)
              ·
                refine ⟨7558673793491924182257425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5039115862327949454838283 7558673793491924182257425)
                ·
                  refine ⟨5669005345118943136693069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7558673793491924182257425 5669005345118943136693069)
                  ·
                    refine ⟨2125877004419603676259901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5669005345118943136693069 2125877004419603676259901)
                    ·
                      refine ⟨797203876657351378597463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2125877004419603676259901 797203876657351378597463)
                      ·
                        rfl

theorem cell23_1552549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_1552549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552549 prefixEnd_1552549 := by exact prefixLift 1552549
  have htrace : WordTrace (prefixWord ++ tailWord_1552549) baseStart_1552549 baseEnd_1552549 := by
    simpa [prefixWord, tailWord_1552549, baseEnd_1552549] using wordTrace_append hprefix tailTrace_1552549
  have hstable : (prefixWord ++ tailWord_1552549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552549).length < 2 ^ (prefixWord ++ tailWord_1552549).sum := by decide
  have hdescent : baseEnd_1552549 < baseStart_1552549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552559 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 4, 5, 2]
def baseStart_1552559 : Nat := 118140960795 + 1552559 * 2 ^ 59
def prefixEnd_1552559 : Nat := 4983230072969 + 3 ^ 40 * 1552559 * 2
def baseEnd_1552559 : Nat := 797209011463896339472417

theorem tailTrace_1552559 : CollatzResearch.WordTrace tailWord_1552559 prefixEnd_1552559 797209011463896339472417 := by
  unfold tailWord_1552559
  simp only [CollatzResearch.WordTrace]
  refine ⟨56626478782351373812164731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37750985854900915874776487 56626478782351373812164731)
  ·
    refine ⟨84939718173527060718247097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56626478782351373812164731 84939718173527060718247097)
    ·
      refine ⟨63704788630145295538685323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84939718173527060718247097 63704788630145295538685323)
      ·
        refine ⟨95557182945217943308027985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63704788630145295538685323 95557182945217943308027985)
        ·
          refine ⟨71667887208913457481020989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95557182945217943308027985 71667887208913457481020989)
          ·
            refine ⟨26875457703342546555382871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71667887208913457481020989 26875457703342546555382871)
            ·
              refine ⟨40313186555013819833074307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26875457703342546555382871 40313186555013819833074307)
              ·
                refine ⟨60469779832520729749611461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40313186555013819833074307 60469779832520729749611461)
                ·
                  refine ⟨11338083718597636828052149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60469779832520729749611461 11338083718597636828052149)
                  ·
                    refine ⟨1062945348618528452629889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11338083718597636828052149 1062945348618528452629889)
                    ·
                      refine ⟨797209011463896339472417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1062945348618528452629889 797209011463896339472417)
                      ·
                        rfl

theorem cell23_1552559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 5, 2].length) (baseStart_1552559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552559 prefixEnd_1552559 := by exact prefixLift 1552559
  have htrace : WordTrace (prefixWord ++ tailWord_1552559) baseStart_1552559 baseEnd_1552559 := by
    simpa [prefixWord, tailWord_1552559, baseEnd_1552559] using wordTrace_append hprefix tailTrace_1552559
  have hstable : (prefixWord ++ tailWord_1552559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552559).length < 2 ^ (prefixWord ++ tailWord_1552559).sum := by decide
  have hdescent : baseEnd_1552559 < baseStart_1552559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552609 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 3, 4, 3]
def baseStart_1552609 : Nat := 118140960795 + 1552609 * 2 ^ 59
def prefixEnd_1552609 : Nat := 4983230072969 + 3 ^ 40 * 1552609 * 2
def baseEnd_1552609 : Nat := 797234685496621143847187

theorem tailTrace_1552609 : CollatzResearch.WordTrace tailWord_1552609 prefixEnd_1552609 797234685496621143847187 := by
  unfold tailWord_1552609
  simp only [CollatzResearch.WordTrace]
  refine ⟨56628302432170232351484881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37752201621446821567656587 56628302432170232351484881)
  ·
    refine ⟨42471226824127674263613661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56628302432170232351484881 42471226824127674263613661)
    ·
      refine ⟨15926710059047877848855123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42471226824127674263613661 15926710059047877848855123)
      ·
        refine ⟨23890065088571816773282685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15926710059047877848855123 23890065088571816773282685)
        ·
          refine ⟨8958774408214431289981007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23890065088571816773282685 8958774408214431289981007)
          ·
            refine ⟨13438161612321646934971511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8958774408214431289981007 13438161612321646934971511)
            ·
              refine ⟨20157242418482470402457267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13438161612321646934971511 20157242418482470402457267)
              ·
                refine ⟨30235863627723705603685901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20157242418482470402457267 30235863627723705603685901)
                ·
                  refine ⟨11338448860396389601382213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30235863627723705603685901 11338448860396389601382213)
                  ·
                    refine ⟨2125959161324323050259165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11338448860396389601382213 2125959161324323050259165)
                    ·
                      refine ⟨797234685496621143847187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2125959161324323050259165 797234685496621143847187)
                      ·
                        rfl

theorem cell23_1552609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_1552609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552609 prefixEnd_1552609 := by exact prefixLift 1552609
  have htrace : WordTrace (prefixWord ++ tailWord_1552609) baseStart_1552609 baseEnd_1552609 := by
    simpa [prefixWord, tailWord_1552609, baseEnd_1552609] using wordTrace_append hprefix tailTrace_1552609
  have hstable : (prefixWord ++ tailWord_1552609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552609).length < 2 ^ (prefixWord ++ tailWord_1552609).sum := by decide
  have hdescent : baseEnd_1552609 < baseStart_1552609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552616 : List Nat := [2, 1, 4, 1, 2, 2, 2, 2, 3, 4]
def baseStart_1552616 : Nat := 118140960795 + 1552616 * 2 ^ 59
def prefixEnd_1552616 : Nat := 4983230072969 + 3 ^ 40 * 1552616 * 2
def baseEnd_1552616 : Nat := 265746093287067538819885

theorem tailTrace_1552616 : CollatzResearch.WordTrace tailWord_1552616 prefixEnd_1552616 265746093287067538819885 := by
  unfold tailWord_1552616
  simp only [CollatzResearch.WordTrace]
  refine ⟨28314278871572436273494851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37752371828763248364659801 28314278871572436273494851)
  ·
    refine ⟨42471418307358654410242277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28314278871572436273494851 42471418307358654410242277)
    ·
      refine ⟨7963390932629747701920427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42471418307358654410242277 7963390932629747701920427)
      ·
        refine ⟨11945086398944621552880641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7963390932629747701920427 11945086398944621552880641)
        ·
          refine ⟨8958814799208466164660481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11945086398944621552880641 8958814799208466164660481)
          ·
            refine ⟨6719111099406349623495361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8958814799208466164660481 6719111099406349623495361)
            ·
              refine ⟨5039333324554762217621521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6719111099406349623495361 5039333324554762217621521)
              ·
                refine ⟨3779499993416071663216141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5039333324554762217621521 3779499993416071663216141)
                ·
                  refine ⟨1417312497531026873706053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3779499993416071663216141 1417312497531026873706053)
                  ·
                    refine ⟨265746093287067538819885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1417312497531026873706053 265746093287067538819885)
                    ·
                      rfl

theorem cell23_1552616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_1552616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552616 prefixEnd_1552616 := by exact prefixLift 1552616
  have htrace : WordTrace (prefixWord ++ tailWord_1552616) baseStart_1552616 baseEnd_1552616 := by
    simpa [prefixWord, tailWord_1552616, baseEnd_1552616] using wordTrace_append hprefix tailTrace_1552616
  have hstable : (prefixWord ++ tailWord_1552616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552616).length < 2 ^ (prefixWord ++ tailWord_1552616).sum := by decide
  have hdescent : baseEnd_1552616 < baseStart_1552616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552626 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 1, 4, 3]
def baseStart_1552626 : Nat := 118140960795 + 1552626 * 2 ^ 59
def prefixEnd_1552626 : Nat := 4983230072969 + 3 ^ 40 * 1552626 * 2
def baseEnd_1552626 : Nat := 797243414667747577334609

theorem tailTrace_1552626 : CollatzResearch.WordTrace tailWord_1552626 prefixEnd_1552626 797243414667747577334609 := by
  unfold tailWord_1552626
  simp only [CollatzResearch.WordTrace]
  refine ⟨14157230618277161063713433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37752614982072429503235821 14157230618277161063713433)
  ·
    refine ⟨10617922963707870797785075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14157230618277161063713433 10617922963707870797785075)
    ·
      refine ⟨15926884445561806196677613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10617922963707870797785075 15926884445561806196677613)
      ·
        refine ⟨5972581667085677323754105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15926884445561806196677613 5972581667085677323754105)
        ·
          refine ⟨4479436250314257992815579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5972581667085677323754105 4479436250314257992815579)
          ·
            refine ⟨6719154375471386989223369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4479436250314257992815579 6719154375471386989223369)
            ·
              refine ⟨5039365781603540241917527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6719154375471386989223369 5039365781603540241917527)
              ·
                refine ⟨7559048672405310362876291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5039365781603540241917527 7559048672405310362876291)
                ·
                  refine ⟨11338573008607965544314437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7559048672405310362876291 11338573008607965544314437)
                  ·
                    refine ⟨2125982439113993539558957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11338573008607965544314437 2125982439113993539558957)
                    ·
                      refine ⟨797243414667747577334609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2125982439113993539558957 797243414667747577334609)
                      ·
                        rfl

theorem cell23_1552626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_1552626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552626 prefixEnd_1552626 := by exact prefixLift 1552626
  have htrace : WordTrace (prefixWord ++ tailWord_1552626) baseStart_1552626 baseEnd_1552626 := by
    simpa [prefixWord, tailWord_1552626, baseEnd_1552626] using wordTrace_append hprefix tailTrace_1552626
  have hstable : (prefixWord ++ tailWord_1552626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552626).length < 2 ^ (prefixWord ++ tailWord_1552626).sum := by decide
  have hdescent : baseEnd_1552626 < baseStart_1552626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552663 : List Nat := [1, 1, 3, 4, 1, 4, 2, 1, 6]
def baseStart_1552663 : Nat := 118140960795 + 1552663 * 2 ^ 59
def prefixEnd_1552663 : Nat := 4983230072969 + 3 ^ 40 * 1552663 * 2
def baseEnd_1552663 : Nat := 88584712605773770285771

theorem tailTrace_1552663 : CollatzResearch.WordTrace tailWord_1552663 prefixEnd_1552663 88584712605773770285771 := by
  unfold tailWord_1552663
  simp only [CollatzResearch.WordTrace]
  refine ⟨56630271973974599573950643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37753514649316399715967095 56630271973974599573950643)
  ·
    refine ⟨84945407960961899360925965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56630271973974599573950643 84945407960961899360925965)
    ·
      refine ⟨31854527985360712260347237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84945407960961899360925965 31854527985360712260347237)
      ·
        refine ⟨5972723997255133548815107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31854527985360712260347237 5972723997255133548815107)
        ·
          refine ⟨8959085995882700323222661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5972723997255133548815107 8959085995882700323222661)
          ·
            refine ⟨1679828624228006310604249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8959085995882700323222661 1679828624228006310604249)
            ·
              refine ⟨1259871468171004732953187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1679828624228006310604249 1259871468171004732953187)
              ·
                refine ⟨1889807202256507099429781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259871468171004732953187 1889807202256507099429781)
                ·
                  refine ⟨88584712605773770285771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1889807202256507099429781 88584712605773770285771)
                  ·
                    rfl

theorem cell23_1552663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 6].length) (baseStart_1552663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552663 prefixEnd_1552663 := by exact prefixLift 1552663
  have htrace : WordTrace (prefixWord ++ tailWord_1552663) baseStart_1552663 baseEnd_1552663 := by
    simpa [prefixWord, tailWord_1552663, baseEnd_1552663] using wordTrace_append hprefix tailTrace_1552663
  have hstable : (prefixWord ++ tailWord_1552663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552663).length < 2 ^ (prefixWord ++ tailWord_1552663).sum := by decide
  have hdescent : baseEnd_1552663 < baseStart_1552663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552676 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 3, 5]
def baseStart_1552676 : Nat := 118140960795 + 1552676 * 2 ^ 59
def prefixEnd_1552676 : Nat := 4983230072969 + 3 ^ 40 * 1552676 * 2
def baseEnd_1552676 : Nat := 265756362900157460569793

theorem tailTrace_1552676 : CollatzResearch.WordTrace tailWord_1552676 prefixEnd_1552676 265756362900157460569793 := by
  unfold tailWord_1552676
  simp only [CollatzResearch.WordTrace]
  refine ⟨28315373061463751397086941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37753830748618335196115921 28315373061463751397086941)
  ·
    refine ⟨10618264898048906773907603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28315373061463751397086941 10618264898048906773907603)
    ·
      refine ⟨15927397347073360160861405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10618264898048906773907603 15927397347073360160861405)
      ·
        refine ⟨5972774005152510060323027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15927397347073360160861405 5972774005152510060323027)
        ·
          refine ⟨8959161007728765090484541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5972774005152510060323027 8959161007728765090484541)
          ·
            refine ⟨3359685377898286908931703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8959161007728765090484541 3359685377898286908931703)
            ·
              refine ⟨5039528066847430363397555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3359685377898286908931703 5039528066847430363397555)
              ·
                refine ⟨7559292100271145545096333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5039528066847430363397555 7559292100271145545096333)
                ·
                  refine ⟨2834734537601679579411125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7559292100271145545096333 2834734537601679579411125)
                  ·
                    refine ⟨265756362900157460569793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2834734537601679579411125 265756362900157460569793)
                    ·
                      rfl

theorem cell23_1552676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_1552676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552676 prefixEnd_1552676 := by exact prefixLift 1552676
  have htrace : WordTrace (prefixWord ++ tailWord_1552676) baseStart_1552676 baseEnd_1552676 := by
    simpa [prefixWord, tailWord_1552676, baseEnd_1552676] using wordTrace_append hprefix tailTrace_1552676
  have hstable : (prefixWord ++ tailWord_1552676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552676).length < 2 ^ (prefixWord ++ tailWord_1552676).sum := by decide
  have hdescent : baseEnd_1552676 < baseStart_1552676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552693 : List Nat := [1, 3, 3, 1, 2, 1, 5, 1, 1, 5]
def baseStart_1552693 : Nat := 118140960795 + 1552693 * 2 ^ 59
def prefixEnd_1552693 : Nat := 4983230072969 + 3 ^ 40 * 1552693 * 2
def baseEnd_1552693 : Nat := 265759272623866271732267

theorem tailTrace_1552693 : CollatzResearch.WordTrace tailWord_1552693 prefixEnd_1552693 265759272623866271732267 := by
  unfold tailWord_1552693
  simp only [CollatzResearch.WordTrace]
  refine ⟨56631366163865914697542733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37754244109243943131695155 56631366163865914697542733)
  ·
    refine ⟨21236762311449718011578525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56631366163865914697542733 21236762311449718011578525)
    ·
      refine ⟨7963785866793644254341947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21236762311449718011578525 7963785866793644254341947)
      ·
        refine ⟨11945678800190466381512921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7963785866793644254341947 11945678800190466381512921)
        ·
          refine ⟨8959259100142849786134691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11945678800190466381512921 8959259100142849786134691)
          ·
            refine ⟨13438888650214274679202037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8959259100142849786134691 13438888650214274679202037)
            ·
              refine ⟨1259895810957588251175191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13438888650214274679202037 1259895810957588251175191)
              ·
                refine ⟨1889843716436382376762787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259895810957588251175191 1889843716436382376762787)
                ·
                  refine ⟨2834765574654573565144181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889843716436382376762787 2834765574654573565144181)
                  ·
                    refine ⟨265759272623866271732267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2834765574654573565144181 265759272623866271732267)
                    ·
                      rfl

theorem cell23_1552693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_1552693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552693 prefixEnd_1552693 := by exact prefixLift 1552693
  have htrace : WordTrace (prefixWord ++ tailWord_1552693) baseStart_1552693 baseEnd_1552693 := by
    simpa [prefixWord, tailWord_1552693, baseEnd_1552693] using wordTrace_append hprefix tailTrace_1552693
  have hstable : (prefixWord ++ tailWord_1552693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552693).length < 2 ^ (prefixWord ++ tailWord_1552693).sum := by decide
  have hdescent : baseEnd_1552693 < baseStart_1552693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552696 : List Nat := [2, 1, 2, 1, 3, 1, 2, 5, 1, 1, 4]
def baseStart_1552696 : Nat := 118140960795 + 1552696 * 2 ^ 59
def prefixEnd_1552696 : Nat := 4983230072969 + 3 ^ 40 * 1552696 * 2
def baseEnd_1552696 : Nat := 797279358313562303459287

theorem tailTrace_1552696 : CollatzResearch.WordTrace tailWord_1552696 prefixEnd_1552696 797279358313562303459287 := by
  unfold tailWord_1552696
  simp only [CollatzResearch.WordTrace]
  refine ⟨28315737791427523104950971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37754317055236697473267961 28315737791427523104950971)
  ·
    refine ⟨42473606687141284657426457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28315737791427523104950971 42473606687141284657426457)
    ·
      refine ⟨31855205015355963493069843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42473606687141284657426457 31855205015355963493069843)
      ·
        refine ⟨47782807523033945239604765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31855205015355963493069843 47782807523033945239604765)
        ·
          refine ⟨17918552821137729464851787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47782807523033945239604765 17918552821137729464851787)
          ·
            refine ⟨26877829231706594197277681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17918552821137729464851787 26877829231706594197277681)
            ·
              refine ⟨20158371923779945647958261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26877829231706594197277681 20158371923779945647958261)
              ·
                refine ⟨1889847367854369904496087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20158371923779945647958261 1889847367854369904496087)
                ·
                  refine ⟨2834771051781554856744131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889847367854369904496087 2834771051781554856744131)
                  ·
                    refine ⟨4252156577672332285116197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2834771051781554856744131 4252156577672332285116197)
                    ·
                      refine ⟨797279358313562303459287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4252156577672332285116197 797279358313562303459287)
                      ·
                        rfl

theorem cell23_1552696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 1, 1, 4].length) (baseStart_1552696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552696 prefixEnd_1552696 := by exact prefixLift 1552696
  have htrace : WordTrace (prefixWord ++ tailWord_1552696) baseStart_1552696 baseEnd_1552696 := by
    simpa [prefixWord, tailWord_1552696, baseEnd_1552696] using wordTrace_append hprefix tailTrace_1552696
  have hstable : (prefixWord ++ tailWord_1552696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552696).length < 2 ^ (prefixWord ++ tailWord_1552696).sum := by decide
  have hdescent : baseEnd_1552696 < baseStart_1552696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552713 : List Nat := [1, 2, 1, 1, 2, 3, 1, 5, 3, 2, 2]
def baseStart_1552713 : Nat := 118140960795 + 1552713 * 2 ^ 59
def prefixEnd_1552713 : Nat := 4983230072969 + 3 ^ 40 * 1552713 * 2
def baseEnd_1552713 : Nat := 797288087484688736946709

theorem tailTrace_1552713 : CollatzResearch.WordTrace tailWord_1552713 prefixEnd_1552713 797288087484688736946709 := by
  unfold tailWord_1552713
  simp only [CollatzResearch.WordTrace]
  refine ⟨56632095623793458113270793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37754730415862305408847195 56632095623793458113270793)
  ·
    refine ⟨42474071717845093584953095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56632095623793458113270793 42474071717845093584953095)
    ·
      refine ⟨63711107576767640377429643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42474071717845093584953095 63711107576767640377429643)
      ·
        refine ⟨95566661365151460566144465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63711107576767640377429643 95566661365151460566144465)
        ·
          refine ⟨71674996023863595424608349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95566661365151460566144465 71674996023863595424608349)
          ·
            refine ⟨26878123508948848284228131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71674996023863595424608349 26878123508948848284228131)
            ·
              refine ⟨40317185263423272426342197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26878123508948848284228131 40317185263423272426342197)
              ·
                refine ⟨3779736118445931789969581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40317185263423272426342197 3779736118445931789969581)
                ·
                  refine ⟨1417401044417224421238593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3779736118445931789969581 1417401044417224421238593)
                  ·
                    refine ⟨1063050783312918315928945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1417401044417224421238593 1063050783312918315928945)
                    ·
                      refine ⟨797288087484688736946709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1063050783312918315928945 797288087484688736946709)
                      ·
                        rfl

theorem cell23_1552713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 2, 2].length) (baseStart_1552713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552713 prefixEnd_1552713 := by exact prefixLift 1552713
  have htrace : WordTrace (prefixWord ++ tailWord_1552713) baseStart_1552713 baseEnd_1552713 := by
    simpa [prefixWord, tailWord_1552713, baseEnd_1552713] using wordTrace_append hprefix tailTrace_1552713
  have hstable : (prefixWord ++ tailWord_1552713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552713).length < 2 ^ (prefixWord ++ tailWord_1552713).sum := by decide
  have hdescent : baseEnd_1552713 < baseStart_1552713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552716 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 5, 2, 3]
def baseStart_1552716 : Nat := 118140960795 + 1552716 * 2 ^ 59
def prefixEnd_1552716 : Nat := 4983230072969 + 3 ^ 40 * 1552716 * 2
def baseEnd_1552716 : Nat := 797289627926652225209195

theorem tailTrace_1552716 : CollatzResearch.WordTrace tailWord_1552716 prefixEnd_1552716 797289627926652225209195 := by
  unfold tailWord_1552716
  simp only [CollatzResearch.WordTrace]
  refine ⟨28316102521391294812815001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37754803361855059750420001 28316102521391294812815001)
  ·
    refine ⟨21237076891043471109611251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28316102521391294812815001 21237076891043471109611251)
    ·
      refine ⟨31855615336565206664416877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21237076891043471109611251 31855615336565206664416877)
      ·
        refine ⟨11945855751211952499156329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31855615336565206664416877 11945855751211952499156329)
        ·
          refine ⟨8959391813408964374367247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11945855751211952499156329 8959391813408964374367247)
          ·
            refine ⟨13439087720113446561550871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8959391813408964374367247 13439087720113446561550871)
            ·
              refine ⟨20158631580170169842326307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13439087720113446561550871 20158631580170169842326307)
              ·
                refine ⟨30237947370255254763489461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20158631580170169842326307 30237947370255254763489461)
                ·
                  refine ⟨2834807565961430134077137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30237947370255254763489461 2834807565961430134077137)
                  ·
                    refine ⟨2126105674471072600557853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2834807565961430134077137 2126105674471072600557853)
                    ·
                      refine ⟨797289627926652225209195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2126105674471072600557853 797289627926652225209195)
                      ·
                        rfl

theorem cell23_1552716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_1552716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552716 prefixEnd_1552716 := by exact prefixLift 1552716
  have htrace : WordTrace (prefixWord ++ tailWord_1552716) baseStart_1552716 baseEnd_1552716 := by
    simpa [prefixWord, tailWord_1552716, baseEnd_1552716] using wordTrace_append hprefix tailTrace_1552716
  have hstable : (prefixWord ++ tailWord_1552716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552716).length < 2 ^ (prefixWord ++ tailWord_1552716).sum := by decide
  have hdescent : baseEnd_1552716 < baseStart_1552716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552759 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 5]
def baseStart_1552759 : Nat := 118140960795 + 1552759 * 2 ^ 59
def prefixEnd_1552759 : Nat := 4983230072969 + 3 ^ 40 * 1552759 * 2
def baseEnd_1552759 : Nat := 797311707594795556971497

theorem tailTrace_1552759 : CollatzResearch.WordTrace tailWord_1552759 prefixEnd_1552759 797311707594795556971497 := by
  unfold tailWord_1552759
  simp only [CollatzResearch.WordTrace]
  refine ⟨56633773381626807969445331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37755848921084538646296887 56633773381626807969445331)
  ·
    refine ⟨84950660072440211954167997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56633773381626807969445331 84950660072440211954167997)
    ·
      refine ⟨31856497527165079482812999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84950660072440211954167997 31856497527165079482812999)
      ·
        refine ⟨47784746290747619224219499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31856497527165079482812999 47784746290747619224219499)
        ·
          refine ⟨71677119436121428836329249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47784746290747619224219499 71677119436121428836329249)
          ·
            refine ⟨53757839577091071627246937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71677119436121428836329249 53757839577091071627246937)
            ·
              refine ⟨40318379682818303720435203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53757839577091071627246937 40318379682818303720435203)
              ·
                refine ⟨60477569524227455580652805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40318379682818303720435203 60477569524227455580652805)
                ·
                  refine ⟨11339544285792647921372401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60477569524227455580652805 11339544285792647921372401)
                  ·
                    refine ⟨8504658214344485941029301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11339544285792647921372401 8504658214344485941029301)
                    ·
                      refine ⟨797311707594795556971497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8504658214344485941029301 797311707594795556971497)
                      ·
                        rfl

theorem cell23_1552759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_1552759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552759 prefixEnd_1552759 := by exact prefixLift 1552759
  have htrace : WordTrace (prefixWord ++ tailWord_1552759) baseStart_1552759 baseEnd_1552759 := by
    simpa [prefixWord, tailWord_1552759, baseEnd_1552759] using wordTrace_append hprefix tailTrace_1552759
  have hstable : (prefixWord ++ tailWord_1552759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552759).length < 2 ^ (prefixWord ++ tailWord_1552759).sum := by decide
  have hdescent : baseEnd_1552759 < baseStart_1552759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552763 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 4, 1, 3]
def baseStart_1552763 : Nat := 118140960795 + 1552763 * 2 ^ 59
def prefixEnd_1552763 : Nat := 4983230072969 + 3 ^ 40 * 1552763 * 2
def baseEnd_1552763 : Nat := 797313761517413541321479

theorem tailTrace_1552763 : CollatzResearch.WordTrace tailWord_1552763 prefixEnd_1552763 797313761517413541321479 := by
  unfold tailWord_1552763
  simp only [CollatzResearch.WordTrace]
  refine ⟨56633919273612316652590943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37755946182408211101727295 56633919273612316652590943)
  ·
    refine ⟨84950878910418474978886415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56633919273612316652590943 84950878910418474978886415)
    ·
      refine ⟨127426318365627712468329623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84950878910418474978886415 127426318365627712468329623)
      ·
        refine ⟨191139477548441568702494435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127426318365627712468329623 191139477548441568702494435)
        ·
          refine ⟨286709216322662353053741653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191139477548441568702494435 286709216322662353053741653)
          ·
            refine ⟨3359873628781199449848535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 286709216322662353053741653 3359873628781199449848535)
            ·
              refine ⟨5039810443171799174772803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3359873628781199449848535 5039810443171799174772803)
              ·
                refine ⟨7559715664757698762159205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5039810443171799174772803 7559715664757698762159205)
                ·
                  refine ⟨1417446687142068517904851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7559715664757698762159205 1417446687142068517904851)
                  ·
                    refine ⟨2126170030713102776857277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1417446687142068517904851 2126170030713102776857277)
                    ·
                      refine ⟨797313761517413541321479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2126170030713102776857277 797313761517413541321479)
                      ·
                        rfl

theorem cell23_1552763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 1, 3].length) (baseStart_1552763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552763 prefixEnd_1552763 := by exact prefixLift 1552763
  have htrace : WordTrace (prefixWord ++ tailWord_1552763) baseStart_1552763 baseEnd_1552763 := by
    simpa [prefixWord, tailWord_1552763, baseEnd_1552763] using wordTrace_append hprefix tailTrace_1552763
  have hstable : (prefixWord ++ tailWord_1552763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552763).length < 2 ^ (prefixWord ++ tailWord_1552763).sum := by decide
  have hdescent : baseEnd_1552763 < baseStart_1552763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552809 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 9]
def baseStart_1552809 : Nat := 118140960795 + 1552809 * 2 ^ 59
def prefixEnd_1552809 : Nat := 4983230072969 + 3 ^ 40 * 1552809 * 2
def baseEnd_1552809 : Nat := 88593042403057817927363

theorem tailTrace_1552809 : CollatzResearch.WordTrace tailWord_1552809 prefixEnd_1552809 88593042403057817927363 := by
  unfold tailWord_1552809
  simp only [CollatzResearch.WordTrace]
  refine ⟨56635597031445666508765481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37757064687630444339176987 56635597031445666508765481)
  ·
    refine ⟨42476697773584249881574111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56635597031445666508765481 42476697773584249881574111)
    ·
      refine ⟨63715046660376374822361167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42476697773584249881574111 63715046660376374822361167)
      ·
        refine ⟨95572569990564562233541751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63715046660376374822361167 95572569990564562233541751)
        ·
          refine ⟨143358854985846843350312627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95572569990564562233541751 143358854985846843350312627)
          ·
            refine ⟨215038282478770265025468941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143358854985846843350312627 215038282478770265025468941)
            ·
              refine ⟨80639355929538849384550853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215038282478770265025468941 80639355929538849384550853)
              ·
                refine ⟨15119879236788534259603285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80639355929538849384550853 15119879236788534259603285)
                ·
                  refine ⟨88593042403057817927363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15119879236788534259603285 88593042403057817927363)
                  ·
                    rfl

theorem cell23_1552809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 9].length) (baseStart_1552809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552809 prefixEnd_1552809 := by exact prefixLift 1552809
  have htrace : WordTrace (prefixWord ++ tailWord_1552809) baseStart_1552809 baseEnd_1552809 := by
    simpa [prefixWord, tailWord_1552809, baseEnd_1552809] using wordTrace_append hprefix tailTrace_1552809
  have hstable : (prefixWord ++ tailWord_1552809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552809).length < 2 ^ (prefixWord ++ tailWord_1552809).sum := by decide
  have hdescent : baseEnd_1552809 < baseStart_1552809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552877 : List Nat := [1, 5, 1, 3, 1, 1, 4, 2, 5]
def baseStart_1552877 : Nat := 118140960795 + 1552877 * 2 ^ 59
def prefixEnd_1552877 : Nat := 4983230072969 + 3 ^ 40 * 1552877 * 2
def baseEnd_1552877 : Nat := 88596922034669566143995

theorem tailTrace_1552877 : CollatzResearch.WordTrace tailWord_1552877 prefixEnd_1552877 88596922034669566143995 := by
  unfold tailWord_1552877
  simp only [CollatzResearch.WordTrace]
  refine ⟨56638077195199314122240885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37758718130132876081493923 56638077195199314122240885)
  ·
    refine ⟨5309819737049935698960083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56638077195199314122240885 5309819737049935698960083)
    ·
      refine ⟨7964729605574903548440125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5309819737049935698960083 7964729605574903548440125)
      ·
        refine ⟨2986773602090588830665047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7964729605574903548440125 2986773602090588830665047)
        ·
          refine ⟨4480160403135883245997571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2986773602090588830665047 4480160403135883245997571)
          ·
            refine ⟨6720240604703824868996357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4480160403135883245997571 6720240604703824868996357)
            ·
              refine ⟨1260045113381967162936817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6720240604703824868996357 1260045113381967162936817)
              ·
                refine ⟨945033835036475372202613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1260045113381967162936817 945033835036475372202613)
                ·
                  refine ⟨88596922034669566143995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 945033835036475372202613 88596922034669566143995)
                  ·
                    rfl

theorem cell23_1552877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_1552877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552877 prefixEnd_1552877 := by exact prefixLift 1552877
  have htrace : WordTrace (prefixWord ++ tailWord_1552877) baseStart_1552877 baseEnd_1552877 := by
    simpa [prefixWord, tailWord_1552877, baseEnd_1552877] using wordTrace_append hprefix tailTrace_1552877
  have hstable : (prefixWord ++ tailWord_1552877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552877).length < 2 ^ (prefixWord ++ tailWord_1552877).sum := by decide
  have hdescent : baseEnd_1552877 < baseStart_1552877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552910 : List Nat := [4, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4]
def baseStart_1552910 : Nat := 118140960795 + 1552910 * 2 ^ 59
def prefixEnd_1552910 : Nat := 4983230072969 + 3 ^ 40 * 1552910 * 2
def baseEnd_1552910 : Nat := 797389243173624466183303

theorem tailTrace_1552910 : CollatzResearch.WordTrace tailWord_1552910 prefixEnd_1552910 797389243173624466183303 := by
  unfold tailWord_1552910
  simp only [CollatzResearch.WordTrace]
  refine ⟨7079910100509970094774023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37759520536053173838794789 7079910100509970094774023)
  ·
    refine ⟨10619865150764955142161035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7079910100509970094774023 10619865150764955142161035)
    ·
      refine ⟨15929797726147432713241553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10619865150764955142161035 15929797726147432713241553)
      ·
        refine ⟨11947348294610574534931165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15929797726147432713241553 11947348294610574534931165)
        ·
          refine ⟨4480255610478965450599187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11947348294610574534931165 4480255610478965450599187)
          ·
            refine ⟨6720383415718448175898781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4480255610478965450599187 6720383415718448175898781)
            ·
              refine ⟨2520143780894418065962043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6720383415718448175898781 2520143780894418065962043)
              ·
                refine ⟨3780215671341627098943065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2520143780894418065962043 3780215671341627098943065)
                ·
                  refine ⟨2835161753506220324207299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3780215671341627098943065 2835161753506220324207299)
                  ·
                    refine ⟨4252742630259330486310949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2835161753506220324207299 4252742630259330486310949)
                    ·
                      refine ⟨797389243173624466183303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4252742630259330486310949 797389243173624466183303)
                      ·
                        rfl

theorem cell23_1552910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_1552910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552910 prefixEnd_1552910 := by exact prefixLift 1552910
  have htrace : WordTrace (prefixWord ++ tailWord_1552910) baseStart_1552910 baseEnd_1552910 := by
    simpa [prefixWord, tailWord_1552910, baseEnd_1552910] using wordTrace_append hprefix tailTrace_1552910
  have hstable : (prefixWord ++ tailWord_1552910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552910).length < 2 ^ (prefixWord ++ tailWord_1552910).sum := by decide
  have hdescent : baseEnd_1552910 < baseStart_1552910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552913 : List Nat := [1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 3]
def baseStart_1552913 : Nat := 118140960795 + 1552913 * 2 ^ 59
def prefixEnd_1552913 : Nat := 4983230072969 + 3 ^ 40 * 1552913 * 2
def baseEnd_1552913 : Nat := 797390783615587954445789

theorem tailTrace_1552913 : CollatzResearch.WordTrace tailWord_1552913 prefixEnd_1552913 797390783615587954445789 := by
  unfold tailWord_1552913
  simp only [CollatzResearch.WordTrace]
  refine ⟨56639390223068892270551393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37759593482045928180367595 56639390223068892270551393)
  ·
    refine ⟨42479542667301669202913545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56639390223068892270551393 42479542667301669202913545)
    ·
      refine ⟨31859657000476251902185159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42479542667301669202913545 31859657000476251902185159)
      ·
        refine ⟨47789485500714377853277739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31859657000476251902185159 47789485500714377853277739)
        ·
          refine ⟨71684228251071566779916609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47789485500714377853277739 71684228251071566779916609)
          ·
            refine ⟨53763171188303675084937457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71684228251071566779916609 53763171188303675084937457)
            ·
              refine ⟨40322378391227756313703093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53763171188303675084937457 40322378391227756313703093)
              ·
                refine ⟨3780222974177602154409665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40322378391227756313703093 3780222974177602154409665)
                ·
                  refine ⟨2835167230633201615807249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3780222974177602154409665 2835167230633201615807249)
                  ·
                    refine ⟨2126375422974901211855437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2835167230633201615807249 2126375422974901211855437)
                    ·
                      refine ⟨797390783615587954445789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2126375422974901211855437 797390783615587954445789)
                      ·
                        rfl

theorem cell23_1552913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_1552913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552913 prefixEnd_1552913 := by exact prefixLift 1552913
  have htrace : WordTrace (prefixWord ++ tailWord_1552913) baseStart_1552913 baseEnd_1552913 := by
    simpa [prefixWord, tailWord_1552913, baseEnd_1552913] using wordTrace_append hprefix tailTrace_1552913
  have hstable : (prefixWord ++ tailWord_1552913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552913).length < 2 ^ (prefixWord ++ tailWord_1552913).sum := by decide
  have hdescent : baseEnd_1552913 < baseStart_1552913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552933 : List Nat := [1, 3, 1, 2, 2, 1, 5, 2, 6]
def baseStart_1552933 : Nat := 118140960795 + 1552933 * 2 ^ 59
def prefixEnd_1552933 : Nat := 4983230072969 + 3 ^ 40 * 1552933 * 2
def baseEnd_1552933 : Nat := 88600117025408652910633

theorem tailTrace_1552933 : CollatzResearch.WordTrace tailWord_1552933 prefixEnd_1552933 88600117025408652910633 := by
  unfold tailWord_1552933
  simp only [CollatzResearch.WordTrace]
  refine ⟨56640119682996435686279453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37760079788664290457519635 56640119682996435686279453)
  ·
    refine ⟨21240044881123663382354795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56640119682996435686279453 21240044881123663382354795)
    ·
      refine ⟨31860067321685495073532193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21240044881123663382354795 31860067321685495073532193)
      ·
        refine ⟨23895050491264121305149145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31860067321685495073532193 23895050491264121305149145)
        ·
          refine ⟨17921287868448090978861859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23895050491264121305149145 17921287868448090978861859)
          ·
            refine ⟨26881931802672136468292789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17921287868448090978861859 26881931802672136468292789)
            ·
              refine ⟨2520181106500512793902449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26881931802672136468292789 2520181106500512793902449)
              ·
                refine ⟨1890135829875384595426837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2520181106500512793902449 1890135829875384595426837)
                ·
                  refine ⟨88600117025408652910633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1890135829875384595426837 88600117025408652910633)
                  ·
                    rfl

theorem cell23_1552933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 6].length) (baseStart_1552933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552933 prefixEnd_1552933 := by exact prefixLift 1552933
  have htrace : WordTrace (prefixWord ++ tailWord_1552933) baseStart_1552933 baseEnd_1552933 := by
    simpa [prefixWord, tailWord_1552933, baseEnd_1552933] using wordTrace_append hprefix tailTrace_1552933
  have hstable : (prefixWord ++ tailWord_1552933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552933).length < 2 ^ (prefixWord ++ tailWord_1552933).sum := by decide
  have hdescent : baseEnd_1552933 < baseStart_1552933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552960 : List Nat := [2, 1, 1, 2, 2, 2, 4, 2, 3, 1, 3]
def baseStart_1552960 : Nat := 118140960795 + 1552960 * 2 ^ 59
def prefixEnd_1552960 : Nat := 4983230072969 + 3 ^ 40 * 1552960 * 2
def baseEnd_1552960 : Nat := 797414917206349270558073

theorem tailTrace_1552960 : CollatzResearch.WordTrace tailWord_1552960 prefixEnd_1552960 797414917206349270558073 := by
  unfold tailWord_1552960
  simp only [CollatzResearch.WordTrace]
  refine ⟨28320552226949309648756167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37760736302599079531674889 28320552226949309648756167)
  ·
    refine ⟨42480828340423964473134251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28320552226949309648756167 42480828340423964473134251)
    ·
      refine ⟨63721242510635946709701377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42480828340423964473134251 63721242510635946709701377)
      ·
        refine ⟨47790931882976960032276033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63721242510635946709701377 47790931882976960032276033)
        ·
          refine ⟨35843198912232720024207025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47790931882976960032276033 35843198912232720024207025)
          ·
            refine ⟨26882399184174540018155269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35843198912232720024207025 26882399184174540018155269)
            ·
              refine ⟨5040449847032726253404113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26882399184174540018155269 5040449847032726253404113)
              ·
                refine ⟨3780337385274544690053085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5040449847032726253404113 3780337385274544690053085)
                ·
                  refine ⟨1417626519477954258769907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3780337385274544690053085 1417626519477954258769907)
                  ·
                    refine ⟨2126439779216931388154861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1417626519477954258769907 2126439779216931388154861)
                    ·
                      refine ⟨797414917206349270558073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2126439779216931388154861 797414917206349270558073)
                      ·
                        rfl

theorem cell23_1552960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 3, 1, 3].length) (baseStart_1552960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552960 prefixEnd_1552960 := by exact prefixLift 1552960
  have htrace : WordTrace (prefixWord ++ tailWord_1552960) baseStart_1552960 baseEnd_1552960 := by
    simpa [prefixWord, tailWord_1552960, baseEnd_1552960] using wordTrace_append hprefix tailTrace_1552960
  have hstable : (prefixWord ++ tailWord_1552960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552960).length < 2 ^ (prefixWord ++ tailWord_1552960).sum := by decide
  have hdescent : baseEnd_1552960 < baseStart_1552960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552970 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 1, 5, 2]
def baseStart_1552970 : Nat := 118140960795 + 1552970 * 2 ^ 59
def prefixEnd_1552970 : Nat := 4983230072969 + 3 ^ 40 * 1552970 * 2
def baseEnd_1552970 : Nat := 797420052012894231433027

theorem tailTrace_1552970 : CollatzResearch.WordTrace tailWord_1552970 prefixEnd_1552970 797420052012894231433027 := by
  unfold tailWord_1552970
  simp only [CollatzResearch.WordTrace]
  refine ⟨14160367295965597751344091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37760979455908260670250909 14160367295965597751344091)
  ·
    refine ⟨21240550943948396627016137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14160367295965597751344091 21240550943948396627016137)
    ·
      refine ⟨15930413207961297470262103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21240550943948396627016137 15930413207961297470262103)
      ·
        refine ⟨23895619811941946205393155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15930413207961297470262103 23895619811941946205393155)
        ·
          refine ⟨35843429717912919308089733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23895619811941946205393155 35843429717912919308089733)
          ·
            refine ⟨6720643072108672370266825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35843429717912919308089733 6720643072108672370266825)
            ·
              refine ⟨5040482304081504277700119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6720643072108672370266825 5040482304081504277700119)
              ·
                refine ⟨7560723456122256416550179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5040482304081504277700119 7560723456122256416550179)
                ·
                  refine ⟨11341085184183384624825269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7560723456122256416550179 11341085184183384624825269)
                  ·
                    refine ⟨1063226736017192308577369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11341085184183384624825269 1063226736017192308577369)
                    ·
                      refine ⟨797420052012894231433027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1063226736017192308577369 797420052012894231433027)
                      ·
                        rfl

theorem cell23_1552970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_1552970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552970 prefixEnd_1552970 := by exact prefixLift 1552970
  have htrace : WordTrace (prefixWord ++ tailWord_1552970) baseStart_1552970 baseEnd_1552970 := by
    simpa [prefixWord, tailWord_1552970, baseEnd_1552970] using wordTrace_append hprefix tailTrace_1552970
  have hstable : (prefixWord ++ tailWord_1552970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552970).length < 2 ^ (prefixWord ++ tailWord_1552970).sum := by decide
  have hdescent : baseEnd_1552970 < baseStart_1552970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552980 : List Nat := [2, 4, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_1552980 : Nat := 118140960795 + 1552980 * 2 ^ 59
def prefixEnd_1552980 : Nat := 4983230072969 + 3 ^ 40 * 1552980 * 2
def baseEnd_1552980 : Nat := 265808395606479730769327

theorem tailTrace_1552980 : CollatzResearch.WordTrace tailWord_1552980 prefixEnd_1552980 265808395606479730769327 := by
  unfold tailWord_1552980
  simp only [CollatzResearch.WordTrace]
  refine ⟨28320916956913081356620197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37761222609217441808826929 28320916956913081356620197)
  ·
    refine ⟨5310171929421202754366287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28320916956913081356620197 5310171929421202754366287)
    ·
      refine ⟨7965257894131804131549431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5310171929421202754366287 7965257894131804131549431)
      ·
        refine ⟨11947886841197706197324147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7965257894131804131549431 11947886841197706197324147)
        ·
          refine ⟨17921830261796559295986221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11947886841197706197324147 17921830261796559295986221)
          ·
            refine ⟨6720686348173709735994833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17921830261796559295986221 6720686348173709735994833)
            ·
              refine ⟨5040514761130282301996125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6720686348173709735994833 5040514761130282301996125)
              ·
                refine ⟨1890193035423855863248547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5040514761130282301996125 1890193035423855863248547)
                ·
                  refine ⟨2835289553135783794872821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890193035423855863248547 2835289553135783794872821)
                  ·
                    refine ⟨265808395606479730769327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2835289553135783794872821 265808395606479730769327)
                    ·
                      rfl

theorem cell23_1552980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_1552980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1552980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1552980 prefixEnd_1552980 := by exact prefixLift 1552980
  have htrace : WordTrace (prefixWord ++ tailWord_1552980) baseStart_1552980 baseEnd_1552980 := by
    simpa [prefixWord, tailWord_1552980, baseEnd_1552980] using wordTrace_append hprefix tailTrace_1552980
  have hstable : (prefixWord ++ tailWord_1552980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552980).length < 2 ^ (prefixWord ++ tailWord_1552980).sum := by decide
  have hdescent : baseEnd_1552980 < baseStart_1552980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553014 : List Nat := [5, 1, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_1553014 : Nat := 118140960795 + 1553014 * 2 ^ 59
def prefixEnd_1553014 : Nat := 4983230072969 + 3 ^ 40 * 1553014 * 2
def baseEnd_1553014 : Nat := 265814215053897353094275

theorem tailTrace_1553014 : CollatzResearch.WordTrace tailWord_1553014 prefixEnd_1553014 265814215053897353094275 := by
  unfold tailWord_1553014
  simp only [CollatzResearch.WordTrace]
  refine ⟨3540192124731436657498631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37762049330468657679985397 3540192124731436657498631)
  ·
    refine ⟨5310288187097154986247947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3540192124731436657498631 5310288187097154986247947)
    ·
      refine ⟨7965432280645732479371921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5310288187097154986247947 7965432280645732479371921)
      ·
        refine ⟨5974074210484299359528941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7965432280645732479371921 5974074210484299359528941)
        ·
          refine ⟨2240277828931612259823353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5974074210484299359528941 2240277828931612259823353)
          ·
            refine ⟨1680208371698709194867515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2240277828931612259823353 1680208371698709194867515)
            ·
              refine ⟨2520312557548063792301273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1680208371698709194867515 2520312557548063792301273)
              ·
                refine ⟨1890234418161047844225955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2520312557548063792301273 1890234418161047844225955)
                ·
                  refine ⟨2835351627241571766338933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890234418161047844225955 2835351627241571766338933)
                  ·
                    refine ⟨265814215053897353094275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2835351627241571766338933 265814215053897353094275)
                    ·
                      rfl

theorem cell23_1553014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_1553014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553014 prefixEnd_1553014 := by exact prefixLift 1553014
  have htrace : WordTrace (prefixWord ++ tailWord_1553014) baseStart_1553014 baseEnd_1553014 := by
    simpa [prefixWord, tailWord_1553014, baseEnd_1553014] using wordTrace_append hprefix tailTrace_1553014
  have hstable : (prefixWord ++ tailWord_1553014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553014).length < 2 ^ (prefixWord ++ tailWord_1553014).sum := by decide
  have hdescent : baseEnd_1553014 < baseStart_1553014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553017 : List Nat := [1, 2, 1, 3, 3, 4, 1, 2, 1, 1, 4]
def baseStart_1553017 : Nat := 118140960795 + 1553017 * 2 ^ 59
def prefixEnd_1553017 : Nat := 4983230072969 + 3 ^ 40 * 1553017 * 2
def baseEnd_1553017 : Nat := 797444185603655547545311

theorem tailTrace_1553017 : CollatzResearch.WordTrace tailWord_1553017 prefixEnd_1553017 797444185603655547545311 := by
  unfold tailWord_1553017
  simp only [CollatzResearch.WordTrace]
  refine ⟨56643183414692118032337305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37762122276461412021558203 56643183414692118032337305)
  ·
    refine ⟨42482387561019088524252979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56643183414692118032337305 42482387561019088524252979)
    ·
      refine ⟨63723581341528632786379469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42482387561019088524252979 63723581341528632786379469)
      ·
        refine ⟨23896343003073237294892301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63723581341528632786379469 23896343003073237294892301)
        ·
          refine ⟨8961128626152463985584613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23896343003073237294892301 8961128626152463985584613)
          ·
            refine ⟨1680211617403586997297115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8961128626152463985584613 1680211617403586997297115)
            ·
              refine ⟨2520317426105380495945673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1680211617403586997297115 2520317426105380495945673)
              ·
                refine ⟨1890238069579035371959255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2520317426105380495945673 1890238069579035371959255)
                ·
                  refine ⟨2835357104368553057938883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890238069579035371959255 2835357104368553057938883)
                  ·
                    refine ⟨4253035656552829586908325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2835357104368553057938883 4253035656552829586908325)
                    ·
                      refine ⟨797444185603655547545311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4253035656552829586908325 797444185603655547545311)
                      ·
                        rfl

theorem cell23_1553017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_1553017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553017 prefixEnd_1553017 := by exact prefixLift 1553017
  have htrace : WordTrace (prefixWord ++ tailWord_1553017) baseStart_1553017 baseEnd_1553017 := by
    simpa [prefixWord, tailWord_1553017, baseEnd_1553017] using wordTrace_append hprefix tailTrace_1553017
  have hstable : (prefixWord ++ tailWord_1553017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553017).length < 2 ^ (prefixWord ++ tailWord_1553017).sum := by decide
  have hdescent : baseEnd_1553017 < baseStart_1553017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553034 : List Nat := [3, 1, 2, 3, 3, 1, 3, 1, 1, 1, 4]
def baseStart_1553034 : Nat := 118140960795 + 1553034 * 2 ^ 59
def prefixEnd_1553034 : Nat := 4983230072969 + 3 ^ 40 * 1553034 * 2
def baseEnd_1553034 : Nat := 797452914774781981032733

theorem tailTrace_1553034 : CollatzResearch.WordTrace tailWord_1553034 prefixEnd_1553034 797452914774781981032733 := by
  unfold tailWord_1553034
  simp only [CollatzResearch.WordTrace]
  refine ⟨14160950863907632483926539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37762535637087019957137437 14160950863907632483926539)
  ·
    refine ⟨21241426295861448725889809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14160950863907632483926539 21241426295861448725889809)
    ·
      refine ⟨15931069721896086544417357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21241426295861448725889809 15931069721896086544417357)
      ·
        refine ⟨5974151145711032454156509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15931069721896086544417357 5974151145711032454156509)
        ·
          refine ⟨2240306679641637170308691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5974151145711032454156509 2240306679641637170308691)
          ·
            refine ⟨3360460019462455755463037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240306679641637170308691 3360460019462455755463037)
            ·
              refine ⟨1260172507298420908298639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3360460019462455755463037 1260172507298420908298639)
              ·
                refine ⟨1890258760947631362447959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1260172507298420908298639 1890258760947631362447959)
                ·
                  refine ⟨2835388141421447043671939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890258760947631362447959 2835388141421447043671939)
                  ·
                    refine ⟨4253082212132170565507909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2835388141421447043671939 4253082212132170565507909)
                    ·
                      refine ⟨797452914774781981032733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4253082212132170565507909 797452914774781981032733)
                      ·
                        rfl

theorem cell23_1553034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_1553034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553034 prefixEnd_1553034 := by exact prefixLift 1553034
  have htrace : WordTrace (prefixWord ++ tailWord_1553034) baseStart_1553034 baseEnd_1553034 := by
    simpa [prefixWord, tailWord_1553034, baseEnd_1553034] using wordTrace_append hprefix tailTrace_1553034
  have hstable : (prefixWord ++ tailWord_1553034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553034).length < 2 ^ (prefixWord ++ tailWord_1553034).sum := by decide
  have hdescent : baseEnd_1553034 < baseStart_1553034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553044 : List Nat := [2, 4, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_1553044 : Nat := 118140960795 + 1553044 * 2 ^ 59
def prefixEnd_1553044 : Nat := 4983230072969 + 3 ^ 40 * 1553044 * 2
def baseEnd_1553044 : Nat := 265819349860442313969229

theorem tailTrace_1553044 : CollatzResearch.WordTrace tailWord_1553044 prefixEnd_1553044 265819349860442313969229 := by
  unfold tailWord_1553044
  simp only [CollatzResearch.WordTrace]
  refine ⟨28322084092797150821785093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37762778790396201095713457 28322084092797150821785093)
  ·
    refine ⟨5310390767399465779084705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28322084092797150821785093 5310390767399465779084705)
    ·
      refine ⟨3982793075549599334313529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5310390767399465779084705 3982793075549599334313529)
      ·
        refine ⟨2987094806662199500735147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3982793075549599334313529 2987094806662199500735147)
        ·
          refine ⟨4480642209993299251102721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2987094806662199500735147 4480642209993299251102721)
          ·
            refine ⟨3360481657494974438327041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4480642209993299251102721 3360481657494974438327041)
            ·
              refine ⟨2520361243121230828745281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3360481657494974438327041 2520361243121230828745281)
              ·
                refine ⟨1890270932340923121558961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2520361243121230828745281 1890270932340923121558961)
                ·
                  refine ⟨1417703199255692341169221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1890270932340923121558961 1417703199255692341169221)
                  ·
                    refine ⟨265819349860442313969229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1417703199255692341169221 265819349860442313969229)
                    ·
                      rfl

theorem cell23_1553044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_1553044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553044 prefixEnd_1553044 := by exact prefixLift 1553044
  have htrace : WordTrace (prefixWord ++ tailWord_1553044) baseStart_1553044 baseEnd_1553044 := by
    simpa [prefixWord, tailWord_1553044, baseEnd_1553044] using wordTrace_append hprefix tailTrace_1553044
  have hstable : (prefixWord ++ tailWord_1553044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553044).length < 2 ^ (prefixWord ++ tailWord_1553044).sum := by decide
  have hdescent : baseEnd_1553044 < baseStart_1553044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553053 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 2, 7]
def baseStart_1553053 : Nat := 118140960795 + 1553053 * 2 ^ 59
def prefixEnd_1553053 : Nat := 4983230072969 + 3 ^ 40 * 1553053 * 2
def baseEnd_1553053 : Nat := 265820890302405802231715

theorem tailTrace_1553053 : CollatzResearch.WordTrace tailWord_1553053 prefixEnd_1553053 265820890302405802231715 := by
  unfold tailWord_1553053
  simp only [CollatzResearch.WordTrace]
  refine ⟨56644496442561696180647813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37762997628374464120431875 56644496442561696180647813)
  ·
    refine ⟨10620843082980318033871465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56644496442561696180647813 10620843082980318033871465)
    ·
      refine ⟨7965632312235238525403599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10620843082980318033871465 7965632312235238525403599)
      ·
        refine ⟨11948448468352857788105399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7965632312235238525403599 11948448468352857788105399)
        ·
          refine ⟨17922672702529286682158099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11948448468352857788105399 17922672702529286682158099)
          ·
            refine ⟨26884009053793930023237149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17922672702529286682158099 26884009053793930023237149)
            ·
              refine ⟨10081503395172723758713931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26884009053793930023237149 10081503395172723758713931)
              ·
                refine ⟨15122255092759085638070897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10081503395172723758713931 15122255092759085638070897)
                ·
                  refine ⟨11341691319569314228553173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15122255092759085638070897 11341691319569314228553173)
                  ·
                    refine ⟨265820890302405802231715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11341691319569314228553173 265820890302405802231715)
                    ·
                      rfl

theorem cell23_1553053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_1553053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553053 prefixEnd_1553053 := by exact prefixLift 1553053
  have htrace : WordTrace (prefixWord ++ tailWord_1553053) baseStart_1553053 baseEnd_1553053 := by
    simpa [prefixWord, tailWord_1553053, baseEnd_1553053] using wordTrace_append hprefix tailTrace_1553053
  have hstable : (prefixWord ++ tailWord_1553053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553053).length < 2 ^ (prefixWord ++ tailWord_1553053).sum := by decide
  have hdescent : baseEnd_1553053 < baseStart_1553053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553057 : List Nat := [1, 2, 3, 3, 4, 1, 1, 8]
def baseStart_1553057 : Nat := 118140960795 + 1553057 * 2 ^ 59
def prefixEnd_1553057 : Nat := 4983230072969 + 3 ^ 40 * 1553057 * 2
def baseEnd_1553057 : Nat := 29535730549253162631301

theorem tailTrace_1553057 : CollatzResearch.WordTrace tailWord_1553057 prefixEnd_1553057 29535730549253162631301 := by
  unfold tailWord_1553057
  simp only [CollatzResearch.WordTrace]
  refine ⟨56644642334547204863793425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37763094889698136575862283 56644642334547204863793425)
  ·
    refine ⟨42483481750910403647845069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56644642334547204863793425 42483481750910403647845069)
    ·
      refine ⟨15931305656591401367941901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42483481750910403647845069 15931305656591401367941901)
      ·
        refine ⟨5974239621221775512978213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15931305656591401367941901 5974239621221775512978213)
        ·
          refine ⟨1120169928979082908683415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5974239621221775512978213 1120169928979082908683415)
          ·
            refine ⟨1680254893468624363025123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1120169928979082908683415 1680254893468624363025123)
            ·
              refine ⟨2520382340202936544537685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1680254893468624363025123 2520382340202936544537685)
              ·
                refine ⟨29535730549253162631301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2520382340202936544537685 29535730549253162631301)
                ·
                  rfl

theorem cell23_1553057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 8].length) (baseStart_1553057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553057 prefixEnd_1553057 := by exact prefixLift 1553057
  have htrace : WordTrace (prefixWord ++ tailWord_1553057) baseStart_1553057 baseEnd_1553057 := by
    simpa [prefixWord, tailWord_1553057, baseEnd_1553057] using wordTrace_append hprefix tailTrace_1553057
  have hstable : (prefixWord ++ tailWord_1553057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553057).length < 2 ^ (prefixWord ++ tailWord_1553057).sum := by decide
  have hdescent : baseEnd_1553057 < baseStart_1553057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553100 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 2, 6]
def baseStart_1553100 : Nat := 118140960795 + 1553100 * 2 ^ 59
def prefixEnd_1553100 : Nat := 4983230072969 + 3 ^ 40 * 1553100 * 2
def baseEnd_1553100 : Nat := 265828934832659574269143

theorem tailTrace_1553100 : CollatzResearch.WordTrace tailWord_1553100 prefixEnd_1553100 265828934832659574269143 := by
  unfold tailWord_1553100
  simp only [CollatzResearch.WordTrace]
  refine ⟨28323105336695711603804377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37764140448927615471739169 28323105336695711603804377)
  ·
    refine ⟨21242329002521783702853283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28323105336695711603804377 21242329002521783702853283)
    ·
      refine ⟨31863493503782675554279925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21242329002521783702853283 31863493503782675554279925)
      ·
        refine ⟨2987202515979625833213743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31863493503782675554279925 2987202515979625833213743)
        ·
          refine ⟨4480803773969438749820615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2987202515979625833213743 4480803773969438749820615)
          ·
            refine ⟨6721205660954158124730923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4480803773969438749820615 6721205660954158124730923)
            ·
              refine ⟨10081808491431237187096385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6721205660954158124730923 10081808491431237187096385)
              ·
                refine ⟨7561356368573427890322289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10081808491431237187096385 7561356368573427890322289)
                ·
                  refine ⟨5671017276430070917741717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7561356368573427890322289 5671017276430070917741717)
                  ·
                    refine ⟨265828934832659574269143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5671017276430070917741717 265828934832659574269143)
                    ·
                      rfl

theorem cell23_1553100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_1553100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553100 prefixEnd_1553100 := by exact prefixLift 1553100
  have htrace : WordTrace (prefixWord ++ tailWord_1553100) baseStart_1553100 baseEnd_1553100 := by
    simpa [prefixWord, tailWord_1553100, baseEnd_1553100] using wordTrace_append hprefix tailTrace_1553100
  have hstable : (prefixWord ++ tailWord_1553100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553100).length < 2 ^ (prefixWord ++ tailWord_1553100).sum := by decide
  have hdescent : baseEnd_1553100 < baseStart_1553100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553101 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_1553101 : Nat := 118140960795 + 1553101 * 2 ^ 59
def prefixEnd_1553101 : Nat := 4983230072969 + 3 ^ 40 * 1553101 * 2
def baseEnd_1553101 : Nat := 797487317978633218894925

theorem tailTrace_1553101 : CollatzResearch.WordTrace tailWord_1553101 prefixEnd_1553101 797487317978633218894925 := by
  unfold tailWord_1553101
  simp only [CollatzResearch.WordTrace]
  refine ⟨56646247146387800378395157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37764164764258533585596771 56646247146387800378395157)
  ·
    refine ⟨2655292834986928142737273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56646247146387800378395157 2655292834986928142737273)
    ·
      refine ⟨1991469626240196107052955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2655292834986928142737273 1991469626240196107052955)
      ·
        refine ⟨2987204439360294160579433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1991469626240196107052955 2987204439360294160579433)
        ·
          refine ⟨2240403329520220620434575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2987204439360294160579433 2240403329520220620434575)
          ·
            refine ⟨3360604994280330930651863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240403329520220620434575 3360604994280330930651863)
            ·
              refine ⟨5040907491420496395977795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3360604994280330930651863 5040907491420496395977795)
              ·
                refine ⟨7561361237130744593966693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5040907491420496395977795 7561361237130744593966693)
                ·
                  refine ⟨1417755231962014611368755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7561361237130744593966693 1417755231962014611368755)
                  ·
                    refine ⟨2126632847943021917053133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1417755231962014611368755 2126632847943021917053133)
                    ·
                      refine ⟨797487317978633218894925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2126632847943021917053133 797487317978633218894925)
                      ·
                        rfl

theorem cell23_1553101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_1553101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553101 prefixEnd_1553101 := by exact prefixLift 1553101
  have htrace : WordTrace (prefixWord ++ tailWord_1553101) baseStart_1553101 baseEnd_1553101 := by
    simpa [prefixWord, tailWord_1553101, baseEnd_1553101] using wordTrace_append hprefix tailTrace_1553101
  have hstable : (prefixWord ++ tailWord_1553101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553101).length < 2 ^ (prefixWord ++ tailWord_1553101).sum := by decide
  have hdescent : baseEnd_1553101 < baseStart_1553101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553124 : List Nat := [2, 3, 1, 1, 1, 6, 1, 1, 1, 4, 2]
def baseStart_1553124 : Nat := 118140960795 + 1553124 * 2 ^ 59
def prefixEnd_1553124 : Nat := 4983230072969 + 3 ^ 40 * 1553124 * 2
def baseEnd_1553124 : Nat := 797499128033686628907319

theorem tailTrace_1553124 : CollatzResearch.WordTrace tailWord_1553124 prefixEnd_1553124 797499128033686628907319 := by
  unfold tailWord_1553124
  simp only [CollatzResearch.WordTrace]
  refine ⟨28323543012652237653241213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37764724016869650204321617 28323543012652237653241213)
  ·
    refine ⟨10621328629744589119965455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28323543012652237653241213 10621328629744589119965455)
    ·
      refine ⟨15931992944616883679948183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10621328629744589119965455 15931992944616883679948183)
      ·
        refine ⟨23897989416925325519922275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15931992944616883679948183 23897989416925325519922275)
        ·
          refine ⟨35846984125387988279883413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23897989416925325519922275 35846984125387988279883413)
          ·
            refine ⟨1680327380877561950619535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35846984125387988279883413 1680327380877561950619535)
            ·
              refine ⟨2520491071316342925929303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1680327380877561950619535 2520491071316342925929303)
              ·
                refine ⟨3780736606974514388893955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2520491071316342925929303 3780736606974514388893955)
                ·
                  refine ⟨5671104910461771583340933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3780736606974514388893955 5671104910461771583340933)
                  ·
                    refine ⟨1063332170711582171876425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5671104910461771583340933 1063332170711582171876425)
                    ·
                      refine ⟨797499128033686628907319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1063332170711582171876425 797499128033686628907319)
                      ·
                        rfl

theorem cell23_1553124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_1553124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553124 prefixEnd_1553124 := by exact prefixLift 1553124
  have htrace : WordTrace (prefixWord ++ tailWord_1553124) baseStart_1553124 baseEnd_1553124 := by
    simpa [prefixWord, tailWord_1553124, baseEnd_1553124] using wordTrace_append hprefix tailTrace_1553124
  have hstable : (prefixWord ++ tailWord_1553124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553124).length < 2 ^ (prefixWord ++ tailWord_1553124).sum := by decide
  have hdescent : baseEnd_1553124 < baseStart_1553124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553160 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 4, 5]
def baseStart_1553160 : Nat := 118140960795 + 1553160 * 2 ^ 59
def prefixEnd_1553160 : Nat := 4983230072969 + 3 ^ 40 * 1553160 * 2
def baseEnd_1553160 : Nat := 265839204445749496019051

theorem tailTrace_1553160 : CollatzResearch.WordTrace tailWord_1553160 prefixEnd_1553160 265839204445749496019051 := by
  unfold tailWord_1553160
  simp only [CollatzResearch.WordTrace]
  refine ⟨28324199526587026727396467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37765599368782702303195289 28324199526587026727396467)
  ·
    refine ⟨42486299289880540091094701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28324199526587026727396467 42486299289880540091094701)
    ·
      refine ⟨15932362233705202534160513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42486299289880540091094701 15932362233705202534160513)
      ·
        refine ⟨11949271675278901900620385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15932362233705202534160513 11949271675278901900620385)
        ·
          refine ⟨8961953756459176425465289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11949271675278901900620385 8961953756459176425465289)
          ·
            refine ⟨6721465317344382319098967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8961953756459176425465289 6721465317344382319098967)
            ·
              refine ⟨10082197976016573478648451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6721465317344382319098967 10082197976016573478648451)
              ·
                refine ⟨15123296964024860217972677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10082197976016573478648451 15123296964024860217972677)
                ·
                  refine ⟨2835618180754661290869877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15123296964024860217972677 2835618180754661290869877)
                  ·
                    refine ⟨265839204445749496019051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2835618180754661290869877 265839204445749496019051)
                    ·
                      rfl

theorem cell23_1553160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_1553160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553160 prefixEnd_1553160 := by exact prefixLift 1553160
  have htrace : WordTrace (prefixWord ++ tailWord_1553160) baseStart_1553160 baseEnd_1553160 := by
    simpa [prefixWord, tailWord_1553160, baseEnd_1553160] using wordTrace_append hprefix tailTrace_1553160
  have hstable : (prefixWord ++ tailWord_1553160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553160).length < 2 ^ (prefixWord ++ tailWord_1553160).sum := by decide
  have hdescent : baseEnd_1553160 < baseStart_1553160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553175 : List Nat := [1, 1, 3, 4, 4, 1, 2, 1, 2, 2, 2]
def baseStart_1553175 : Nat := 118140960795 + 1553175 * 2 ^ 59
def prefixEnd_1553175 : Nat := 4983230072969 + 3 ^ 40 * 1553175 * 2
def baseEnd_1553175 : Nat := 797525315547065929369585

theorem tailTrace_1553175 : CollatzResearch.WordTrace tailWord_1553175 prefixEnd_1553175 797525315547065929369585 := by
  unfold tailWord_1553175
  simp only [CollatzResearch.WordTrace]
  refine ⟨56648946148119711016588979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37765964098746474011059319 56648946148119711016588979)
  ·
    refine ⟨84973419222179566524883469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56648946148119711016588979 84973419222179566524883469)
    ·
      refine ⟨31865032208317337446831301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84973419222179566524883469 31865032208317337446831301)
      ·
        refine ⟨5974693539059500771280869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31865032208317337446831301 5974693539059500771280869)
        ·
          refine ⟨1120255038573656394615163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5974693539059500771280869 1120255038573656394615163)
          ·
            refine ⟨1680382557860484591922745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1120255038573656394615163 1680382557860484591922745)
            ·
              refine ⟨1260286918395363443942059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1680382557860484591922745 1260286918395363443942059)
              ·
                refine ⟨1890430377593045165913089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1260286918395363443942059 1890430377593045165913089)
                ·
                  refine ⟨1417822783194783874434817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1890430377593045165913089 1417822783194783874434817)
                  ·
                    refine ⟨1063367087396087905826113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1417822783194783874434817 1063367087396087905826113)
                    ·
                      refine ⟨797525315547065929369585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1063367087396087905826113 797525315547065929369585)
                      ·
                        rfl

theorem cell23_1553175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_1553175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553175 prefixEnd_1553175 := by exact prefixLift 1553175
  have htrace : WordTrace (prefixWord ++ tailWord_1553175) baseStart_1553175 baseEnd_1553175 := by
    simpa [prefixWord, tailWord_1553175, baseEnd_1553175] using wordTrace_append hprefix tailTrace_1553175
  have hstable : (prefixWord ++ tailWord_1553175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553175).length < 2 ^ (prefixWord ++ tailWord_1553175).sum := by decide
  have hdescent : baseEnd_1553175 < baseStart_1553175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553200 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 3]
def baseStart_1553200 : Nat := 118140960795 + 1553200 * 2 ^ 59
def prefixEnd_1553200 : Nat := 4983230072969 + 3 ^ 40 * 1553200 * 2
def baseEnd_1553200 : Nat := 797538152563428331556969

theorem tailTrace_1553200 : CollatzResearch.WordTrace tailWord_1553200 prefixEnd_1553200 797538152563428331556969 := by
  unfold tailWord_1553200
  simp only [CollatzResearch.WordTrace]
  refine ⟨28324928986514570143124527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37766571982019426857499369 28324928986514570143124527)
  ·
    refine ⟨42487393479771855214686791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28324928986514570143124527 42487393479771855214686791)
    ·
      refine ⟨63731090219657782822030187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42487393479771855214686791 63731090219657782822030187)
      ·
        refine ⟨95596635329486674233045281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63731090219657782822030187 95596635329486674233045281)
        ·
          refine ⟨71697476497115005674783961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95596635329486674233045281 71697476497115005674783961)
          ·
            refine ⟨53773107372836254256087971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71697476497115005674783961 53773107372836254256087971)
            ·
              refine ⟨80659661059254381384131957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53773107372836254256087971 80659661059254381384131957)
              ·
                refine ⟨7561843224305098254762371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80659661059254381384131957 7561843224305098254762371)
                ·
                  refine ⟨11342764836457647382143557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7561843224305098254762371 11342764836457647382143557)
                  ·
                    refine ⟨2126768406835808884151917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11342764836457647382143557 2126768406835808884151917)
                    ·
                      refine ⟨797538152563428331556969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2126768406835808884151917 797538152563428331556969)
                      ·
                        rfl

theorem cell23_1553200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 3].length) (baseStart_1553200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553200 prefixEnd_1553200 := by exact prefixLift 1553200
  have htrace : WordTrace (prefixWord ++ tailWord_1553200) baseStart_1553200 baseEnd_1553200 := by
    simpa [prefixWord, tailWord_1553200, baseEnd_1553200] using wordTrace_append hprefix tailTrace_1553200
  have hstable : (prefixWord ++ tailWord_1553200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553200).length < 2 ^ (prefixWord ++ tailWord_1553200).sum := by decide
  have hdescent : baseEnd_1553200 < baseStart_1553200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553224 : List Nat := [2, 1, 3, 1, 1, 3, 3, 4, 1, 4]
def baseStart_1553224 : Nat := 118140960795 + 1553224 * 2 ^ 59
def prefixEnd_1553224 : Nat := 4983230072969 + 3 ^ 40 * 1553224 * 2
def baseEnd_1553224 : Nat := 265850158699712079218953

theorem tailTrace_1553224 : CollatzResearch.WordTrace tailWord_1553224 prefixEnd_1553224 265850158699712079218953 := by
  unfold tailWord_1553224
  simp only [CollatzResearch.WordTrace]
  refine ⟨28325366662471096192561363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37767155549961461590081817 28325366662471096192561363)
  ·
    refine ⟨42488049993706644288842045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28325366662471096192561363 42488049993706644288842045)
    ·
      refine ⟨15933018747639991608315767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42488049993706644288842045 15933018747639991608315767)
      ·
        refine ⟨23899528121459987412473651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15933018747639991608315767 23899528121459987412473651)
        ·
          refine ⟨35849292182189981118710477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23899528121459987412473651 35849292182189981118710477)
          ·
            refine ⟨13443484568321242919516429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35849292182189981118710477 13443484568321242919516429)
            ·
              refine ⟨5041306713120466094818661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13443484568321242919516429 5041306713120466094818661)
              ·
                refine ⟨945245008710087392778499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5041306713120466094818661 945245008710087392778499)
                ·
                  refine ⟨1417867513065131089167749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 945245008710087392778499 1417867513065131089167749)
                  ·
                    refine ⟨265850158699712079218953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1417867513065131089167749 265850158699712079218953)
                    ·
                      rfl

theorem cell23_1553224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_1553224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553224 prefixEnd_1553224 := by exact prefixLift 1553224
  have htrace : WordTrace (prefixWord ++ tailWord_1553224) baseStart_1553224 baseEnd_1553224 := by
    simpa [prefixWord, tailWord_1553224, baseEnd_1553224] using wordTrace_append hprefix tailTrace_1553224
  have hstable : (prefixWord ++ tailWord_1553224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553224).length < 2 ^ (prefixWord ++ tailWord_1553224).sum := by decide
  have hdescent : baseEnd_1553224 < baseStart_1553224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553314 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_1553314 : Nat := 118140960795 + 1553314 * 2 ^ 59
def prefixEnd_1553314 : Nat := 4983230072969 + 3 ^ 40 * 1553314 * 2
def baseEnd_1553314 : Nat := 265865563119346961843815

theorem tailTrace_1553314 : CollatzResearch.WordTrace tailWord_1553314 prefixEnd_1553314 265865563119346961843815 := by
  unfold tailWord_1553314
  simp only [CollatzResearch.WordTrace]
  refine ⟨14163503973654034438974749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37769343929744091837265997 14163503973654034438974749)
  ·
    refine ⟨5311313990120262914615531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14163503973654034438974749 5311313990120262914615531)
    ·
      refine ⟨7966970985180394371923297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5311313990120262914615531 7966970985180394371923297)
      ·
        refine ⟨5975228238885295778942473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7966970985180394371923297 5975228238885295778942473)
        ·
          refine ⟨4481421179163971834206855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5975228238885295778942473 4481421179163971834206855)
          ·
            refine ⟨6722131768745957751310283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4481421179163971834206855 6722131768745957751310283)
            ·
              refine ⟨10083197653118936626965425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6722131768745957751310283 10083197653118936626965425)
              ·
                refine ⟨7562398239839202470224069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10083197653118936626965425 7562398239839202470224069)
                ·
                  refine ⟨1417949669969850463167013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7562398239839202470224069 1417949669969850463167013)
                  ·
                    refine ⟨265865563119346961843815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1417949669969850463167013 265865563119346961843815)
                    ·
                      rfl

theorem cell23_1553314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_1553314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553314 prefixEnd_1553314 := by exact prefixLift 1553314
  have htrace : WordTrace (prefixWord ++ tailWord_1553314) baseStart_1553314 baseEnd_1553314 := by
    simpa [prefixWord, tailWord_1553314, baseEnd_1553314] using wordTrace_append hprefix tailTrace_1553314
  have hstable : (prefixWord ++ tailWord_1553314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553314).length < 2 ^ (prefixWord ++ tailWord_1553314).sum := by decide
  have hdescent : baseEnd_1553314 < baseStart_1553314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553332 : List Nat := [2, 5, 2, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_1553332 : Nat := 118140960795 + 1553332 * 2 ^ 59
def prefixEnd_1553332 : Nat := 4983230072969 + 3 ^ 40 * 1553332 * 2
def baseEnd_1553332 : Nat := 797605932009821815106363

theorem tailTrace_1553332 : CollatzResearch.WordTrace tailWord_1553332 prefixEnd_1553332 797605932009821815106363 := by
  unfold tailWord_1553332
  simp only [CollatzResearch.WordTrace]
  refine ⟨28327336204275463415027125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37769781605700617886702833 28327336204275463415027125)
  ·
    refine ⟨2655687769150824695158793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28327336204275463415027125 2655687769150824695158793)
    ·
      refine ⟨1991765826863118521369095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2655687769150824695158793 1991765826863118521369095)
      ·
        refine ⟨2987648740294677782053643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1991765826863118521369095 2987648740294677782053643)
        ·
          refine ⟨4481473110442016673080465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2987648740294677782053643 4481473110442016673080465)
          ·
            refine ⟨3361104832831512504810349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4481473110442016673080465 3361104832831512504810349)
            ·
              refine ⟨1260414312311817189303881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3361104832831512504810349 1260414312311817189303881)
              ·
                refine ⟨945310734233862891977911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1260414312311817189303881 945310734233862891977911)
                ·
                  refine ⟨1417966101350794337966867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 945310734233862891977911 1417966101350794337966867)
                  ·
                    refine ⟨2126949152026191506950301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1417966101350794337966867 2126949152026191506950301)
                    ·
                      refine ⟨797605932009821815106363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2126949152026191506950301 797605932009821815106363)
                      ·
                        rfl

theorem cell23_1553332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_1553332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553332 prefixEnd_1553332 := by exact prefixLift 1553332
  have htrace : WordTrace (prefixWord ++ tailWord_1553332) baseStart_1553332 baseEnd_1553332 := by
    simpa [prefixWord, tailWord_1553332, baseEnd_1553332] using wordTrace_append hprefix tailTrace_1553332
  have hstable : (prefixWord ++ tailWord_1553332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553332).length < 2 ^ (prefixWord ++ tailWord_1553332).sum := by decide
  have hdescent : baseEnd_1553332 < baseStart_1553332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553348 : List Nat := [2, 3, 3, 3, 1, 1, 1, 3, 2, 4]
def baseStart_1553348 : Nat := 118140960795 + 1553348 * 2 ^ 59
def prefixEnd_1553348 : Nat := 4983230072969 + 3 ^ 40 * 1553348 * 2
def baseEnd_1553348 : Nat := 265871382566764584168763

theorem tailTrace_1553348 : CollatzResearch.WordTrace tailWord_1553348 prefixEnd_1553348 265871382566764584168763 := by
  unfold tailWord_1553348
  simp only [CollatzResearch.WordTrace]
  refine ⟨28327627988246480781318349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37770170650995307708424465 28327627988246480781318349)
  ·
    refine ⟨10622860495592430292994381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28327627988246480781318349 10622860495592430292994381)
    ·
      refine ⟨3983572685847161359872893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10622860495592430292994381 3983572685847161359872893)
      ·
        refine ⟨1493839757192685509952335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3983572685847161359872893 1493839757192685509952335)
        ·
          refine ⟨2240759635789028264928503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1493839757192685509952335 2240759635789028264928503)
          ·
            refine ⟨3361139453683542397392755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240759635789028264928503 3361139453683542397392755)
            ·
              refine ⟨5041709180525313596089133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3361139453683542397392755 5041709180525313596089133)
              ·
                refine ⟨1890640942696992598533425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5041709180525313596089133 1890640942696992598533425)
                ·
                  refine ⟨1417980707022744448900069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1890640942696992598533425 1417980707022744448900069)
                  ·
                    refine ⟨265871382566764584168763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1417980707022744448900069 265871382566764584168763)
                    ·
                      rfl

theorem cell23_1553348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_1553348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553348 prefixEnd_1553348 := by exact prefixLift 1553348
  have htrace : WordTrace (prefixWord ++ tailWord_1553348) baseStart_1553348 baseEnd_1553348 := by
    simpa [prefixWord, tailWord_1553348, baseEnd_1553348] using wordTrace_append hprefix tailTrace_1553348
  have hstable : (prefixWord ++ tailWord_1553348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553348).length < 2 ^ (prefixWord ++ tailWord_1553348).sum := by decide
  have hdescent : baseEnd_1553348 < baseStart_1553348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553360 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 8]
def baseStart_1553360 : Nat := 118140960795 + 1553360 * 2 ^ 59
def prefixEnd_1553360 : Nat := 4983230072969 + 3 ^ 40 * 1553360 * 2
def baseEnd_1553360 : Nat := 797620309468147705556233

theorem tailTrace_1553360 : CollatzResearch.WordTrace tailWord_1553360 prefixEnd_1553360 797620309468147705556233 := by
  unfold tailWord_1553360
  simp only [CollatzResearch.WordTrace]
  refine ⟨28327846826224743806036767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37770462434966325074715689 28327846826224743806036767)
  ·
    refine ⟨42491770239337115709055151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28327846826224743806036767 42491770239337115709055151)
    ·
      refine ⟨63737655359005673563582727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42491770239337115709055151 63737655359005673563582727)
      ·
        refine ⟨95606483038508510345374091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63737655359005673563582727 95606483038508510345374091)
        ·
          refine ⟨143409724557762765518061137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95606483038508510345374091 143409724557762765518061137)
          ·
            refine ⟨107557293418322074138545853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143409724557762765518061137 107557293418322074138545853)
            ·
              refine ⟨40333985031870777801954695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107557293418322074138545853 40333985031870777801954695)
              ·
                refine ⟨60500977547806166702932043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40333985031870777801954695 60500977547806166702932043)
                ·
                  refine ⟨90751466321709250054398065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60500977547806166702932043 90751466321709250054398065)
                  ·
                    refine ⟨68063599741281937540798549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90751466321709250054398065 68063599741281937540798549)
                    ·
                      refine ⟨797620309468147705556233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 68063599741281937540798549 797620309468147705556233)
                      ·
                        rfl

theorem cell23_1553360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_1553360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553360 prefixEnd_1553360 := by exact prefixLift 1553360
  have htrace : WordTrace (prefixWord ++ tailWord_1553360) baseStart_1553360 baseEnd_1553360 := by
    simpa [prefixWord, tailWord_1553360, baseEnd_1553360] using wordTrace_append hprefix tailTrace_1553360
  have hstable : (prefixWord ++ tailWord_1553360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553360).length < 2 ^ (prefixWord ++ tailWord_1553360).sum := by decide
  have hdescent : baseEnd_1553360 < baseStart_1553360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553427 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 3]
def baseStart_1553427 : Nat := 118140960795 + 1553427 * 2 ^ 59
def prefixEnd_1553427 : Nat := 4983230072969 + 3 ^ 40 * 1553427 * 2
def baseEnd_1553427 : Nat := 797654712671998943418425

theorem tailTrace_1553427 : CollatzResearch.WordTrace tailWord_1553427 prefixEnd_1553427 797654712671998943418425 := by
  unfold tailWord_1553427
  simp only [CollatzResearch.WordTrace]
  refine ⟨56658137343206758054762535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37772091562137838703175023 56658137343206758054762535)
  ·
    refine ⟨84987206014810137082143803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56658137343206758054762535 84987206014810137082143803)
    ·
      refine ⟨127480809022215205623215705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84987206014810137082143803 127480809022215205623215705)
      ·
        refine ⟨95610606766661404217411779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127480809022215205623215705 95610606766661404217411779)
        ·
          refine ⟨143415910149992106326117669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95610606766661404217411779 143415910149992106326117669)
          ·
            refine ⟨26890483153123519936147063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143415910149992106326117669 26890483153123519936147063)
            ·
              refine ⟨40335724729685279904220595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26890483153123519936147063 40335724729685279904220595)
              ·
                refine ⟨60503587094527919856330893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40335724729685279904220595 60503587094527919856330893)
                ·
                  refine ⟨22688845160447969946124085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60503587094527919856330893 22688845160447969946124085)
                  ·
                    refine ⟨2127079233791997182449133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22688845160447969946124085 2127079233791997182449133)
                    ·
                      refine ⟨797654712671998943418425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2127079233791997182449133 797654712671998943418425)
                      ·
                        rfl

theorem cell23_1553427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 3].length) (baseStart_1553427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553427 prefixEnd_1553427 := by exact prefixLift 1553427
  have htrace : WordTrace (prefixWord ++ tailWord_1553427) baseStart_1553427 baseEnd_1553427 := by
    simpa [prefixWord, tailWord_1553427, baseEnd_1553427] using wordTrace_append hprefix tailTrace_1553427
  have hstable : (prefixWord ++ tailWord_1553427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553427).length < 2 ^ (prefixWord ++ tailWord_1553427).sum := by decide
  have hdescent : baseEnd_1553427 < baseStart_1553427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553457 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 1, 1, 7]
def baseStart_1553457 : Nat := 118140960795 + 1553457 * 2 ^ 59
def prefixEnd_1553457 : Nat := 4983230072969 + 3 ^ 40 * 1553457 * 2
def baseEnd_1553457 : Nat := 797670117091633826043287

theorem tailTrace_1553457 : CollatzResearch.WordTrace tailWord_1553457 prefixEnd_1553457 797670117091633826043287 := by
  unfold tailWord_1553457
  simp only [CollatzResearch.WordTrace]
  refine ⟨56659231533098073178354625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37772821022065382118903083 56659231533098073178354625)
  ·
    refine ⟨42494423649823554883765969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56659231533098073178354625 42494423649823554883765969)
    ·
      refine ⟨31870817737367666162824477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42494423649823554883765969 31870817737367666162824477)
      ·
        refine ⟨11951556651512874811059179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31870817737367666162824477 11951556651512874811059179)
        ·
          refine ⟨17927334977269312216588769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11951556651512874811059179 17927334977269312216588769)
          ·
            refine ⟨13445501232951984162441577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17927334977269312216588769 13445501232951984162441577)
            ·
              refine ⟨10084125924713988121831183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13445501232951984162441577 10084125924713988121831183)
              ·
                refine ⟨15126188887070982182746775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10084125924713988121831183 15126188887070982182746775)
                ·
                  refine ⟨22689283330606473274120163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15126188887070982182746775 22689283330606473274120163)
                  ·
                    refine ⟨34033924995909709911180245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22689283330606473274120163 34033924995909709911180245)
                    ·
                      refine ⟨797670117091633826043287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34033924995909709911180245 797670117091633826043287)
                      ·
                        rfl

theorem cell23_1553457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_1553457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553457 prefixEnd_1553457 := by exact prefixLift 1553457
  have htrace : WordTrace (prefixWord ++ tailWord_1553457) baseStart_1553457 baseEnd_1553457 := by
    simpa [prefixWord, tailWord_1553457, baseEnd_1553457] using wordTrace_append hprefix tailTrace_1553457
  have hstable : (prefixWord ++ tailWord_1553457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553457).length < 2 ^ (prefixWord ++ tailWord_1553457).sum := by decide
  have hdescent : baseEnd_1553457 < baseStart_1553457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553462 : List Nat := [5, 1, 2, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_1553462 : Nat := 118140960795 + 1553462 * 2 ^ 59
def prefixEnd_1553462 : Nat := 4983230072969 + 3 ^ 40 * 1553462 * 2
def baseEnd_1553462 : Nat := 797672684494906306480765

theorem tailTrace_1553462 : CollatzResearch.WordTrace tailWord_1553462 prefixEnd_1553462 797672684494906306480765 := by
  unfold tailWord_1553462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3541213368629997439517915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37772942598719972688191093 3541213368629997439517915)
  ·
    refine ⟨5311820052944996159276873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3541213368629997439517915 5311820052944996159276873)
    ·
      refine ⟨3983865039708747119457655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5311820052944996159276873 3983865039708747119457655)
      ·
        refine ⟨5975797559563120679186483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3983865039708747119457655 5975797559563120679186483)
        ·
          refine ⟨8963696339344681018779725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5975797559563120679186483 8963696339344681018779725)
          ·
            refine ⟨3361386127254255382042397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8963696339344681018779725 3361386127254255382042397)
            ·
              refine ⟨1260519797720345768265899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3361386127254255382042397 1260519797720345768265899)
              ·
                refine ⟨1890779696580518652398849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1260519797720345768265899 1890779696580518652398849)
                ·
                  refine ⟨1418084772435388989299137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1890779696580518652398849 1418084772435388989299137)
                  ·
                    refine ⟨1063563579326541741974353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1418084772435388989299137 1063563579326541741974353)
                    ·
                      refine ⟨797672684494906306480765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1063563579326541741974353 797672684494906306480765)
                      ·
                        rfl

theorem cell23_1553462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_1553462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553462 prefixEnd_1553462 := by exact prefixLift 1553462
  have htrace : WordTrace (prefixWord ++ tailWord_1553462) baseStart_1553462 baseEnd_1553462 := by
    simpa [prefixWord, tailWord_1553462, baseEnd_1553462] using wordTrace_append hprefix tailTrace_1553462
  have hstable : (prefixWord ++ tailWord_1553462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553462).length < 2 ^ (prefixWord ++ tailWord_1553462).sum := by decide
  have hdescent : baseEnd_1553462 < baseStart_1553462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553484 : List Nat := [2, 2, 1, 3, 1, 1, 1, 5, 2, 1, 4]
def baseStart_1553484 : Nat := 118140960795 + 1553484 * 2 ^ 59
def prefixEnd_1553484 : Nat := 4983230072969 + 3 ^ 40 * 1553484 * 2
def baseEnd_1553484 : Nat := 797683981069305220405663

theorem tailTrace_1553484 : CollatzResearch.WordTrace tailWord_1553484 prefixEnd_1553484 797683981069305220405663 := by
  unfold tailWord_1553484
  simp only [CollatzResearch.WordTrace]
  refine ⟨28330108152000128394793753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37773477536000171193058337 28330108152000128394793753)
  ·
    refine ⟨21247581114000096296095315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28330108152000128394793753 21247581114000096296095315)
    ·
      refine ⟨31871371671000144444142973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21247581114000096296095315 31871371671000144444142973)
      ·
        refine ⟨11951764376625054166553615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31871371671000144444142973 11951764376625054166553615)
        ·
          refine ⟨17927646564937581249830423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11951764376625054166553615 17927646564937581249830423)
          ·
            refine ⟨26891469847406371874745635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17927646564937581249830423 26891469847406371874745635)
            ·
              refine ⟨40337204771109557812118453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26891469847406371874745635 40337204771109557812118453)
              ·
                refine ⟨3781612947291521044886105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40337204771109557812118453 3781612947291521044886105)
                ·
                  refine ⟨2836209710468640783664579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3781612947291521044886105 2836209710468640783664579)
                  ·
                    refine ⟨4254314565702961175496869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2836209710468640783664579 4254314565702961175496869)
                    ·
                      refine ⟨797683981069305220405663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4254314565702961175496869 797683981069305220405663)
                      ·
                        rfl

theorem cell23_1553484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_1553484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553484 prefixEnd_1553484 := by exact prefixLift 1553484
  have htrace : WordTrace (prefixWord ++ tailWord_1553484) baseStart_1553484 baseEnd_1553484 := by
    simpa [prefixWord, tailWord_1553484, baseEnd_1553484] using wordTrace_append hprefix tailTrace_1553484
  have hstable : (prefixWord ++ tailWord_1553484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553484).length < 2 ^ (prefixWord ++ tailWord_1553484).sum := by decide
  have hdescent : baseEnd_1553484 < baseStart_1553484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553497 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 2, 1, 6]
def baseStart_1553497 : Nat := 118140960795 + 1553497 * 2 ^ 59
def prefixEnd_1553497 : Nat := 4983230072969 + 3 ^ 40 * 1553497 * 2
def baseEnd_1553497 : Nat := 797690656317813669543103

theorem tailTrace_1553497 : CollatzResearch.WordTrace tailWord_1553497 prefixEnd_1553497 797690656317813669543103 := by
  unfold tailWord_1553497
  simp only [CollatzResearch.WordTrace]
  refine ⟨56660690452953160009810745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37773793635302106673207163 56660690452953160009810745)
  ·
    refine ⟨42495517839714870007358059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56660690452953160009810745 42495517839714870007358059)
    ·
      refine ⟨63743276759572305011037089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42495517839714870007358059 63743276759572305011037089)
      ·
        refine ⟨47807457569679228758277817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63743276759572305011037089 47807457569679228758277817)
        ·
          refine ⟨35855593177259421568708363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47807457569679228758277817 35855593177259421568708363)
          ·
            refine ⟨53783389765889132353062545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35855593177259421568708363 53783389765889132353062545)
            ·
              refine ⟨40337542324416849264796909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53783389765889132353062545 40337542324416849264796909)
              ·
                refine ⟨15126578371656318474298841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40337542324416849264796909 15126578371656318474298841)
                ·
                  refine ⟨11344933778742238855724131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15126578371656318474298841 11344933778742238855724131)
                  ·
                    refine ⟨17017400668113358283586197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11344933778742238855724131 17017400668113358283586197)
                    ·
                      refine ⟨797690656317813669543103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17017400668113358283586197 797690656317813669543103)
                      ·
                        rfl

theorem cell23_1553497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_1553497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553497 prefixEnd_1553497 := by exact prefixLift 1553497
  have htrace : WordTrace (prefixWord ++ tailWord_1553497) baseStart_1553497 baseEnd_1553497 := by
    simpa [prefixWord, tailWord_1553497, baseEnd_1553497] using wordTrace_append hprefix tailTrace_1553497
  have hstable : (prefixWord ++ tailWord_1553497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553497).length < 2 ^ (prefixWord ++ tailWord_1553497).sum := by decide
  have hdescent : baseEnd_1553497 < baseStart_1553497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553502 : List Nat := [4, 4, 1, 1, 1, 2, 3, 2, 5]
def baseStart_1553502 : Nat := 118140960795 + 1553502 * 2 ^ 59
def prefixEnd_1553502 : Nat := 4983230072969 + 3 ^ 40 * 1553502 * 2
def baseEnd_1553502 : Nat := 88632580413454016664509

theorem tailTrace_1553502 : CollatzResearch.WordTrace tailWord_1553502 prefixEnd_1553502 88632580413454016664509 := by
  unfold tailWord_1553502
  simp only [CollatzResearch.WordTrace]
  refine ⟨7082609102241880732967845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37773915211956697242495173 7082609102241880732967845)
  ·
    refine ⟨1327989206670352637431471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7082609102241880732967845 1327989206670352637431471)
    ·
      refine ⟨1991983810005528956147207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1327989206670352637431471 1991983810005528956147207)
      ·
        refine ⟨2987975715008293434220811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1991983810005528956147207 2987975715008293434220811)
        ·
          refine ⟨4481963572512440151331217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2987975715008293434220811 4481963572512440151331217)
          ·
            refine ⟨3361472679384330113498413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4481963572512440151331217 3361472679384330113498413)
            ·
              refine ⟨1260552254769123792561905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3361472679384330113498413 1260552254769123792561905)
              ·
                refine ⟨945414191076842844421429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1260552254769123792561905 945414191076842844421429)
                ·
                  refine ⟨88632580413454016664509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 945414191076842844421429 88632580413454016664509)
                  ·
                    rfl

theorem cell23_1553502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_1553502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553502 prefixEnd_1553502 := by exact prefixLift 1553502
  have htrace : WordTrace (prefixWord ++ tailWord_1553502) baseStart_1553502 baseEnd_1553502 := by
    simpa [prefixWord, tailWord_1553502, baseEnd_1553502] using wordTrace_append hprefix tailTrace_1553502
  have hstable : (prefixWord ++ tailWord_1553502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553502).length < 2 ^ (prefixWord ++ tailWord_1553502).sum := by decide
  have hdescent : baseEnd_1553502 < baseStart_1553502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553511 : List Nat := [1, 1, 5, 1, 1, 3, 3, 1, 3, 4]
def baseStart_1553511 : Nat := 118140960795 + 1553511 * 2 ^ 59
def prefixEnd_1553511 : Nat := 4983230072969 + 3 ^ 40 * 1553511 * 2
def baseEnd_1553511 : Nat := 265899281682325538256013

theorem tailTrace_1553511 : CollatzResearch.WordTrace tailWord_1553511 prefixEnd_1553511 265899281682325538256013 := by
  unfold tailWord_1553511
  simp only [CollatzResearch.WordTrace]
  refine ⟨56661201074902440400820387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37774134049934960267213591 56661201074902440400820387)
  ·
    refine ⟨84991801612353660601230581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56661201074902440400820387 84991801612353660601230581)
    ·
      refine ⟨7967981401158155681365367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84991801612353660601230581 7967981401158155681365367)
      ·
        refine ⟨11951972101737233522048051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7967981401158155681365367 11951972101737233522048051)
        ·
          refine ⟨17927958152605850283072077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11951972101737233522048051 17927958152605850283072077)
          ·
            refine ⟨6722984307227193856152029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17927958152605850283072077 6722984307227193856152029)
            ·
              refine ⟨2521119115210197696057011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6722984307227193856152029 2521119115210197696057011)
              ·
                refine ⟨3781678672815296544085517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2521119115210197696057011 3781678672815296544085517)
                ·
                  refine ⟨1418129502305736204032069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3781678672815296544085517 1418129502305736204032069)
                  ·
                    refine ⟨265899281682325538256013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1418129502305736204032069 265899281682325538256013)
                    ·
                      rfl

theorem cell23_1553511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_1553511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553511 prefixEnd_1553511 := by exact prefixLift 1553511
  have htrace : WordTrace (prefixWord ++ tailWord_1553511) baseStart_1553511 baseEnd_1553511 := by
    simpa [prefixWord, tailWord_1553511, baseEnd_1553511] using wordTrace_append hprefix tailTrace_1553511
  have hstable : (prefixWord ++ tailWord_1553511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553511).length < 2 ^ (prefixWord ++ tailWord_1553511).sum := by decide
  have hdescent : baseEnd_1553511 < baseStart_1553511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553547 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 7]
def baseStart_1553547 : Nat := 118140960795 + 1553547 * 2 ^ 59
def prefixEnd_1553547 : Nat := 4983230072969 + 3 ^ 40 * 1553547 * 2
def baseEnd_1553547 : Nat := 797716330350538473917873

theorem tailTrace_1553547 : CollatzResearch.WordTrace tailWord_1553547 prefixEnd_1553547 797716330350538473917873 := by
  unfold tailWord_1553547
  simp only [CollatzResearch.WordTrace]
  refine ⟨56662514102772018549130895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37775009401848012366087263 56662514102772018549130895)
  ·
    refine ⟨84993771154158027823696343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56662514102772018549130895 84993771154158027823696343)
    ·
      refine ⟨127490656731237041735544515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84993771154158027823696343 127490656731237041735544515)
      ·
        refine ⟨191235985096855562603316773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127490656731237041735544515 191235985096855562603316773)
        ·
          refine ⟨35856747205660417988121895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191235985096855562603316773 35856747205660417988121895)
          ·
            refine ⟨53785120808490626982182843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35856747205660417988121895 53785120808490626982182843)
            ·
              refine ⟨80677681212735940473274265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53785120808490626982182843 80677681212735940473274265)
              ·
                refine ⟨60508260909551955354955699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80677681212735940473274265 60508260909551955354955699)
                ·
                  refine ⟨90762391364327933032433549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60508260909551955354955699 90762391364327933032433549)
                  ·
                    refine ⟨34035896761622974887162581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90762391364327933032433549 34035896761622974887162581)
                    ·
                      refine ⟨797716330350538473917873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34035896761622974887162581 797716330350538473917873)
                      ·
                        rfl

theorem cell23_1553547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 7].length) (baseStart_1553547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553547 prefixEnd_1553547 := by exact prefixLift 1553547
  have htrace : WordTrace (prefixWord ++ tailWord_1553547) baseStart_1553547 baseEnd_1553547 := by
    simpa [prefixWord, tailWord_1553547, baseEnd_1553547] using wordTrace_append hprefix tailTrace_1553547
  have hstable : (prefixWord ++ tailWord_1553547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553547).length < 2 ^ (prefixWord ++ tailWord_1553547).sum := by decide
  have hdescent : baseEnd_1553547 < baseStart_1553547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553562 : List Nat := [3, 1, 1, 5, 1, 3, 2, 2, 1, 4]
def baseStart_1553562 : Nat := 118140960795 + 1553562 * 2 ^ 59
def prefixEnd_1553562 : Nat := 4983230072969 + 3 ^ 40 * 1553562 * 2
def baseEnd_1553562 : Nat := 265908010853451971743435

theorem tailTrace_1553562 : CollatzResearch.WordTrace tailWord_1553562 prefixEnd_1553562 265908010853451971743435 := by
  unfold tailWord_1553562
  simp only [CollatzResearch.WordTrace]
  refine ⟨14165765299429419027731735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37775374131811784073951293 14165765299429419027731735)
  ·
    refine ⟨21248647949144128541597603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14165765299429419027731735 21248647949144128541597603)
    ·
      refine ⟨31872971923716192812396405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21248647949144128541597603 31872971923716192812396405)
      ·
        refine ⟨2988091117848393076162163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31872971923716192812396405 2988091117848393076162163)
        ·
          refine ⟨4482136676772589614243245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2988091117848393076162163 4482136676772589614243245)
          ·
            refine ⟨1680801253789721105341217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4482136676772589614243245 1680801253789721105341217)
            ·
              refine ⟨1260600940342290829005913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1680801253789721105341217 1260600940342290829005913)
              ·
                refine ⟨945450705256718121754435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1260600940342290829005913 945450705256718121754435)
                ·
                  refine ⟨1418176057885077182631653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 945450705256718121754435 1418176057885077182631653)
                  ·
                    refine ⟨265908010853451971743435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1418176057885077182631653 265908010853451971743435)
                    ·
                      rfl

theorem cell23_1553562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 1, 4].length) (baseStart_1553562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553562 prefixEnd_1553562 := by exact prefixLift 1553562
  have htrace : WordTrace (prefixWord ++ tailWord_1553562) baseStart_1553562 baseEnd_1553562 := by
    simpa [prefixWord, tailWord_1553562, baseEnd_1553562] using wordTrace_append hprefix tailTrace_1553562
  have hstable : (prefixWord ++ tailWord_1553562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553562).length < 2 ^ (prefixWord ++ tailWord_1553562).sum := by decide
  have hdescent : baseEnd_1553562 < baseStart_1553562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553591 : List Nat := [1, 1, 3, 1, 4, 1, 2, 4, 1, 1, 4]
def baseStart_1553591 : Nat := 118140960795 + 1553591 * 2 ^ 59
def prefixEnd_1553591 : Nat := 4983230072969 + 3 ^ 40 * 1553591 * 2
def baseEnd_1553591 : Nat := 797738923499336301767671

theorem tailTrace_1553591 : CollatzResearch.WordTrace tailWord_1553591 prefixEnd_1553591 797738923499336301767671 := by
  unfold tailWord_1553591
  simp only [CollatzResearch.WordTrace]
  refine ⟨56664118914612614063732627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37776079276408409375821751 56664118914612614063732627)
  ·
    refine ⟨84996178371918921095598941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56664118914612614063732627 84996178371918921095598941)
    ·
      refine ⟨31873566889469595410849603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84996178371918921095598941 31873566889469595410849603)
      ·
        refine ⟨47810350334204393116274405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31873566889469595410849603 47810350334204393116274405)
        ·
          refine ⟨8964440687663323709301451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47810350334204393116274405 8964440687663323709301451)
          ·
            refine ⟨13446661031494985563952177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8964440687663323709301451 13446661031494985563952177)
            ·
              refine ⟨10084995773621239172964133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13446661031494985563952177 10084995773621239172964133)
              ·
                refine ⟨1890936707553982344930775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10084995773621239172964133 1890936707553982344930775)
                ·
                  refine ⟨2836405061330973517396163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890936707553982344930775 2836405061330973517396163)
                  ·
                    refine ⟨4254607591996460276094245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2836405061330973517396163 4254607591996460276094245)
                    ·
                      refine ⟨797738923499336301767671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4254607591996460276094245 797738923499336301767671)
                      ·
                        rfl

theorem cell23_1553591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 1, 4].length) (baseStart_1553591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553591 prefixEnd_1553591 := by exact prefixLift 1553591
  have htrace : WordTrace (prefixWord ++ tailWord_1553591) baseStart_1553591 baseEnd_1553591 := by
    simpa [prefixWord, tailWord_1553591, baseEnd_1553591] using wordTrace_append hprefix tailTrace_1553591
  have hstable : (prefixWord ++ tailWord_1553591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553591).length < 2 ^ (prefixWord ++ tailWord_1553591).sum := by decide
  have hdescent : baseEnd_1553591 < baseStart_1553591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553608 : List Nat := [2, 1, 3, 1, 2, 1, 6, 1, 1, 1, 4]
def baseStart_1553608 : Nat := 118140960795 + 1553608 * 2 ^ 59
def prefixEnd_1553608 : Nat := 4983230072969 + 3 ^ 40 * 1553608 * 2
def baseEnd_1553608 : Nat := 797747652670462735255093

theorem tailTrace_1553608 : CollatzResearch.WordTrace tailWord_1553608 prefixEnd_1553608 797747652670462735255093 := by
  unfold tailWord_1553608
  simp only [CollatzResearch.WordTrace]
  refine ⟨28332369477775512983550739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37776492637034017311400985 28332369477775512983550739)
  ·
    refine ⟨42498554216663269475326109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28332369477775512983550739 42498554216663269475326109)
    ·
      refine ⟨15936957831248726053247291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42498554216663269475326109 15936957831248726053247291)
      ·
        refine ⟨23905436746873089079870937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15936957831248726053247291 23905436746873089079870937)
        ·
          refine ⟨17929077560154816809903203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23905436746873089079870937 17929077560154816809903203)
          ·
            refine ⟨26893616340232225214854805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17929077560154816809903203 26893616340232225214854805)
            ·
              refine ⟨1260638265948385556946319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26893616340232225214854805 1260638265948385556946319)
              ·
                refine ⟨1890957398922578335419479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1260638265948385556946319 1890957398922578335419479)
                ·
                  refine ⟨2836436098383867503129219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890957398922578335419479 2836436098383867503129219)
                  ·
                    refine ⟨4254654147575801254693829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2836436098383867503129219 4254654147575801254693829)
                    ·
                      refine ⟨797747652670462735255093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4254654147575801254693829 797747652670462735255093)
                      ·
                        rfl

theorem cell23_1553608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_1553608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553608 prefixEnd_1553608 := by exact prefixLift 1553608
  have htrace : WordTrace (prefixWord ++ tailWord_1553608) baseStart_1553608 baseEnd_1553608 := by
    simpa [prefixWord, tailWord_1553608, baseEnd_1553608] using wordTrace_append hprefix tailTrace_1553608
  have hstable : (prefixWord ++ tailWord_1553608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553608).length < 2 ^ (prefixWord ++ tailWord_1553608).sum := by decide
  have hdescent : baseEnd_1553608 < baseStart_1553608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553641 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 8, 1, 3]
def baseStart_1553641 : Nat := 118140960795 + 1553641 * 2 ^ 59
def prefixEnd_1553641 : Nat := 4983230072969 + 3 ^ 40 * 1553641 * 2
def baseEnd_1553641 : Nat := 797764597532061106142441

theorem tailTrace_1553641 : CollatzResearch.WordTrace tailWord_1553641 prefixEnd_1553641 797764597532061106142441 := by
  unfold tailWord_1553641
  simp only [CollatzResearch.WordTrace]
  refine ⟨56665942564431472603052777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37777295042954315068701851 56665942564431472603052777)
  ·
    refine ⟨42499456923323604452289583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56665942564431472603052777 42499456923323604452289583)
    ·
      refine ⟨63749185384985406678434375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42499456923323604452289583 63749185384985406678434375)
      ·
        refine ⟨95623778077478110017651563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63749185384985406678434375 95623778077478110017651563)
        ·
          refine ⟨143435667116217165026477345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95623778077478110017651563 143435667116217165026477345)
          ·
            refine ⟨107576750337162873769858009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143435667116217165026477345 107576750337162873769858009)
            ·
              refine ⟨80682562752872155327393507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107576750337162873769858009 80682562752872155327393507)
              ·
                refine ⟨121023844129308232991090261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80682562752872155327393507 121023844129308232991090261)
                ·
                  refine ⟨1418248173390330855364339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 121023844129308232991090261 1418248173390330855364339)
                  ·
                    refine ⟨2127372260085496283046509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1418248173390330855364339 2127372260085496283046509)
                    ·
                      refine ⟨797764597532061106142441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2127372260085496283046509 797764597532061106142441)
                      ·
                        rfl

theorem cell23_1553641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 1, 3].length) (baseStart_1553641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553641 prefixEnd_1553641 := by exact prefixLift 1553641
  have htrace : WordTrace (prefixWord ++ tailWord_1553641) baseStart_1553641 baseEnd_1553641 := by
    simpa [prefixWord, tailWord_1553641, baseEnd_1553641] using wordTrace_append hprefix tailTrace_1553641
  have hstable : (prefixWord ++ tailWord_1553641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553641).length < 2 ^ (prefixWord ++ tailWord_1553641).sum := by decide
  have hdescent : baseEnd_1553641 < baseStart_1553641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553645 : List Nat := [1, 5, 1, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_1553645 : Nat := 118140960795 + 1553645 * 2 ^ 59
def prefixEnd_1553645 : Nat := 4983230072969 + 3 ^ 40 * 1553645 * 2
def baseEnd_1553645 : Nat := 797766651454679090492423

theorem tailTrace_1553645 : CollatzResearch.WordTrace tailWord_1553645 prefixEnd_1553645 797766651454679090492423 := by
  unfold tailWord_1553645
  simp only [CollatzResearch.WordTrace]
  refine ⟨56666088456416981286198389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37777392304277987524132259 56666088456416981286198389)
  ·
    refine ⟨5312445792789091995581099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56666088456416981286198389 5312445792789091995581099)
    ·
      refine ⟨7968668689183637993371649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5312445792789091995581099 7968668689183637993371649)
      ·
        refine ⟨5976501516887728495028737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7968668689183637993371649 5976501516887728495028737)
        ·
          refine ⟨4482376137665796371271553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5976501516887728495028737 4482376137665796371271553)
          ·
            refine ⟨3361782103249347278453665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4482376137665796371271553 3361782103249347278453665)
            ·
              refine ⟨2521336577437010458840249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3361782103249347278453665 2521336577437010458840249)
              ·
                refine ⟨1891002433077757844130187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2521336577437010458840249 1891002433077757844130187)
                ·
                  refine ⟨2836503649616636766195281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1891002433077757844130187 2836503649616636766195281)
                  ·
                    refine ⟨2127377737212477574646461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2836503649616636766195281 2127377737212477574646461)
                    ·
                      refine ⟨797766651454679090492423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2127377737212477574646461 797766651454679090492423)
                      ·
                        rfl

theorem cell23_1553645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_1553645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553645 prefixEnd_1553645 := by exact prefixLift 1553645
  have htrace : WordTrace (prefixWord ++ tailWord_1553645) baseStart_1553645 baseEnd_1553645 := by
    simpa [prefixWord, tailWord_1553645, baseEnd_1553645] using wordTrace_append hprefix tailTrace_1553645
  have hstable : (prefixWord ++ tailWord_1553645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553645).length < 2 ^ (prefixWord ++ tailWord_1553645).sum := by decide
  have hdescent : baseEnd_1553645 < baseStart_1553645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553664 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 4]
def baseStart_1553664 : Nat := 118140960795 + 1553664 * 2 ^ 59
def prefixEnd_1553664 : Nat := 4983230072969 + 3 ^ 40 * 1553664 * 2
def baseEnd_1553664 : Nat := 797776407587114516154835

theorem tailTrace_1553664 : CollatzResearch.WordTrace tailWord_1553664 prefixEnd_1553664 797776407587114516154835 := by
  unfold tailWord_1553664
  simp only [CollatzResearch.WordTrace]
  refine ⟨28333390721674073765570023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37777854295565431687426697 28333390721674073765570023)
  ·
    refine ⟨42500086082511110648355035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28333390721674073765570023 42500086082511110648355035)
    ·
      refine ⟨63750129123766665972532553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42500086082511110648355035 63750129123766665972532553)
      ·
        refine ⟨47812596842824999479399415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63750129123766665972532553 47812596842824999479399415)
        ·
          refine ⟨71718895264237499219099123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47812596842824999479399415 71718895264237499219099123)
          ·
            refine ⟨107578342896356248828648685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71718895264237499219099123 107578342896356248828648685)
            ·
              refine ⟨40341878586133593310743257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107578342896356248828648685 40341878586133593310743257)
              ·
                refine ⟨30256408939600194983057443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40341878586133593310743257 30256408939600194983057443)
                ·
                  refine ⟨45384613409400292474586165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30256408939600194983057443 45384613409400292474586165)
                  ·
                    refine ⟨4254807507131277419492453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45384613409400292474586165 4254807507131277419492453)
                    ·
                      refine ⟨797776407587114516154835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4254807507131277419492453 797776407587114516154835)
                      ·
                        rfl

theorem cell23_1553664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_1553664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553664 prefixEnd_1553664 := by exact prefixLift 1553664
  have htrace : WordTrace (prefixWord ++ tailWord_1553664) baseStart_1553664 baseEnd_1553664 := by
    simpa [prefixWord, tailWord_1553664, baseEnd_1553664] using wordTrace_append hprefix tailTrace_1553664
  have hstable : (prefixWord ++ tailWord_1553664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553664).length < 2 ^ (prefixWord ++ tailWord_1553664).sum := by decide
  have hdescent : baseEnd_1553664 < baseStart_1553664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553701 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 2, 1, 5]
def baseStart_1553701 : Nat := 118140960795 + 1553701 * 2 ^ 59
def prefixEnd_1553701 : Nat := 4983230072969 + 3 ^ 40 * 1553701 * 2
def baseEnd_1553701 : Nat := 797795406371330871392165

theorem tailTrace_1553701 : CollatzResearch.WordTrace tailWord_1553701 prefixEnd_1553701 797795406371330871392165 := by
  unfold tailWord_1553701
  simp only [CollatzResearch.WordTrace]
  refine ⟨56668130944214102850236957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37778753962809401900157971 56668130944214102850236957)
  ·
    refine ⟨21250549104080288568838859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56668130944214102850236957 21250549104080288568838859)
    ·
      refine ⟨31875823656120432853258289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21250549104080288568838859 31875823656120432853258289)
      ·
        refine ⟨23906867742090324639943717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31875823656120432853258289 23906867742090324639943717)
        ·
          refine ⟨4482537701641935869989447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23906867742090324639943717 4482537701641935869989447)
          ·
            refine ⟨6723806552462903804984171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4482537701641935869989447 6723806552462903804984171)
            ·
              refine ⟨10085709828694355707476257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6723806552462903804984171 10085709828694355707476257)
              ·
                refine ⟨7564282371520766780607193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10085709828694355707476257 7564282371520766780607193)
                ·
                  refine ⟨5673211778640575085455395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7564282371520766780607193 5673211778640575085455395)
                  ·
                    refine ⟨8509817667960862628183093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5673211778640575085455395 8509817667960862628183093)
                    ·
                      refine ⟨797795406371330871392165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8509817667960862628183093 797795406371330871392165)
                      ·
                        rfl

theorem cell23_1553701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_1553701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553701 prefixEnd_1553701 := by exact prefixLift 1553701
  have htrace : WordTrace (prefixWord ++ tailWord_1553701) baseStart_1553701 baseEnd_1553701 := by
    simpa [prefixWord, tailWord_1553701, baseEnd_1553701] using wordTrace_append hprefix tailTrace_1553701
  have hstable : (prefixWord ++ tailWord_1553701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553701).length < 2 ^ (prefixWord ++ tailWord_1553701).sum := by decide
  have hdescent : baseEnd_1553701 < baseStart_1553701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553731 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 3]
def baseStart_1553731 : Nat := 118140960795 + 1553731 * 2 ^ 59
def prefixEnd_1553731 : Nat := 4983230072969 + 3 ^ 40 * 1553731 * 2
def baseEnd_1553731 : Nat := 797810810790965754017027

theorem tailTrace_1553731 : CollatzResearch.WordTrace tailWord_1553731 prefixEnd_1553731 797810810790965754017027 := by
  unfold tailWord_1553731
  simp only [CollatzResearch.WordTrace]
  refine ⟨56669225134105417973829047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37779483422736945315886031 56669225134105417973829047)
  ·
    refine ⟨85003837701158126960743571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56669225134105417973829047 85003837701158126960743571)
    ·
      refine ⟨127505756551737190441115357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85003837701158126960743571 127505756551737190441115357)
      ·
        refine ⟨47814658706901446415418259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127505756551737190441115357 47814658706901446415418259)
        ·
          refine ⟨71721988060352169623127389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47814658706901446415418259 71721988060352169623127389)
          ·
            refine ⟨26895745522632063608672771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71721988060352169623127389 26895745522632063608672771)
            ·
              refine ⟨40343618283948095413009157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26895745522632063608672771 40343618283948095413009157)
              ·
                refine ⟨7564428428240267889939217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40343618283948095413009157 7564428428240267889939217)
                ·
                  refine ⟨5673321321180200917454413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7564428428240267889939217 5673321321180200917454413)
                  ·
                    refine ⟨2127495495442575344045405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5673321321180200917454413 2127495495442575344045405)
                    ·
                      refine ⟨797810810790965754017027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2127495495442575344045405 797810810790965754017027)
                      ·
                        rfl

theorem cell23_1553731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_1553731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553731 prefixEnd_1553731 := by exact prefixLift 1553731
  have htrace : WordTrace (prefixWord ++ tailWord_1553731) baseStart_1553731 baseEnd_1553731 := by
    simpa [prefixWord, tailWord_1553731, baseEnd_1553731] using wordTrace_append hprefix tailTrace_1553731
  have hstable : (prefixWord ++ tailWord_1553731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553731).length < 2 ^ (prefixWord ++ tailWord_1553731).sum := by decide
  have hdescent : baseEnd_1553731 < baseStart_1553731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553748 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_1553748 : Nat := 118140960795 + 1553748 * 2 ^ 59
def prefixEnd_1553748 : Nat := 4983230072969 + 3 ^ 40 * 1553748 * 2
def baseEnd_1553748 : Nat := 797819539962092187504449

theorem tailTrace_1553748 : CollatzResearch.WordTrace tailWord_1553748 prefixEnd_1553748 797819539962092187504449 := by
  unfold tailWord_1553748
  simp only [CollatzResearch.WordTrace]
  refine ⟨28334922587521914938598949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37779896783362553251465265 28334922587521914938598949)
  ·
    refine ⟨5312797985160359050987303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28334922587521914938598949 5312797985160359050987303)
    ·
      refine ⟨7969196977740538576480955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5312797985160359050987303 7969196977740538576480955)
      ·
        refine ⟨11953795466610807864721433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7969196977740538576480955 11953795466610807864721433)
        ·
          refine ⟨8965346599958105898541075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11953795466610807864721433 8965346599958105898541075)
          ·
            refine ⟨13448019899937158847811613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8965346599958105898541075 13448019899937158847811613)
            ·
              refine ⟨5043007462476434567929355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13448019899937158847811613 5043007462476434567929355)
              ·
                refine ⟨7564511193714651851894033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5043007462476434567929355 7564511193714651851894033)
                ·
                  refine ⟨5673383395285988888920525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7564511193714651851894033 5673383395285988888920525)
                  ·
                    refine ⟨2127518773232245833345197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5673383395285988888920525 2127518773232245833345197)
                    ·
                      refine ⟨797819539962092187504449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2127518773232245833345197 797819539962092187504449)
                      ·
                        rfl

theorem cell23_1553748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_1553748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553748 prefixEnd_1553748 := by exact prefixLift 1553748
  have htrace : WordTrace (prefixWord ++ tailWord_1553748) baseStart_1553748 baseEnd_1553748 := by
    simpa [prefixWord, tailWord_1553748, baseEnd_1553748] using wordTrace_append hprefix tailTrace_1553748
  have hstable : (prefixWord ++ tailWord_1553748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553748).length < 2 ^ (prefixWord ++ tailWord_1553748).sum := by decide
  have hdescent : baseEnd_1553748 < baseStart_1553748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553768 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 1, 7]
def baseStart_1553768 : Nat := 118140960795 + 1553768 * 2 ^ 59
def prefixEnd_1553768 : Nat := 4983230072969 + 3 ^ 40 * 1553768 * 2
def baseEnd_1553768 : Nat := 265943269858394036418119

theorem tailTrace_1553768 : CollatzResearch.WordTrace tailWord_1553768 prefixEnd_1553768 265943269858394036418119 := by
  unfold tailWord_1553768
  simp only [CollatzResearch.WordTrace]
  refine ⟨28335287317485686646462979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37780383089980915528617305 28335287317485686646462979)
  ·
    refine ⟨42502930976228529969694469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28335287317485686646462979 42502930976228529969694469)
    ·
      refine ⟨7969299558042849369317713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42502930976228529969694469 7969299558042849369317713)
      ·
        refine ⟨5976974668532137026988285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7969299558042849369317713 5976974668532137026988285)
        ·
          refine ⟨2241365500699551385120607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5976974668532137026988285 2241365500699551385120607)
          ·
            refine ⟨3362048251049327077680911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2241365500699551385120607 3362048251049327077680911)
            ·
              refine ⟨5043072376573990616521367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3362048251049327077680911 5043072376573990616521367)
              ·
                refine ⟨7564608564860985924782051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5043072376573990616521367 7564608564860985924782051)
                ·
                  refine ⟨11346912847291478887173077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7564608564860985924782051 11346912847291478887173077)
                  ·
                    refine ⟨265943269858394036418119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11346912847291478887173077 265943269858394036418119)
                    ·
                      rfl

theorem cell23_1553768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_1553768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553768 prefixEnd_1553768 := by exact prefixLift 1553768
  have htrace : WordTrace (prefixWord ++ tailWord_1553768) baseStart_1553768 baseEnd_1553768 := by
    simpa [prefixWord, tailWord_1553768, baseEnd_1553768] using wordTrace_append hprefix tailTrace_1553768
  have hstable : (prefixWord ++ tailWord_1553768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553768).length < 2 ^ (prefixWord ++ tailWord_1553768).sum := by decide
  have hdescent : baseEnd_1553768 < baseStart_1553768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553788 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 4, 4, 2]
def baseStart_1553788 : Nat := 118140960795 + 1553788 * 2 ^ 59
def prefixEnd_1553788 : Nat := 4983230072969 + 3 ^ 40 * 1553788 * 2
def baseEnd_1553788 : Nat := 797840079188272031004265

theorem tailTrace_1553788 : CollatzResearch.WordTrace tailWord_1553788 prefixEnd_1553788 797840079188272031004265 := by
  unfold tailWord_1553788
  simp only [CollatzResearch.WordTrace]
  refine ⟨28335652047449458354327009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37780869396599277805769345 28335652047449458354327009)
  ·
    refine ⟨21251739035587093765745257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28335652047449458354327009 21251739035587093765745257)
    ·
      refine ⟨15938804276690320324308943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21251739035587093765745257 15938804276690320324308943)
      ·
        refine ⟨23908206415035480486463415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15938804276690320324308943 23908206415035480486463415)
        ·
          refine ⟨35862309622553220729695123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23908206415035480486463415 35862309622553220729695123)
          ·
            refine ⟨53793464433829831094542685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35862309622553220729695123 53793464433829831094542685)
            ·
              refine ⟨20172549162686186660453507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53793464433829831094542685 20172549162686186660453507)
              ·
                refine ⟨30258823744029279990680261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20172549162686186660453507 30258823744029279990680261)
                ·
                  refine ⟨5673529452005489998252549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30258823744029279990680261 5673529452005489998252549)
                  ·
                    refine ⟨1063786772251029374672353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5673529452005489998252549 1063786772251029374672353)
                    ·
                      refine ⟨797840079188272031004265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1063786772251029374672353 797840079188272031004265)
                      ·
                        rfl

theorem cell23_1553788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_1553788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553788 prefixEnd_1553788 := by exact prefixLift 1553788
  have htrace : WordTrace (prefixWord ++ tailWord_1553788) baseStart_1553788 baseEnd_1553788 := by
    simpa [prefixWord, tailWord_1553788, baseEnd_1553788] using wordTrace_append hprefix tailTrace_1553788
  have hstable : (prefixWord ++ tailWord_1553788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553788).length < 2 ^ (prefixWord ++ tailWord_1553788).sum := by decide
  have hdescent : baseEnd_1553788 < baseStart_1553788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553791 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 3]
def baseStart_1553791 : Nat := 118140960795 + 1553791 * 2 ^ 59
def prefixEnd_1553791 : Nat := 4983230072969 + 3 ^ 40 * 1553791 * 2
def baseEnd_1553791 : Nat := 797841619630235519266751

theorem tailTrace_1553791 : CollatzResearch.WordTrace tailWord_1553791 prefixEnd_1553791 797841619630235519266751 := by
  unfold tailWord_1553791
  simp only [CollatzResearch.WordTrace]
  refine ⟨56671413513888048221013227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37780942342592032147342151 56671413513888048221013227)
  ·
    refine ⟨85007120270832072331519841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56671413513888048221013227 85007120270832072331519841)
    ·
      refine ⟨63755340203124054248639881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85007120270832072331519841 63755340203124054248639881)
      ·
        refine ⟨47816505152343040686479911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63755340203124054248639881 47816505152343040686479911)
        ·
          refine ⟨71724757728514561029719867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47816505152343040686479911 71724757728514561029719867)
          ·
            refine ⟨107587136592771841544579801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71724757728514561029719867 107587136592771841544579801)
            ·
              refine ⟨80690352444578881158434851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107587136592771841544579801 80690352444578881158434851)
              ·
                refine ⟨121035528666868321737652277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80690352444578881158434851 121035528666868321737652277)
                ·
                  refine ⟨11347080812518905162904901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121035528666868321737652277 11347080812518905162904901)
                  ·
                    refine ⟨2127577652347294718044669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11347080812518905162904901 2127577652347294718044669)
                    ·
                      refine ⟨797841619630235519266751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2127577652347294718044669 797841619630235519266751)
                      ·
                        rfl

theorem cell23_1553791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_1553791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553791 prefixEnd_1553791 := by exact prefixLift 1553791
  have htrace : WordTrace (prefixWord ++ tailWord_1553791) baseStart_1553791 baseEnd_1553791 := by
    simpa [prefixWord, tailWord_1553791, baseEnd_1553791] using wordTrace_append hprefix tailTrace_1553791
  have hstable : (prefixWord ++ tailWord_1553791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553791).length < 2 ^ (prefixWord ++ tailWord_1553791).sum := by decide
  have hdescent : baseEnd_1553791 < baseStart_1553791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553849 : List Nat := [1, 2, 1, 4, 4, 1, 3, 2, 1, 4]
def baseStart_1553849 : Nat := 118140960795 + 1553849 * 2 ^ 59
def prefixEnd_1553849 : Nat := 4983230072969 + 3 ^ 40 * 1553849 * 2
def baseEnd_1553849 : Nat := 265957133836065430780495

theorem tailTrace_1553849 : CollatzResearch.WordTrace tailWord_1553849 prefixEnd_1553849 265957133836065430780495 := by
  unfold tailWord_1553849
  simp only [CollatzResearch.WordTrace]
  refine ⟨56673528947677924126624601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37782352631785282751083067 56673528947677924126624601)
  ·
    refine ⟨42505146710758443094968451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56673528947677924126624601 42505146710758443094968451)
    ·
      refine ⟨63757720066137664642452677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42505146710758443094968451 63757720066137664642452677)
      ·
        refine ⟨11954572512400812120459877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63757720066137664642452677 11954572512400812120459877)
        ·
          refine ⟨2241482346075152272586227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11954572512400812120459877 2241482346075152272586227)
          ·
            refine ⟨3362223519112728408879341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2241482346075152272586227 3362223519112728408879341)
            ·
              refine ⟨1260833819667273153329753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3362223519112728408879341 1260833819667273153329753)
              ·
                refine ⟨945625364750454864997315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1260833819667273153329753 945625364750454864997315)
                ·
                  refine ⟨1418438047125682297495973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 945625364750454864997315 1418438047125682297495973)
                  ·
                    refine ⟨265957133836065430780495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1418438047125682297495973 265957133836065430780495)
                    ·
                      rfl

theorem cell23_1553849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 1, 4].length) (baseStart_1553849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553849 prefixEnd_1553849 := by exact prefixLift 1553849
  have htrace : WordTrace (prefixWord ++ tailWord_1553849) baseStart_1553849 baseEnd_1553849 := by
    simpa [prefixWord, tailWord_1553849, baseEnd_1553849] using wordTrace_append hprefix tailTrace_1553849
  have hstable : (prefixWord ++ tailWord_1553849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553849).length < 2 ^ (prefixWord ++ tailWord_1553849).sum := by decide
  have hdescent : baseEnd_1553849 < baseStart_1553849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553882 : List Nat := [3, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2]
def baseStart_1553882 : Nat := 118140960795 + 1553882 * 2 ^ 59
def prefixEnd_1553882 : Nat := 4983230072969 + 3 ^ 40 * 1553882 * 2
def baseEnd_1553882 : Nat := 797888346369794663228833

theorem tailTrace_1553882 : CollatzResearch.WordTrace tailWord_1553882 prefixEnd_1553882 797888346369794663228833 := by
  unfold tailWord_1553882
  simp only [CollatzResearch.WordTrace]
  refine ⟨14168683139139592690643975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37783155037705580508383933 14168683139139592690643975)
  ·
    refine ⟨21253024708709389035965963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14168683139139592690643975 21253024708709389035965963)
    ·
      refine ⟨31879537063064083553948945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21253024708709389035965963 31879537063064083553948945)
      ·
        refine ⟨23909652797298062665461709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31879537063064083553948945 23909652797298062665461709)
        ·
          refine ⟨8966119798986773499548141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23909652797298062665461709 8966119798986773499548141)
          ·
            refine ⟨3362294924620040062330553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8966119798986773499548141 3362294924620040062330553)
            ·
              refine ⟨2521721193465030046747915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3362294924620040062330553 2521721193465030046747915)
              ·
                refine ⟨3782581790197545070121873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2521721193465030046747915 3782581790197545070121873)
                ·
                  refine ⟨2836936342648158802591405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3782581790197545070121873 2836936342648158802591405)
                  ·
                    refine ⟨1063851128493059550971777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2836936342648158802591405 1063851128493059550971777)
                    ·
                      refine ⟨797888346369794663228833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1063851128493059550971777 797888346369794663228833)
                      ·
                        rfl

theorem cell23_1553882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_1553882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553882 prefixEnd_1553882 := by exact prefixLift 1553882
  have htrace : WordTrace (prefixWord ++ tailWord_1553882) baseStart_1553882 baseEnd_1553882 := by
    simpa [prefixWord, tailWord_1553882, baseEnd_1553882] using wordTrace_append hprefix tailTrace_1553882
  have hstable : (prefixWord ++ tailWord_1553882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553882).length < 2 ^ (prefixWord ++ tailWord_1553882).sum := by decide
  have hdescent : baseEnd_1553882 < baseStart_1553882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553888 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 4, 4]
def baseStart_1553888 : Nat := 118140960795 + 1553888 * 2 ^ 59
def prefixEnd_1553888 : Nat := 4983230072969 + 3 ^ 40 * 1553888 * 2
def baseEnd_1553888 : Nat := 265963809084573879917935

theorem tailTrace_1553888 : CollatzResearch.WordTrace tailWord_1553888 prefixEnd_1553888 265963809084573879917935 := by
  unfold tailWord_1553888
  simp only [CollatzResearch.WordTrace]
  refine ⟨28337475697268316893647159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37783300929691089191529545 28337475697268316893647159)
  ·
    refine ⟨42506213545902475340470739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28337475697268316893647159 42506213545902475340470739)
    ·
      refine ⟨63759320318853713010706109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42506213545902475340470739 63759320318853713010706109)
      ·
        refine ⟨23909745119570142379014791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63759320318853713010706109 23909745119570142379014791)
        ·
          refine ⟨35864617679355213568522187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23909745119570142379014791 35864617679355213568522187)
          ·
            refine ⟨53796926519032820352783281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35864617679355213568522187 53796926519032820352783281)
            ·
              refine ⟨40347694889274615264587461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53796926519032820352783281 40347694889274615264587461)
              ·
                refine ⟨7565192791738990362110149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40347694889274615264587461 7565192791738990362110149)
                ·
                  refine ⟨1418473648451060692895653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7565192791738990362110149 1418473648451060692895653)
                  ·
                    refine ⟨265963809084573879917935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1418473648451060692895653 265963809084573879917935)
                    ·
                      rfl

theorem cell23_1553888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 4, 4].length) (baseStart_1553888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553888 prefixEnd_1553888 := by exact prefixLift 1553888
  have htrace : WordTrace (prefixWord ++ tailWord_1553888) baseStart_1553888 baseEnd_1553888 := by
    simpa [prefixWord, tailWord_1553888, baseEnd_1553888] using wordTrace_append hprefix tailTrace_1553888
  have hstable : (prefixWord ++ tailWord_1553888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553888).length < 2 ^ (prefixWord ++ tailWord_1553888).sum := by decide
  have hdescent : baseEnd_1553888 < baseStart_1553888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553905 : List Nat := [1, 2, 2, 2, 3, 2, 1, 4, 2, 4]
def baseStart_1553905 : Nat := 118140960795 + 1553905 * 2 ^ 59
def prefixEnd_1553905 : Nat := 4983230072969 + 3 ^ 40 * 1553905 * 2
def baseEnd_1553905 : Nat := 265966718808282691080409

theorem tailTrace_1553905 : CollatzResearch.WordTrace tailWord_1553905 prefixEnd_1553905 265966718808282691080409 := by
  unfold tailWord_1553905
  simp only [CollatzResearch.WordTrace]
  refine ⟨56675571435475045690663169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37783714290316697127108779 56675571435475045690663169)
  ·
    refine ⟨42506678576606284267997377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56675571435475045690663169 42506678576606284267997377)
    ·
      refine ⟨31880008932454713200998033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42506678576606284267997377 31880008932454713200998033)
      ·
        refine ⟨23910006699341034900748525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31880008932454713200998033 23910006699341034900748525)
        ·
          refine ⟨8966252512252888087780697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23910006699341034900748525 8966252512252888087780697)
          ·
            refine ⟨6724689384189666065835523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8966252512252888087780697 6724689384189666065835523)
            ·
              refine ⟨10087034076284499098753285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6724689384189666065835523 10087034076284499098753285)
              ·
                refine ⟨1891318889303343581016241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10087034076284499098753285 1891318889303343581016241)
                ·
                  refine ⟨1418489166977507685762181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1891318889303343581016241 1418489166977507685762181)
                  ·
                    refine ⟨265966718808282691080409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1418489166977507685762181 265966718808282691080409)
                    ·
                      rfl

theorem cell23_1553905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_1553905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553905 prefixEnd_1553905 := by exact prefixLift 1553905
  have htrace : WordTrace (prefixWord ++ tailWord_1553905) baseStart_1553905 baseEnd_1553905 := by
    simpa [prefixWord, tailWord_1553905, baseEnd_1553905] using wordTrace_append hprefix tailTrace_1553905
  have hstable : (prefixWord ++ tailWord_1553905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553905).length < 2 ^ (prefixWord ++ tailWord_1553905).sum := by decide
  have hdescent : baseEnd_1553905 < baseStart_1553905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553906 : List Nat := [3, 2, 1, 4, 1, 1, 4, 2, 1, 1, 3]
def baseStart_1553906 : Nat := 118140960795 + 1553906 * 2 ^ 59
def prefixEnd_1553906 : Nat := 4983230072969 + 3 ^ 40 * 1553906 * 2
def baseEnd_1553906 : Nat := 797900669905502569328723

theorem tailTrace_1553906 : CollatzResearch.WordTrace tailWord_1553906 prefixEnd_1553906 797900669905502569328723 := by
  unfold tailWord_1553906
  simp only [CollatzResearch.WordTrace]
  refine ⟨14168901977117855715362393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37783738605647615240966381 14168901977117855715362393)
  ·
    refine ⟨10626676482838391786521795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14168901977117855715362393 10626676482838391786521795)
    ·
      refine ⟨15940014724257587679782693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10626676482838391786521795 15940014724257587679782693)
      ·
        refine ⟨2988752760798297689959255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15940014724257587679782693 2988752760798297689959255)
        ·
          refine ⟨4483129141197446534938883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2988752760798297689959255 4483129141197446534938883)
          ·
            refine ⟨6724693711796169802408325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4483129141197446534938883 6724693711796169802408325)
            ·
              refine ⟨1260880070961781837951561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6724693711796169802408325 1260880070961781837951561)
              ·
                refine ⟨945660053221336378463671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1260880070961781837951561 945660053221336378463671)
                ·
                  refine ⟨1418490079832004567695507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 945660053221336378463671 1418490079832004567695507)
                  ·
                    refine ⟨2127735119748006851543261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1418490079832004567695507 2127735119748006851543261)
                    ·
                      refine ⟨797900669905502569328723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2127735119748006851543261 797900669905502569328723)
                      ·
                        rfl

theorem cell23_1553906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_1553906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553906 prefixEnd_1553906 := by exact prefixLift 1553906
  have htrace : WordTrace (prefixWord ++ tailWord_1553906) baseStart_1553906 baseEnd_1553906 := by
    simpa [prefixWord, tailWord_1553906, baseEnd_1553906] using wordTrace_append hprefix tailTrace_1553906
  have hstable : (prefixWord ++ tailWord_1553906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553906).length < 2 ^ (prefixWord ++ tailWord_1553906).sum := by decide
  have hdescent : baseEnd_1553906 < baseStart_1553906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553911 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 7]
def baseStart_1553911 : Nat := 118140960795 + 1553911 * 2 ^ 59
def prefixEnd_1553911 : Nat := 4983230072969 + 3 ^ 40 * 1553911 * 2
def baseEnd_1553911 : Nat := 797903237308775049766199

theorem tailTrace_1553911 : CollatzResearch.WordTrace tailWord_1553911 prefixEnd_1553911 797903237308775049766199 := by
  unfold tailWord_1553911
  simp only [CollatzResearch.WordTrace]
  refine ⟨56675790273453308715381587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37783860182302205810254391 56675790273453308715381587)
  ·
    refine ⟨85013685410179963073072381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56675790273453308715381587 85013685410179963073072381)
    ·
      refine ⟨31880132028817486152402143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85013685410179963073072381 31880132028817486152402143)
      ·
        refine ⟨47820198043226229228603215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31880132028817486152402143 47820198043226229228603215)
        ·
          refine ⟨71730297064839343842904823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47820198043226229228603215 71730297064839343842904823)
          ·
            refine ⟨107595445597259015764357235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71730297064839343842904823 107595445597259015764357235)
            ·
              refine ⟨161393168395888523646535853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107595445597259015764357235 161393168395888523646535853)
              ·
                refine ⟨60522438148458196367450945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161393168395888523646535853 60522438148458196367450945)
                ·
                  refine ⟨45391828611343647275588209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60522438148458196367450945 45391828611343647275588209)
                  ·
                    refine ⟨34043871458507735456691157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45391828611343647275588209 34043871458507735456691157)
                    ·
                      refine ⟨797903237308775049766199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34043871458507735456691157 797903237308775049766199)
                      ·
                        rfl

theorem cell23_1553911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_1553911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553911 prefixEnd_1553911 := by exact prefixLift 1553911
  have htrace : WordTrace (prefixWord ++ tailWord_1553911) baseStart_1553911 baseEnd_1553911 := by
    simpa [prefixWord, tailWord_1553911, baseEnd_1553911] using wordTrace_append hprefix tailTrace_1553911
  have hstable : (prefixWord ++ tailWord_1553911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553911).length < 2 ^ (prefixWord ++ tailWord_1553911).sum := by decide
  have hdescent : baseEnd_1553911 < baseStart_1553911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553922 : List Nat := [3, 4, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_1553922 : Nat := 118140960795 + 1553922 * 2 ^ 59
def prefixEnd_1553922 : Nat := 4983230072969 + 3 ^ 40 * 1553922 * 2
def baseEnd_1553922 : Nat := 265969628531991502242883

theorem tailTrace_1553922 : CollatzResearch.WordTrace tailWord_1553922 prefixEnd_1553922 265969628531991502242883 := by
  unfold tailWord_1553922
  simp only [CollatzResearch.WordTrace]
  refine ⟨14169047869103364398508005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37784127650942305062688013 14169047869103364398508005)
  ·
    refine ⟨2656696475456880824720251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14169047869103364398508005 2656696475456880824720251)
    ·
      refine ⟨3985044713185321237080377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2656696475456880824720251 3985044713185321237080377)
      ·
        refine ⟨2988783534888990927810283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3985044713185321237080377 2988783534888990927810283)
        ·
          refine ⟨4483175302333486391715425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2988783534888990927810283 4483175302333486391715425)
          ·
            refine ⟨3362381476750114793786569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4483175302333486391715425 3362381476750114793786569)
            ·
              refine ⟨2521786107562586095339927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3362381476750114793786569 2521786107562586095339927)
              ·
                refine ⟨3782679161343879143009891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2521786107562586095339927 3782679161343879143009891)
                ·
                  refine ⟨5674018742015818714514837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3782679161343879143009891 5674018742015818714514837)
                  ·
                    refine ⟨265969628531991502242883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5674018742015818714514837 265969628531991502242883)
                    ·
                      rfl

theorem cell23_1553922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_1553922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553922 prefixEnd_1553922 := by exact prefixLift 1553922
  have htrace : WordTrace (prefixWord ++ tailWord_1553922) baseStart_1553922 baseEnd_1553922 := by
    simpa [prefixWord, tailWord_1553922, baseEnd_1553922] using wordTrace_append hprefix tailTrace_1553922
  have hstable : (prefixWord ++ tailWord_1553922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553922).length < 2 ^ (prefixWord ++ tailWord_1553922).sum := by decide
  have hdescent : baseEnd_1553922 < baseStart_1553922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553933 : List Nat := [1, 7, 1, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_1553933 : Nat := 118140960795 + 1553933 * 2 ^ 59
def prefixEnd_1553933 : Nat := 4983230072969 + 3 ^ 40 * 1553933 * 2
def baseEnd_1553933 : Nat := 797914533883173963691099

theorem tailTrace_1553933 : CollatzResearch.WordTrace tailWord_1553933 prefixEnd_1553933 797914533883173963691099 := by
  unfold tailWord_1553933
  simp only [CollatzResearch.WordTrace]
  refine ⟨56676592679373606472682453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37784395119582404315121635 56676592679373606472682453)
  ·
    refine ⟨1328357640922818901703495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 56676592679373606472682453 1328357640922818901703495)
    ·
      refine ⟨1992536461384228352555243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1328357640922818901703495 1992536461384228352555243)
      ·
        refine ⟨2988804692076342528832865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1992536461384228352555243 2988804692076342528832865)
        ·
          refine ⟨2241603519057256896624649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2988804692076342528832865 2241603519057256896624649)
          ·
            refine ⟨1681202639292942672468487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2241603519057256896624649 1681202639292942672468487)
            ·
              refine ⟨2521803958939414008702731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1681202639292942672468487 2521803958939414008702731)
              ·
                refine ⟨3782705938409121013054097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2521803958939414008702731 3782705938409121013054097)
                ·
                  refine ⟨2837029453806840759790573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3782705938409121013054097 2837029453806840759790573)
                  ·
                    refine ⟨1063886045177565284921465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2837029453806840759790573 1063886045177565284921465)
                    ·
                      refine ⟨797914533883173963691099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1063886045177565284921465 797914533883173963691099)
                      ·
                        rfl

theorem cell23_1553933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_1553933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553933 prefixEnd_1553933 := by exact prefixLift 1553933
  have htrace : WordTrace (prefixWord ++ tailWord_1553933) baseStart_1553933 baseEnd_1553933 := by
    simpa [prefixWord, tailWord_1553933, baseEnd_1553933] using wordTrace_append hprefix tailTrace_1553933
  have hstable : (prefixWord ++ tailWord_1553933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553933).length < 2 ^ (prefixWord ++ tailWord_1553933).sum := by decide
  have hdescent : baseEnd_1553933 < baseStart_1553933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553962 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_1553962 : Nat := 118140960795 + 1553962 * 2 ^ 59
def prefixEnd_1553962 : Nat := 4983230072969 + 3 ^ 40 * 1553962 * 2
def baseEnd_1553962 : Nat := 797929424822154350228465

theorem tailTrace_1553962 : CollatzResearch.WordTrace tailWord_1553962 prefixEnd_1553962 797929424822154350228465 := by
  unfold tailWord_1553962
  simp only [CollatzResearch.WordTrace]
  refine ⟨14169412599067136106372035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37785100264179029616992093 14169412599067136106372035)
  ·
    refine ⟨21254118898600704159558053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14169412599067136106372035 21254118898600704159558053)
    ·
      refine ⟨3985147293487632029917135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21254118898600704159558053 3985147293487632029917135)
      ·
        refine ⟨5977720940231448044875703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3985147293487632029917135 5977720940231448044875703)
        ·
          refine ⟨8966581410347172067313555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5977720940231448044875703 8966581410347172067313555)
          ·
            refine ⟨13449872115520758100970333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8966581410347172067313555 13449872115520758100970333)
            ·
              refine ⟨5043702043320284287863875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13449872115520758100970333 5043702043320284287863875)
              ·
                refine ⟨7565553064980426431795813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5043702043320284287863875 7565553064980426431795813)
                ·
                  refine ⟨1418541199683829955961715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7565553064980426431795813 1418541199683829955961715)
                  ·
                    refine ⟨2127811799525744933942573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1418541199683829955961715 2127811799525744933942573)
                    ·
                      refine ⟨797929424822154350228465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2127811799525744933942573 797929424822154350228465)
                      ·
                        rfl

theorem cell23_1553962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_1553962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553962 prefixEnd_1553962 := by exact prefixLift 1553962
  have htrace : WordTrace (prefixWord ++ tailWord_1553962) baseStart_1553962 baseEnd_1553962 := by
    simpa [prefixWord, tailWord_1553962, baseEnd_1553962] using wordTrace_append hprefix tailTrace_1553962
  have hstable : (prefixWord ++ tailWord_1553962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553962).length < 2 ^ (prefixWord ++ tailWord_1553962).sum := by decide
  have hdescent : baseEnd_1553962 < baseStart_1553962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553978 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 2, 6]
def baseStart_1553978 : Nat := 118140960795 + 1553978 * 2 ^ 59
def prefixEnd_1553978 : Nat := 4983230072969 + 3 ^ 40 * 1553978 * 2
def baseEnd_1553978 : Nat := 265979213504208762542797

theorem tailTrace_1553978 : CollatzResearch.WordTrace tailWord_1553978 prefixEnd_1553978 265979213504208762542797 := by
  unfold tailWord_1553978
  simp only [CollatzResearch.WordTrace]
  refine ⟨14169558491052644789517647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37785489309473719438713725 14169558491052644789517647)
  ·
    refine ⟨21254337736578967184276471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14169558491052644789517647 21254337736578967184276471)
    ·
      refine ⟨31881506604868450776414707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21254337736578967184276471 31881506604868450776414707)
      ·
        refine ⟨47822259907302676164622061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31881506604868450776414707 47822259907302676164622061)
        ·
          refine ⟨17933347465238503561733273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47822259907302676164622061 17933347465238503561733273)
          ·
            refine ⟨13450010598928877671299955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17933347465238503561733273 13450010598928877671299955)
            ·
              refine ⟨20175015898393316506949933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13450010598928877671299955 20175015898393316506949933)
              ·
                refine ⟨7565630961897493690106225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20175015898393316506949933 7565630961897493690106225)
                ·
                  refine ⟨5674223221423120267579669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7565630961897493690106225 5674223221423120267579669)
                  ·
                    refine ⟨265979213504208762542797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5674223221423120267579669 265979213504208762542797)
                    ·
                      rfl

theorem cell23_1553978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_1553978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1553978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1553978 prefixEnd_1553978 := by exact prefixLift 1553978
  have htrace : WordTrace (prefixWord ++ tailWord_1553978) baseStart_1553978 baseEnd_1553978 := by
    simpa [prefixWord, tailWord_1553978, baseEnd_1553978] using wordTrace_append hprefix tailTrace_1553978
  have hstable : (prefixWord ++ tailWord_1553978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553978).length < 2 ^ (prefixWord ++ tailWord_1553978).sum := by decide
  have hdescent : baseEnd_1553978 < baseStart_1553978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554025 : List Nat := [1, 2, 1, 1, 1, 4, 2, 6, 5]
def baseStart_1554025 : Nat := 118140960795 + 1554025 * 2 ^ 59
def prefixEnd_1554025 : Nat := 4983230072969 + 3 ^ 40 * 1554025 * 2
def baseEnd_1554025 : Nat := 88662419344820844860075

theorem tailTrace_1554025 : CollatzResearch.WordTrace tailWord_1554025 prefixEnd_1554025 88662419344820844860075 := by
  unfold tailWord_1554025
  simp only [CollatzResearch.WordTrace]
  refine ⟨56679948195040306185031529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37786632130026870790021019 56679948195040306185031529)
  ·
    refine ⟨42509961146280229638773647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56679948195040306185031529 42509961146280229638773647)
    ·
      refine ⟨63764941719420344458160471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42509961146280229638773647 63764941719420344458160471)
      ·
        refine ⟨95647412579130516687240707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63764941719420344458160471 95647412579130516687240707)
        ·
          refine ⟨143471118868695775030861061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95647412579130516687240707 143471118868695775030861061)
          ·
            refine ⟨26900834787880457818286449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143471118868695775030861061 26900834787880457818286449)
            ·
              refine ⟨20175626090910343363714837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26900834787880457818286449 20175626090910343363714837)
              ·
                refine ⟨945732473011422345174133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20175626090910343363714837 945732473011422345174133)
                ·
                  refine ⟨88662419344820844860075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 945732473011422345174133 88662419344820844860075)
                  ·
                    rfl

theorem cell23_1554025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 5].length) (baseStart_1554025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554025 prefixEnd_1554025 := by exact prefixLift 1554025
  have htrace : WordTrace (prefixWord ++ tailWord_1554025) baseStart_1554025 baseEnd_1554025 := by
    simpa [prefixWord, tailWord_1554025, baseEnd_1554025] using wordTrace_append hprefix tailTrace_1554025
  have hstable : (prefixWord ++ tailWord_1554025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554025).length < 2 ^ (prefixWord ++ tailWord_1554025).sum := by decide
  have hdescent : baseEnd_1554025 < baseStart_1554025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554048 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 7]
def baseStart_1554048 : Nat := 118140960795 + 1554048 * 2 ^ 59
def prefixEnd_1554048 : Nat := 4983230072969 + 3 ^ 40 * 1554048 * 2
def baseEnd_1554048 : Nat := 797973584158441013753069

theorem tailTrace_1554048 : CollatzResearch.WordTrace tailWord_1554048 prefixEnd_1554048 797973584158441013753069 := by
  unfold tailWord_1554048
  simp only [CollatzResearch.WordTrace]
  refine ⟨28340393536978490556559399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37787191382637987408745865 28340393536978490556559399)
  ·
    refine ⟨42510590305467735834839099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28340393536978490556559399 42510590305467735834839099)
    ·
      refine ⟨63765885458201603752258649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42510590305467735834839099 63765885458201603752258649)
      ·
        refine ⟨47824414093651202814193987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63765885458201603752258649 47824414093651202814193987)
        ·
          refine ⟨71736621140476804221290981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47824414093651202814193987 71736621140476804221290981)
          ·
            refine ⟨13450616463839400791492059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71736621140476804221290981 13450616463839400791492059)
            ·
              refine ⟨20175924695759101187238089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13450616463839400791492059 20175924695759101187238089)
              ·
                refine ⟨15131943521819325890428567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20175924695759101187238089 15131943521819325890428567)
                ·
                  refine ⟨22697915282728988835642851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15131943521819325890428567 22697915282728988835642851)
                  ·
                    refine ⟨34046872924093483253464277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22697915282728988835642851 34046872924093483253464277)
                    ·
                      refine ⟨797973584158441013753069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34046872924093483253464277 797973584158441013753069)
                      ·
                        rfl

theorem cell23_1554048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_1554048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554048 prefixEnd_1554048 := by exact prefixLift 1554048
  have htrace : WordTrace (prefixWord ++ tailWord_1554048) baseStart_1554048 baseEnd_1554048 := by
    simpa [prefixWord, tailWord_1554048, baseEnd_1554048] using wordTrace_append hprefix tailTrace_1554048
  have hstable : (prefixWord ++ tailWord_1554048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554048).length < 2 ^ (prefixWord ++ tailWord_1554048).sum := by decide
  have hdescent : baseEnd_1554048 < baseStart_1554048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554055 : List Nat := [1, 1, 4, 2, 1, 3, 1, 3, 2, 5]
def baseStart_1554055 : Nat := 118140960795 + 1554055 * 2 ^ 59
def prefixEnd_1554055 : Nat := 4983230072969 + 3 ^ 40 * 1554055 * 2
def baseEnd_1554055 : Nat := 265992392841007495455179

theorem tailTrace_1554055 : CollatzResearch.WordTrace tailWord_1554055 prefixEnd_1554055 265992392841007495455179 := by
  unfold tailWord_1554055
  simp only [CollatzResearch.WordTrace]
  refine ⟨56681042384931621308623619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37787361589954414205749079 56681042384931621308623619)
  ·
    refine ⟨85021563577397431962935429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56681042384931621308623619 85021563577397431962935429)
    ·
      refine ⟨15941543170762018493050393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85021563577397431962935429 15941543170762018493050393)
      ·
        refine ⟨11956157378071513869787795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15941543170762018493050393 11956157378071513869787795)
        ·
          refine ⟨17934236067107270804681693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11956157378071513869787795 17934236067107270804681693)
          ·
            refine ⟨6725338525165226551755635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17934236067107270804681693 6725338525165226551755635)
            ·
              refine ⟨10088007787747839827633453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6725338525165226551755635 10088007787747839827633453)
              ·
                refine ⟨3783002920405439935362545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10088007787747839827633453 3783002920405439935362545)
                ·
                  refine ⟨2837252190304079951521909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3783002920405439935362545 2837252190304079951521909)
                  ·
                    refine ⟨265992392841007495455179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2837252190304079951521909 265992392841007495455179)
                    ·
                      rfl

theorem cell23_1554055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_1554055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554055 prefixEnd_1554055 := by exact prefixLift 1554055
  have htrace : WordTrace (prefixWord ++ tailWord_1554055) baseStart_1554055 baseEnd_1554055 := by
    simpa [prefixWord, tailWord_1554055, baseEnd_1554055] using wordTrace_append hprefix tailTrace_1554055
  have hstable : (prefixWord ++ tailWord_1554055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554055).length < 2 ^ (prefixWord ++ tailWord_1554055).sum := by decide
  have hdescent : baseEnd_1554055 < baseStart_1554055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554076 : List Nat := [2, 2, 3, 2, 3, 2, 2, 2, 5]
def baseStart_1554076 : Nat := 118140960795 + 1554076 * 2 ^ 59
def prefixEnd_1554076 : Nat := 4983230072969 + 3 ^ 40 * 1554076 * 2
def baseEnd_1554076 : Nat := 88665329068529656022549

theorem tailTrace_1554076 : CollatzResearch.WordTrace tailWord_1554076 prefixEnd_1554076 88665329068529656022549 := by
  unfold tailWord_1554076
  simp only [CollatzResearch.WordTrace]
  refine ⟨28340904158927770947569041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37787872211903694596758721 28340904158927770947569041)
  ·
    refine ⟨21255678119195828210676781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28340904158927770947569041 21255678119195828210676781)
    ·
      refine ⟨7970879294698435579003793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21255678119195828210676781 7970879294698435579003793)
      ·
        refine ⟨5978159471023826684252845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7970879294698435579003793 5978159471023826684252845)
        ·
          refine ⟨2241809801633935006594817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5978159471023826684252845 2241809801633935006594817)
          ·
            refine ⟨1681357351225451254946113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2241809801633935006594817 1681357351225451254946113)
            ·
              refine ⟨1261018013419088441209585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1681357351225451254946113 1261018013419088441209585)
              ·
                refine ⟨945763510064316330907189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1261018013419088441209585 945763510064316330907189)
                ·
                  refine ⟨88665329068529656022549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 945763510064316330907189 88665329068529656022549)
                  ·
                    rfl

theorem cell23_1554076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 5].length) (baseStart_1554076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554076 prefixEnd_1554076 := by exact prefixLift 1554076
  have htrace : WordTrace (prefixWord ++ tailWord_1554076) baseStart_1554076 baseEnd_1554076 := by
    simpa [prefixWord, tailWord_1554076, baseEnd_1554076] using wordTrace_append hprefix tailTrace_1554076
  have hstable : (prefixWord ++ tailWord_1554076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554076).length < 2 ^ (prefixWord ++ tailWord_1554076).sum := by decide
  have hdescent : baseEnd_1554076 < baseStart_1554076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554095 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 3]
def baseStart_1554095 : Nat := 118140960795 + 1554095 * 2 ^ 59
def prefixEnd_1554095 : Nat := 4983230072969 + 3 ^ 40 * 1554095 * 2
def baseEnd_1554095 : Nat := 797997717749202329865353

theorem tailTrace_1554095 : CollatzResearch.WordTrace tailWord_1554095 prefixEnd_1554095 797997717749202329865353 := by
  unfold tailWord_1554095
  simp only [CollatzResearch.WordTrace]
  refine ⟨56682501304786708140079739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37788334203191138760053159 56682501304786708140079739)
  ·
    refine ⟨85023751957180062210119609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56682501304786708140079739 85023751957180062210119609)
    ·
      refine ⟨63767813967885046657589707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85023751957180062210119609 63767813967885046657589707)
      ·
        refine ⟨95651720951827569986384561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63767813967885046657589707 95651720951827569986384561)
        ·
          refine ⟨71738790713870677489788421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95651720951827569986384561 71738790713870677489788421)
          ·
            refine ⟨13451023258850752029335329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71738790713870677489788421 13451023258850752029335329)
            ·
              refine ⟨10088267444138064022001497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13451023258850752029335329 10088267444138064022001497)
              ·
                refine ⟨7566200583103548016501123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10088267444138064022001497 7566200583103548016501123)
                ·
                  refine ⟨11349300874655322024751685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7566200583103548016501123 11349300874655322024751685)
                  ·
                    refine ⟨2127993913997872879640941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11349300874655322024751685 2127993913997872879640941)
                    ·
                      refine ⟨797997717749202329865353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2127993913997872879640941 797997717749202329865353)
                      ·
                        rfl

theorem cell23_1554095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 3].length) (baseStart_1554095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554095 prefixEnd_1554095 := by exact prefixLift 1554095
  have htrace : WordTrace (prefixWord ++ tailWord_1554095) baseStart_1554095 baseEnd_1554095 := by
    simpa [prefixWord, tailWord_1554095, baseEnd_1554095] using wordTrace_append hprefix tailTrace_1554095
  have hstable : (prefixWord ++ tailWord_1554095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554095).length < 2 ^ (prefixWord ++ tailWord_1554095).sum := by decide
  have hdescent : baseEnd_1554095 < baseStart_1554095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554119 : List Nat := [1, 1, 4, 1, 1, 1, 6, 3, 1, 4]
def baseStart_1554119 : Nat := 118140960795 + 1554119 * 2 ^ 59
def prefixEnd_1554119 : Nat := 4983230072969 + 3 ^ 40 * 1554119 * 2
def baseEnd_1554119 : Nat := 266003347094970078655081

theorem tailTrace_1554119 : CollatzResearch.WordTrace tailWord_1554119 prefixEnd_1554119 266003347094970078655081 := by
  unfold tailWord_1554119
  simp only [CollatzResearch.WordTrace]
  refine ⟨56683376656699760238953411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37788917771133173492635607 56683376656699760238953411)
  ·
    refine ⟨85025064985049640358430117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56683376656699760238953411 85025064985049640358430117)
    ·
      refine ⟨15942199684696807567205647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85025064985049640358430117 15942199684696807567205647)
      ·
        refine ⟨23913299527045211350808471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15942199684696807567205647 23913299527045211350808471)
        ·
          refine ⟨35869949290567817026212707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23913299527045211350808471 35869949290567817026212707)
          ·
            refine ⟨53804923935851725539319061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35869949290567817026212707 53804923935851725539319061)
            ·
              refine ⟨2522105809493049634655581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53804923935851725539319061 2522105809493049634655581)
              ·
                refine ⟨945789678559893612995843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2522105809493049634655581 945789678559893612995843)
                ·
                  refine ⟨1418684517839840419493765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 945789678559893612995843 1418684517839840419493765)
                  ·
                    refine ⟨266003347094970078655081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1418684517839840419493765 266003347094970078655081)
                    ·
                      rfl

theorem cell23_1554119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_1554119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554119 prefixEnd_1554119 := by exact prefixLift 1554119
  have htrace : WordTrace (prefixWord ++ tailWord_1554119) baseStart_1554119 baseEnd_1554119 := by
    simpa [prefixWord, tailWord_1554119, baseEnd_1554119] using wordTrace_append hprefix tailTrace_1554119
  have hstable : (prefixWord ++ tailWord_1554119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554119).length < 2 ^ (prefixWord ++ tailWord_1554119).sum := by decide
  have hdescent : baseEnd_1554119 < baseStart_1554119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554132 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 8]
def baseStart_1554132 : Nat := 118140960795 + 1554132 * 2 ^ 59
def prefixEnd_1554132 : Nat := 4983230072969 + 3 ^ 40 * 1554132 * 2
def baseEnd_1554132 : Nat := 88668524059268742789187

theorem tailTrace_1554132 : CollatzResearch.WordTrace tailWord_1554132 prefixEnd_1554132 88668524059268742789187 := by
  unfold tailWord_1554132
  simp only [CollatzResearch.WordTrace]
  refine ⟨28341925402826331729588325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37789233870435108972784433 28341925402826331729588325)
  ·
    refine ⟨5314111013029937199297811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28341925402826331729588325 5314111013029937199297811)
    ·
      refine ⟨7971166519544905798946717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5314111013029937199297811 7971166519544905798946717)
      ·
        refine ⟨2989187444829339674605019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7971166519544905798946717 2989187444829339674605019)
        ·
          refine ⟨4483781167244009511907529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2989187444829339674605019 4483781167244009511907529)
          ·
            refine ⟨3362835875433007133930647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4483781167244009511907529 3362835875433007133930647)
            ·
              refine ⟨5044253813149510700895971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3362835875433007133930647 5044253813149510700895971)
              ·
                refine ⟨7566380719724266051343957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5044253813149510700895971 7566380719724266051343957)
                ·
                  refine ⟨88668524059268742789187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7566380719724266051343957 88668524059268742789187)
                  ·
                    rfl

theorem cell23_1554132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_1554132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554132 prefixEnd_1554132 := by exact prefixLift 1554132
  have htrace : WordTrace (prefixWord ++ tailWord_1554132) baseStart_1554132 baseEnd_1554132 := by
    simpa [prefixWord, tailWord_1554132, baseEnd_1554132] using wordTrace_append hprefix tailTrace_1554132
  have hstable : (prefixWord ++ tailWord_1554132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554132).length < 2 ^ (prefixWord ++ tailWord_1554132).sum := by decide
  have hdescent : baseEnd_1554132 < baseStart_1554132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554175 : List Nat := [1, 1, 2, 2, 1, 3, 2, 4, 1, 6]
def baseStart_1554175 : Nat := 118140960795 + 1554175 * 2 ^ 59
def prefixEnd_1554175 : Nat := 4983230072969 + 3 ^ 40 * 1554175 * 2
def baseEnd_1554175 : Nat := 266012932067187338954995

theorem tailTrace_1554175 : CollatzResearch.WordTrace tailWord_1554175 prefixEnd_1554175 266012932067187338954995 := by
  unfold tailWord_1554175
  simp only [CollatzResearch.WordTrace]
  refine ⟨56685419144496881802991979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37790279429664587868661319 56685419144496881802991979)
  ·
    refine ⟨85028128716745322704487969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56685419144496881802991979 85028128716745322704487969)
    ·
      refine ⟨63771096537558992028365977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85028128716745322704487969 63771096537558992028365977)
      ·
        refine ⟨47828322403169244021274483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63771096537558992028365977 47828322403169244021274483)
        ·
          refine ⟨71742483604753866031911725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47828322403169244021274483 71742483604753866031911725)
          ·
            refine ⟨26903431351782699761966897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71742483604753866031911725 26903431351782699761966897)
            ·
              refine ⟨20177573513837024821475173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26903431351782699761966897 20177573513837024821475173)
              ·
                refine ⟨3783295033844442154026595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20177573513837024821475173 3783295033844442154026595)
                ·
                  refine ⟨5674942550766663231039893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3783295033844442154026595 5674942550766663231039893)
                  ·
                    refine ⟨266012932067187338954995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5674942550766663231039893 266012932067187338954995)
                    ·
                      rfl

theorem cell23_1554175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 6].length) (baseStart_1554175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554175 prefixEnd_1554175 := by exact prefixLift 1554175
  have htrace : WordTrace (prefixWord ++ tailWord_1554175) baseStart_1554175 baseEnd_1554175 := by
    simpa [prefixWord, tailWord_1554175, baseEnd_1554175] using wordTrace_append hprefix tailTrace_1554175
  have hstable : (prefixWord ++ tailWord_1554175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554175).length < 2 ^ (prefixWord ++ tailWord_1554175).sum := by decide
  have hdescent : baseEnd_1554175 < baseStart_1554175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554195 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 4]
def baseStart_1554195 : Nat := 118140960795 + 1554195 * 2 ^ 59
def prefixEnd_1554195 : Nat := 4983230072969 + 3 ^ 40 * 1554195 * 2
def baseEnd_1554195 : Nat := 798049065814651938614893

theorem tailTrace_1554195 : CollatzResearch.WordTrace tailWord_1554195 prefixEnd_1554195 798049065814651938614893 := by
  unfold tailWord_1554195
  simp only [CollatzResearch.WordTrace]
  refine ⟨56686148604424425218720039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37790765736282950145813359 56686148604424425218720039)
  ·
    refine ⟨85029222906636637828080059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56686148604424425218720039 85029222906636637828080059)
    ·
      refine ⟨127543834359954956742120089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85029222906636637828080059 127543834359954956742120089)
      ·
        refine ⟨95657875769966217556590067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127543834359954956742120089 95657875769966217556590067)
        ·
          refine ⟨143486813654949326334885101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95657875769966217556590067 143486813654949326334885101)
          ·
            refine ⟨53807555120605997375581913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143486813654949326334885101 53807555120605997375581913)
            ·
              refine ⟨40355666340454498031686435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53807555120605997375581913 40355666340454498031686435)
              ·
                refine ⟨60533499510681747047529653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40355666340454498031686435 60533499510681747047529653)
                ·
                  refine ⟨5675015579126413785705905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60533499510681747047529653 5675015579126413785705905)
                  ·
                    refine ⟨4256261684344810339279429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5675015579126413785705905 4256261684344810339279429)
                    ·
                      refine ⟨798049065814651938614893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4256261684344810339279429 798049065814651938614893)
                      ·
                        rfl

theorem cell23_1554195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_1554195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554195 prefixEnd_1554195 := by exact prefixLift 1554195
  have htrace : WordTrace (prefixWord ++ tailWord_1554195) baseStart_1554195 baseEnd_1554195 := by
    simpa [prefixWord, tailWord_1554195, baseEnd_1554195] using wordTrace_append hprefix tailTrace_1554195
  have hstable : (prefixWord ++ tailWord_1554195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554195).length < 2 ^ (prefixWord ++ tailWord_1554195).sum := by decide
  have hdescent : baseEnd_1554195 < baseStart_1554195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554202 : List Nat := [3, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5]
def baseStart_1554202 : Nat := 118140960795 + 1554202 * 2 ^ 59
def prefixEnd_1554202 : Nat := 4983230072969 + 3 ^ 40 * 1554202 * 2
def baseEnd_1554202 : Nat := 798052660179233411227361

theorem tailTrace_1554202 : CollatzResearch.WordTrace tailWord_1554202 prefixEnd_1554202 798052660179233411227361 := by
  unfold tailWord_1554202
  simp only [CollatzResearch.WordTrace]
  refine ⟨14171600978849766353556215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37790935943599376942816573 14171600978849766353556215)
  ·
    refine ⟨21257401468274649530334323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14171600978849766353556215 21257401468274649530334323)
    ·
      refine ⟨31886102202411974295501485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21257401468274649530334323 31886102202411974295501485)
      ·
        refine ⟨11957288325904490360813057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31886102202411974295501485 11957288325904490360813057)
        ·
          refine ⟨8967966244428367770609793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11957288325904490360813057 8967966244428367770609793)
          ·
            refine ⟨6725974683321275827957345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8967966244428367770609793 6725974683321275827957345)
            ·
              refine ⟨5044481012490956870968009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6725974683321275827957345 5044481012490956870968009)
              ·
                refine ⟨3783360759368217653226007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5044481012490956870968009 3783360759368217653226007)
                ·
                  refine ⟨5675041139052326479839011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3783360759368217653226007 5675041139052326479839011)
                  ·
                    refine ⟨8512561708578489719758517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5675041139052326479839011 8512561708578489719758517)
                    ·
                      refine ⟨798052660179233411227361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8512561708578489719758517 798052660179233411227361)
                      ·
                        rfl

theorem cell23_1554202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_1554202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554202 prefixEnd_1554202 := by exact prefixLift 1554202
  have htrace : WordTrace (prefixWord ++ tailWord_1554202) baseStart_1554202 baseEnd_1554202 := by
    simpa [prefixWord, tailWord_1554202, baseEnd_1554202] using wordTrace_append hprefix tailTrace_1554202
  have hstable : (prefixWord ++ tailWord_1554202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554202).length < 2 ^ (prefixWord ++ tailWord_1554202).sum := by decide
  have hdescent : baseEnd_1554202 < baseStart_1554202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554209 : List Nat := [1, 2, 3, 2, 1, 4, 1, 3, 2, 4]
def baseStart_1554209 : Nat := 118140960795 + 1554209 * 2 ^ 59
def prefixEnd_1554209 : Nat := 4983230072969 + 3 ^ 40 * 1554209 * 2
def baseEnd_1554209 : Nat := 266018751514604961279943

theorem tailTrace_1554209 : CollatzResearch.WordTrace tailWord_1554209 prefixEnd_1554209 266018751514604961279943 := by
  unfold tailWord_1554209
  simp only [CollatzResearch.WordTrace]
  refine ⟨56686659226373705609729681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37791106150915803739819787 56686659226373705609729681)
  ·
    refine ⟨42514994419780279207297261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56686659226373705609729681 42514994419780279207297261)
    ·
      refine ⟨15943122907417604702736473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42514994419780279207297261 15943122907417604702736473)
      ·
        refine ⟨11957342180563203527052355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15943122907417604702736473 11957342180563203527052355)
        ·
          refine ⟨17936013270844805290578533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11957342180563203527052355 17936013270844805290578533)
          ·
            refine ⟨3363002488283400991983475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17936013270844805290578533 3363002488283400991983475)
            ·
              refine ⟨5044503732425101487975213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3363002488283400991983475 5044503732425101487975213)
              ·
                refine ⟨1891688899659413057990705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5044503732425101487975213 1891688899659413057990705)
                ·
                  refine ⟨1418766674744559793493029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1891688899659413057990705 1418766674744559793493029)
                  ·
                    refine ⟨266018751514604961279943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1418766674744559793493029 266018751514604961279943)
                    ·
                      rfl

theorem cell23_1554209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_1554209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554209 prefixEnd_1554209 := by exact prefixLift 1554209
  have htrace : WordTrace (prefixWord ++ tailWord_1554209) baseStart_1554209 baseEnd_1554209 := by
    simpa [prefixWord, tailWord_1554209, baseEnd_1554209] using wordTrace_append hprefix tailTrace_1554209
  have hstable : (prefixWord ++ tailWord_1554209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554209).length < 2 ^ (prefixWord ++ tailWord_1554209).sum := by decide
  have hdescent : baseEnd_1554209 < baseStart_1554209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554212 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_1554212 : Nat := 118140960795 + 1554212 * 2 ^ 59
def prefixEnd_1554212 : Nat := 4983230072969 + 3 ^ 40 * 1554212 * 2
def baseEnd_1554212 : Nat := 798057794985778372102315

theorem tailTrace_1554212 : CollatzResearch.WordTrace tailWord_1554212 prefixEnd_1554212 798057794985778372102315 := by
  unfold tailWord_1554212
  simp only [CollatzResearch.WordTrace]
  refine ⟨28343384322681418561044445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37791179096908558081392593 28343384322681418561044445)
  ·
    refine ⟨10628769121005531960391667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28343384322681418561044445 10628769121005531960391667)
    ·
      refine ⟨15943153681508297940587501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10628769121005531960391667 15943153681508297940587501)
      ·
        refine ⟨5978682630565611727720313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15943153681508297940587501 5978682630565611727720313)
        ·
          refine ⟨4484011972924208795790235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5978682630565611727720313 4484011972924208795790235)
          ·
            refine ⟨6726017959386313193685353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4484011972924208795790235 6726017959386313193685353)
            ·
              refine ⟨5044513469539734895264015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6726017959386313193685353 5044513469539734895264015)
              ·
                refine ⟨7566770204309602342896023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5044513469539734895264015 7566770204309602342896023)
                ·
                  refine ⟨11350155306464403514344035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7566770204309602342896023 11350155306464403514344035)
                  ·
                    refine ⟨17025232959696605271516053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11350155306464403514344035 17025232959696605271516053)
                    ·
                      refine ⟨798057794985778372102315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17025232959696605271516053 798057794985778372102315)
                      ·
                        rfl

theorem cell23_1554212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_1554212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554212 prefixEnd_1554212 := by exact prefixLift 1554212
  have htrace : WordTrace (prefixWord ++ tailWord_1554212) baseStart_1554212 baseEnd_1554212 := by
    simpa [prefixWord, tailWord_1554212, baseEnd_1554212] using wordTrace_append hprefix tailTrace_1554212
  have hstable : (prefixWord ++ tailWord_1554212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554212).length < 2 ^ (prefixWord ++ tailWord_1554212).sum := by decide
  have hdescent : baseEnd_1554212 < baseStart_1554212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554216 : List Nat := [2, 1, 5, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_1554216 : Nat := 118140960795 + 1554216 * 2 ^ 59
def prefixEnd_1554216 : Nat := 4983230072969 + 3 ^ 40 * 1554216 * 2
def baseEnd_1554216 : Nat := 798059848908396356452297

theorem tailTrace_1554216 : CollatzResearch.WordTrace tailWord_1554216 prefixEnd_1554216 798059848908396356452297 := by
  unfold tailWord_1554216
  simp only [CollatzResearch.WordTrace]
  refine ⟨28343457268674172902617251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37791276358232230536823001 28343457268674172902617251)
  ·
    refine ⟨42515185903011259353925877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28343457268674172902617251 42515185903011259353925877)
    ·
      refine ⟨3985798678407305564430551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42515185903011259353925877 3985798678407305564430551)
      ·
        refine ⟨5978698017610958346645827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3985798678407305564430551 5978698017610958346645827)
        ·
          refine ⟨8968047026416437519968741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5978698017610958346645827 8968047026416437519968741)
          ·
            refine ⟨1681508817453082034994139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8968047026416437519968741 1681508817453082034994139)
            ·
              refine ⟨2522263226179623052491209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1681508817453082034994139 2522263226179623052491209)
              ·
                refine ⟨1891697419634717289368407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2522263226179623052491209 1891697419634717289368407)
                ·
                  refine ⟨2837546129452075934052611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1891697419634717289368407 2837546129452075934052611)
                  ·
                    refine ⟨4256319194178113901078917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2837546129452075934052611 4256319194178113901078917)
                    ·
                      refine ⟨798059848908396356452297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4256319194178113901078917 798059848908396356452297)
                      ·
                        rfl

theorem cell23_1554216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_1554216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554216 prefixEnd_1554216 := by exact prefixLift 1554216
  have htrace : WordTrace (prefixWord ++ tailWord_1554216) baseStart_1554216 baseEnd_1554216 := by
    simpa [prefixWord, tailWord_1554216, baseEnd_1554216] using wordTrace_append hprefix tailTrace_1554216
  have hstable : (prefixWord ++ tailWord_1554216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554216).length < 2 ^ (prefixWord ++ tailWord_1554216).sum := by decide
  have hdescent : baseEnd_1554216 < baseStart_1554216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554229 : List Nat := [1, 3, 3, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_1554229 : Nat := 118140960795 + 1554229 * 2 ^ 59
def prefixEnd_1554229 : Nat := 4983230072969 + 3 ^ 40 * 1554229 * 2
def baseEnd_1554229 : Nat := 798066524156904805589737

theorem tailTrace_1554229 : CollatzResearch.WordTrace tailWord_1554229 prefixEnd_1554229 798066524156904805589737 := by
  unfold tailWord_1554229
  simp only [CollatzResearch.WordTrace]
  refine ⟨56687388686301249025457741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37791592457534166016971827 56687388686301249025457741)
  ·
    refine ⟨21257770757362968384546653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56687388686301249025457741 21257770757362968384546653)
    ·
      refine ⟨7971664034011113144204995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21257770757362968384546653 7971664034011113144204995)
      ·
        refine ⟨11957496051016669716307493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7971664034011113144204995 11957496051016669716307493)
        ·
          refine ⟨2242030509565625571807655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11957496051016669716307493 2242030509565625571807655)
          ·
            refine ⟨3363045764348438357711483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2242030509565625571807655 3363045764348438357711483)
            ·
              refine ⟨5044568646522657536567225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3363045764348438357711483 5044568646522657536567225)
              ·
                refine ⟨3783426484891993152425419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5044568646522657536567225 3783426484891993152425419)
                ·
                  refine ⟨5675139727337989728638129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3783426484891993152425419 5675139727337989728638129)
                  ·
                    refine ⟨4256354795503492296478597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5675139727337989728638129 4256354795503492296478597)
                    ·
                      refine ⟨798066524156904805589737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4256354795503492296478597 798066524156904805589737)
                      ·
                        rfl

theorem cell23_1554229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_1554229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554229 prefixEnd_1554229 := by exact prefixLift 1554229
  have htrace : WordTrace (prefixWord ++ tailWord_1554229) baseStart_1554229 baseEnd_1554229 := by
    simpa [prefixWord, tailWord_1554229, baseEnd_1554229] using wordTrace_append hprefix tailTrace_1554229
  have hstable : (prefixWord ++ tailWord_1554229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554229).length < 2 ^ (prefixWord ++ tailWord_1554229).sum := by decide
  have hdescent : baseEnd_1554229 < baseStart_1554229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554232 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 3, 3, 3]
def baseStart_1554232 : Nat := 118140960795 + 1554232 * 2 ^ 59
def prefixEnd_1554232 : Nat := 4983230072969 + 3 ^ 40 * 1554232 * 2
def baseEnd_1554232 : Nat := 798068064598868293852223

theorem tailTrace_1554232 : CollatzResearch.WordTrace tailWord_1554232 prefixEnd_1554232 798068064598868293852223 := by
  unfold tailWord_1554232
  simp only [CollatzResearch.WordTrace]
  refine ⟨28343749052645190268908475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37791665403526920358544633 28343749052645190268908475)
  ·
    refine ⟨42515623578967785403362713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28343749052645190268908475 42515623578967785403362713)
    ·
      refine ⟨31886717684225839052522035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42515623578967785403362713 31886717684225839052522035)
      ·
        refine ⟨47830076526338758578783053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31886717684225839052522035 47830076526338758578783053)
        ·
          refine ⟨17936278697377034467043645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47830076526338758578783053 17936278697377034467043645)
          ·
            refine ⟨6726104511516387925141367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17936278697377034467043645 6726104511516387925141367)
            ·
              refine ⟨10089156767274581887712051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6726104511516387925141367 10089156767274581887712051)
              ·
                refine ⟨15133735150911872831568077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10089156767274581887712051 15133735150911872831568077)
                ·
                  refine ⟨5675150681591952311838029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15133735150911872831568077 5675150681591952311838029)
                  ·
                    refine ⟨2128181505596982116939261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5675150681591952311838029 2128181505596982116939261)
                    ·
                      refine ⟨798068064598868293852223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2128181505596982116939261 798068064598868293852223)
                      ·
                        rfl

theorem cell23_1554232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_1554232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554232 prefixEnd_1554232 := by exact prefixLift 1554232
  have htrace : WordTrace (prefixWord ++ tailWord_1554232) baseStart_1554232 baseEnd_1554232 := by
    simpa [prefixWord, tailWord_1554232, baseEnd_1554232] using wordTrace_append hprefix tailTrace_1554232
  have hstable : (prefixWord ++ tailWord_1554232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554232).length < 2 ^ (prefixWord ++ tailWord_1554232).sum := by decide
  have hdescent : baseEnd_1554232 < baseStart_1554232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554233 : List Nat := [1, 2, 1, 7, 1, 1, 3, 1, 1, 1, 4]
def baseStart_1554233 : Nat := 118140960795 + 1554233 * 2 ^ 59
def prefixEnd_1554233 : Nat := 4983230072969 + 3 ^ 40 * 1554233 * 2
def baseEnd_1554233 : Nat := 798068578079522789939719

theorem tailTrace_1554233 : CollatzResearch.WordTrace tailWord_1554233 prefixEnd_1554233 798068578079522789939719 := by
  unfold tailWord_1554233
  simp only [CollatzResearch.WordTrace]
  refine ⟨56687534578286757708603353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37791689718857838472402235 56687534578286757708603353)
  ·
    refine ⟨42515650933715068281452515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56687534578286757708603353 42515650933715068281452515)
    ·
      refine ⟨63773476400572602422178773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42515650933715068281452515 63773476400572602422178773)
      ·
        refine ⟨1494690853138420369269815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 63773476400572602422178773 1494690853138420369269815)
        ·
          refine ⟨2242036279707630553904723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1494690853138420369269815 2242036279707630553904723)
          ·
            refine ⟨3363054419561445830857085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2242036279707630553904723 3363054419561445830857085)
            ·
              refine ⟨1261145407335542186571407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3363054419561445830857085 1261145407335542186571407)
              ·
                refine ⟨1891718111003313279857111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261145407335542186571407 1891718111003313279857111)
                ·
                  refine ⟨2837577166504969919785667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1891718111003313279857111 2837577166504969919785667)
                  ·
                    refine ⟨4256365749757454879678501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2837577166504969919785667 4256365749757454879678501)
                    ·
                      refine ⟨798068578079522789939719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4256365749757454879678501 798068578079522789939719)
                      ·
                        rfl

theorem cell23_1554233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_1554233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554233 prefixEnd_1554233 := by exact prefixLift 1554233
  have htrace : WordTrace (prefixWord ++ tailWord_1554233) baseStart_1554233 baseEnd_1554233 := by
    simpa [prefixWord, tailWord_1554233, baseEnd_1554233] using wordTrace_append hprefix tailTrace_1554233
  have hstable : (prefixWord ++ tailWord_1554233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554233).length < 2 ^ (prefixWord ++ tailWord_1554233).sum := by decide
  have hdescent : baseEnd_1554233 < baseStart_1554233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554289 : List Nat := [1, 2, 2, 2, 1, 3, 1, 4, 1, 4, 2]
def baseStart_1554289 : Nat := 118140960795 + 1554289 * 2 ^ 59
def prefixEnd_1554289 : Nat := 4983230072969 + 3 ^ 40 * 1554289 * 2
def baseEnd_1554289 : Nat := 798097332996174570839461

theorem tailTrace_1554289 : CollatzResearch.WordTrace tailWord_1554289 prefixEnd_1554289 798097332996174570839461 := by
  unfold tailWord_1554289
  simp only [CollatzResearch.WordTrace]
  refine ⟨56689577066083879272641921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37793051377389252848427947 56689577066083879272641921)
  ·
    refine ⟨42517182799562909454481441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56689577066083879272641921 42517182799562909454481441)
    ·
      refine ⟨31887887099672182090861081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42517182799562909454481441 31887887099672182090861081)
      ·
        refine ⟨23915915324754136568145811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31887887099672182090861081 23915915324754136568145811)
        ·
          refine ⟨35873872987131204852218717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23915915324754136568145811 35873872987131204852218717)
          ·
            refine ⟨13452702370174201819582019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35873872987131204852218717 13452702370174201819582019)
            ·
              refine ⟨20179053555261302729373029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13452702370174201819582019 20179053555261302729373029)
              ·
                refine ⟨3783572541611494261757443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20179053555261302729373029 3783572541611494261757443)
                ·
                  refine ⟨5675358812417241392636165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3783572541611494261757443 5675358812417241392636165)
                  ·
                    refine ⟨1064129777328232761119281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5675358812417241392636165 1064129777328232761119281)
                    ·
                      refine ⟨798097332996174570839461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1064129777328232761119281 798097332996174570839461)
                      ·
                        rfl

theorem cell23_1554289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_1554289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554289 prefixEnd_1554289 := by exact prefixLift 1554289
  have htrace : WordTrace (prefixWord ++ tailWord_1554289) baseStart_1554289 baseEnd_1554289 := by
    simpa [prefixWord, tailWord_1554289, baseEnd_1554289] using wordTrace_append hprefix tailTrace_1554289
  have hstable : (prefixWord ++ tailWord_1554289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554289).length < 2 ^ (prefixWord ++ tailWord_1554289).sum := by decide
  have hdescent : baseEnd_1554289 < baseStart_1554289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554362 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4]
def baseStart_1554362 : Nat := 118140960795 + 1554362 * 2 ^ 59
def prefixEnd_1554362 : Nat := 4983230072969 + 3 ^ 40 * 1554362 * 2
def baseEnd_1554362 : Nat := 798134817083952785226625

theorem tailTrace_1554362 : CollatzResearch.WordTrace tailWord_1554362 prefixEnd_1554362 798134817083952785226625 := by
  unfold tailWord_1554362
  simp only [CollatzResearch.WordTrace]
  refine ⟨14173059898704853185012335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37794826396546275160032893 14173059898704853185012335)
  ·
    refine ⟨21259589848057279777518503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14173059898704853185012335 21259589848057279777518503)
    ·
      refine ⟨31889384772085919666277755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21259589848057279777518503 31889384772085919666277755)
      ·
        refine ⟨47834077158128879499416633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31889384772085919666277755 47834077158128879499416633)
        ·
          refine ⟨35875557868596659624562475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47834077158128879499416633 35875557868596659624562475)
          ·
            refine ⟨53813336802894989436843713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35875557868596659624562475 53813336802894989436843713)
            ·
              refine ⟨40360002602171242077632785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53813336802894989436843713 40360002602171242077632785)
              ·
                refine ⟨30270001951628431558224589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40360002602171242077632785 30270001951628431558224589)
                ·
                  refine ⟨11351250731860661834334221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30270001951628431558224589 11351250731860661834334221)
                  ·
                    refine ⟨4256719024447748187875333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11351250731860661834334221 4256719024447748187875333)
                    ·
                      refine ⟨798134817083952785226625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4256719024447748187875333 798134817083952785226625)
                      ·
                        rfl

theorem cell23_1554362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_1554362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554362 prefixEnd_1554362 := by exact prefixLift 1554362
  have htrace : WordTrace (prefixWord ++ tailWord_1554362) baseStart_1554362 baseEnd_1554362 := by
    simpa [prefixWord, tailWord_1554362, baseEnd_1554362] using wordTrace_append hprefix tailTrace_1554362
  have hstable : (prefixWord ++ tailWord_1554362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554362).length < 2 ^ (prefixWord ++ tailWord_1554362).sum := by decide
  have hdescent : baseEnd_1554362 < baseStart_1554362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554379 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 1, 6, 2]
def baseStart_1554379 : Nat := 118140960795 + 1554379 * 2 ^ 59
def prefixEnd_1554379 : Nat := 4983230072969 + 3 ^ 40 * 1554379 * 2
def baseEnd_1554379 : Nat := 798143546255079218714047

theorem tailTrace_1554379 : CollatzResearch.WordTrace tailWord_1554379 prefixEnd_1554379 798143546255079218714047 := by
  unfold tailWord_1554379
  simp only [CollatzResearch.WordTrace]
  refine ⟨56692859635757824643418191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37795239757171883095612127 56692859635757824643418191)
  ·
    refine ⟨85039289453636736965127287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56692859635757824643418191 85039289453636736965127287)
    ·
      refine ⟨127558934180455105447690931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85039289453636736965127287 127558934180455105447690931)
      ·
        refine ⟨191338401270682658171536397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127558934180455105447690931 191338401270682658171536397)
        ·
          refine ⟨71751900476505996814326149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191338401270682658171536397 71751900476505996814326149)
          ·
            refine ⟨13453481339344874402686153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71751900476505996814326149 13453481339344874402686153)
            ·
              refine ⟨10090111004508655802014615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13453481339344874402686153 10090111004508655802014615)
              ·
                refine ⟨15135166506762983703021923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10090111004508655802014615 15135166506762983703021923)
                ·
                  refine ⟨22702749760144475554532885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15135166506762983703021923 22702749760144475554532885)
                  ·
                    refine ⟨1064191395006772291618729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22702749760144475554532885 1064191395006772291618729)
                    ·
                      refine ⟨798143546255079218714047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1064191395006772291618729 798143546255079218714047)
                      ·
                        rfl

theorem cell23_1554379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 6, 2].length) (baseStart_1554379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554379 prefixEnd_1554379 := by exact prefixLift 1554379
  have htrace : WordTrace (prefixWord ++ tailWord_1554379) baseStart_1554379 baseEnd_1554379 := by
    simpa [prefixWord, tailWord_1554379, baseEnd_1554379] using wordTrace_append hprefix tailTrace_1554379
  have hstable : (prefixWord ++ tailWord_1554379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554379).length < 2 ^ (prefixWord ++ tailWord_1554379).sum := by decide
  have hdescent : baseEnd_1554379 < baseStart_1554379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554456 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 1, 5, 2]
def baseStart_1554456 : Nat := 118140960795 + 1554456 * 2 ^ 59
def prefixEnd_1554456 : Nat := 4983230072969 + 3 ^ 40 * 1554456 * 2
def baseEnd_1554456 : Nat := 798183084265475417451193

theorem tailTrace_1554456 : CollatzResearch.WordTrace tailWord_1554456 prefixEnd_1554456 798183084265475417451193 := by
  unfold tailWord_1554456
  simp only [CollatzResearch.WordTrace]
  refine ⟨28347834028239433396985611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37797112037652577862647481 28347834028239433396985611)
  ·
    refine ⟨42521751042359150095478417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28347834028239433396985611 42521751042359150095478417)
    ·
      refine ⟨31891313281769362571608813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42521751042359150095478417 31891313281769362571608813)
      ·
        refine ⟨11959242480663510964353305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31891313281769362571608813 11959242480663510964353305)
        ·
          refine ⟨8969431860497633223264979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11959242480663510964353305 8969431860497633223264979)
          ·
            refine ⟨13454147790746449834897469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8969431860497633223264979 13454147790746449834897469)
            ·
              refine ⟨5045305421529918688086551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13454147790746449834897469 5045305421529918688086551)
              ·
                refine ⟨7567958132294878032129827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5045305421529918688086551 7567958132294878032129827)
                ·
                  refine ⟨11351937198442317048194741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7567958132294878032129827 11351937198442317048194741)
                  ·
                    refine ⟨1064244112353967223268257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11351937198442317048194741 1064244112353967223268257)
                    ·
                      refine ⟨798183084265475417451193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1064244112353967223268257 798183084265475417451193)
                      ·
                        rfl

theorem cell23_1554456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_1554456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554456 prefixEnd_1554456 := by exact prefixLift 1554456
  have htrace : WordTrace (prefixWord ++ tailWord_1554456) baseStart_1554456 baseEnd_1554456 := by
    simpa [prefixWord, tailWord_1554456, baseEnd_1554456] using wordTrace_append hprefix tailTrace_1554456
  have hstable : (prefixWord ++ tailWord_1554456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554456).length < 2 ^ (prefixWord ++ tailWord_1554456).sum := by decide
  have hdescent : baseEnd_1554456 < baseStart_1554456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554466 : List Nat := [3, 3, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_1554466 : Nat := 118140960795 + 1554466 * 2 ^ 59
def prefixEnd_1554466 : Nat := 4983230072969 + 3 ^ 40 * 1554466 * 2
def baseEnd_1554466 : Nat := 266062739690673459442049

theorem tailTrace_1554466 : CollatzResearch.WordTrace tailWord_1554466 prefixEnd_1554466 266062739690673459442049 := by
  unfold tailWord_1554466
  simp only [CollatzResearch.WordTrace]
  refine ⟨14174008196610659625458813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37797355190961759001223501 14174008196610659625458813)
  ·
    refine ⟨5315253073728997359547055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14174008196610659625458813 5315253073728997359547055)
    ·
      refine ⟨7972879610593496039320583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5315253073728997359547055 7972879610593496039320583)
      ·
        refine ⟨11959319415890244058980875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7972879610593496039320583 11959319415890244058980875)
        ·
          refine ⟨17938979123835366088471313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11959319415890244058980875 17938979123835366088471313)
          ·
            refine ⟨13454234342876524566353485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17938979123835366088471313 13454234342876524566353485)
            ·
              refine ⟨5045337878578696712382557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13454234342876524566353485 5045337878578696712382557)
              ·
                refine ⟨1892001704467011267143459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5045337878578696712382557 1892001704467011267143459)
                ·
                  refine ⟨2838002556700516900715189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1892001704467011267143459 2838002556700516900715189)
                  ·
                    refine ⟨266062739690673459442049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2838002556700516900715189 266062739690673459442049)
                    ·
                      rfl

theorem cell23_1554466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_1554466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554466 prefixEnd_1554466 := by exact prefixLift 1554466
  have htrace : WordTrace (prefixWord ++ tailWord_1554466) baseStart_1554466 baseEnd_1554466 := by
    simpa [prefixWord, tailWord_1554466, baseEnd_1554466] using wordTrace_append hprefix tailTrace_1554466
  have hstable : (prefixWord ++ tailWord_1554466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554466).length < 2 ^ (prefixWord ++ tailWord_1554466).sum := by decide
  have hdescent : baseEnd_1554466 < baseStart_1554466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554496 : List Nat := [2, 1, 1, 2, 2, 6, 1, 1, 1, 6]
def baseStart_1554496 : Nat := 118140960795 + 1554496 * 2 ^ 59
def prefixEnd_1554496 : Nat := 4983230072969 + 3 ^ 40 * 1554496 * 2
def baseEnd_1554496 : Nat := 266067874497218420317003

theorem tailTrace_1554496 : CollatzResearch.WordTrace tailWord_1554496 prefixEnd_1554496 266067874497218420317003 := by
  unfold tailWord_1554496
  simp only [CollatzResearch.WordTrace]
  refine ⟨28348563488166976812713671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37798084650889302416951561 28348563488166976812713671)
  ·
    refine ⟨42522845232250465219070507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28348563488166976812713671 42522845232250465219070507)
    ·
      refine ⟨63784267848375697828605761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42522845232250465219070507 63784267848375697828605761)
      ·
        refine ⟨47838200886281773371454321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63784267848375697828605761 47838200886281773371454321)
        ·
          refine ⟨35878650664711330028590741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47838200886281773371454321 35878650664711330028590741)
          ·
            refine ⟨1681811749908343595090191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35878650664711330028590741 1681811749908343595090191)
            ·
              refine ⟨2522717624862515392635287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1681811749908343595090191 2522717624862515392635287)
              ·
                refine ⟨3784076437293773088952931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2522717624862515392635287 3784076437293773088952931)
                ·
                  refine ⟨5676114655940659633429397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3784076437293773088952931 5676114655940659633429397)
                  ·
                    refine ⟨266067874497218420317003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5676114655940659633429397 266067874497218420317003)
                    ·
                      rfl

theorem cell23_1554496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 1, 6].length) (baseStart_1554496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554496 prefixEnd_1554496 := by exact prefixLift 1554496
  have htrace : WordTrace (prefixWord ++ tailWord_1554496) baseStart_1554496 baseEnd_1554496 := by
    simpa [prefixWord, tailWord_1554496, baseEnd_1554496] using wordTrace_append hprefix tailTrace_1554496
  have hstable : (prefixWord ++ tailWord_1554496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554496).length < 2 ^ (prefixWord ++ tailWord_1554496).sum := by decide
  have hdescent : baseEnd_1554496 < baseStart_1554496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554499 : List Nat := [1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 4]
def baseStart_1554499 : Nat := 118140960795 + 1554499 * 2 ^ 59
def prefixEnd_1554499 : Nat := 4983230072969 + 3 ^ 40 * 1554499 * 2
def baseEnd_1554499 : Nat := 798205163933618749213495

theorem tailTrace_1554499 : CollatzResearch.WordTrace tailWord_1554499 prefixEnd_1554499 798205163933618749213495 := by
  unfold tailWord_1554499
  simp only [CollatzResearch.WordTrace]
  refine ⟨56697236395323085137786551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37798157596882056758524367 56697236395323085137786551)
  ·
    refine ⟨85045854592984627706679827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56697236395323085137786551 85045854592984627706679827)
    ·
      refine ⟨127568781889476941560019741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85045854592984627706679827 127568781889476941560019741)
      ·
        refine ⟨47838293208553853085007403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127568781889476941560019741 47838293208553853085007403)
        ·
          refine ⟨71757439812830779627511105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47838293208553853085007403 71757439812830779627511105)
          ·
            refine ⟨53818079859623084720633329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71757439812830779627511105 53818079859623084720633329)
            ·
              refine ⟨40363559894717313540474997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53818079859623084720633329 40363559894717313540474997)
              ·
                refine ⟨3784083740129748144419531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40363559894717313540474997 3784083740129748144419531)
                ·
                  refine ⟨5676125610194622216629297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3784083740129748144419531 5676125610194622216629297)
                  ·
                    refine ⟨4257094207645966662471973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5676125610194622216629297 4257094207645966662471973)
                    ·
                      refine ⟨798205163933618749213495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4257094207645966662471973 798205163933618749213495)
                      ·
                        rfl

theorem cell23_1554499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_1554499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554499 prefixEnd_1554499 := by exact prefixLift 1554499
  have htrace : WordTrace (prefixWord ++ tailWord_1554499) baseStart_1554499 baseEnd_1554499 := by
    simpa [prefixWord, tailWord_1554499, baseEnd_1554499] using wordTrace_append hprefix tailTrace_1554499
  have hstable : (prefixWord ++ tailWord_1554499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554499).length < 2 ^ (prefixWord ++ tailWord_1554499).sum := by decide
  have hdescent : baseEnd_1554499 < baseStart_1554499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554503 : List Nat := [1, 1, 4, 1, 3, 1, 1, 4, 3, 2, 2]
def baseStart_1554503 : Nat := 118140960795 + 1554503 * 2 ^ 59
def prefixEnd_1554503 : Nat := 4983230072969 + 3 ^ 40 * 1554503 * 2
def baseEnd_1554503 : Nat := 798207217856236733563477

theorem tailTrace_1554503 : CollatzResearch.WordTrace tailWord_1554503 prefixEnd_1554503 798207217856236733563477 := by
  unfold tailWord_1554503
  simp only [CollatzResearch.WordTrace]
  refine ⟨56697382287308593820932163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37798254858205729213954775 56697382287308593820932163)
  ·
    refine ⟨85046073430962890731398245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56697382287308593820932163 85046073430962890731398245)
    ·
      refine ⟨15946138768305542012137171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85046073430962890731398245 15946138768305542012137171)
      ·
        refine ⟨23919208152458313018205757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15946138768305542012137171 23919208152458313018205757)
        ·
          refine ⟨8969703057171867381827159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23919208152458313018205757 8969703057171867381827159)
          ·
            refine ⟨13454554585757801072740739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8969703057171867381827159 13454554585757801072740739)
            ·
              refine ⟨20181831878636701609111109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13454554585757801072740739 20181831878636701609111109)
              ·
                refine ⟨3784093477244381551708333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20181831878636701609111109 3784093477244381551708333)
                ·
                  refine ⟨1419035053966643081890625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3784093477244381551708333 1419035053966643081890625)
                  ·
                    refine ⟨1064276290474982311417969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1419035053966643081890625 1064276290474982311417969)
                    ·
                      refine ⟨798207217856236733563477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1064276290474982311417969 798207217856236733563477)
                      ·
                        rfl

theorem cell23_1554503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_1554503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554503 prefixEnd_1554503 := by exact prefixLift 1554503
  have htrace : WordTrace (prefixWord ++ tailWord_1554503) baseStart_1554503 baseEnd_1554503 := by
    simpa [prefixWord, tailWord_1554503, baseEnd_1554503] using wordTrace_append hprefix tailTrace_1554503
  have hstable : (prefixWord ++ tailWord_1554503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554503).length < 2 ^ (prefixWord ++ tailWord_1554503).sum := by decide
  have hdescent : baseEnd_1554503 < baseStart_1554503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554514 : List Nat := [3, 2, 2, 1, 5, 1, 1, 3, 1, 1, 3]
def baseStart_1554514 : Nat := 118140960795 + 1554514 * 2 ^ 59
def prefixEnd_1554514 : Nat := 4983230072969 + 3 ^ 40 * 1554514 * 2
def baseEnd_1554514 : Nat := 798212866143436190525927

theorem tailTrace_1554514 : CollatzResearch.WordTrace tailWord_1554514 prefixEnd_1554514 798212866143436190525927 := by
  unfold tailWord_1554514
  simp only [CollatzResearch.WordTrace]
  refine ⟨14174445872567185674895649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37798522326845828466388397 14174445872567185674895649)
  ·
    refine ⟨10630834404425389256171737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14174445872567185674895649 10630834404425389256171737)
    ·
      refine ⟨7973125803319041942128803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10630834404425389256171737 7973125803319041942128803)
      ·
        refine ⟨11959688704978562913193205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7973125803319041942128803 11959688704978562913193205)
        ·
          refine ⟨1121220816091740273111863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11959688704978562913193205 1121220816091740273111863)
          ·
            refine ⟨1681831224137610409667795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1121220816091740273111863 1681831224137610409667795)
            ·
              refine ⟨2522746836206415614501693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1681831224137610409667795 2522746836206415614501693)
              ·
                refine ⟨946030063577405855438135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2522746836206415614501693 946030063577405855438135)
                ·
                  refine ⟨1419045095366108783157203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 946030063577405855438135 1419045095366108783157203)
                  ·
                    refine ⟨2128567643049163174735805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1419045095366108783157203 2128567643049163174735805)
                    ·
                      refine ⟨798212866143436190525927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2128567643049163174735805 798212866143436190525927)
                      ·
                        rfl

theorem cell23_1554514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_1554514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554514 prefixEnd_1554514 := by exact prefixLift 1554514
  have htrace : WordTrace (prefixWord ++ tailWord_1554514) baseStart_1554514 baseEnd_1554514 := by
    simpa [prefixWord, tailWord_1554514, baseEnd_1554514] using wordTrace_append hprefix tailTrace_1554514
  have hstable : (prefixWord ++ tailWord_1554514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554514).length < 2 ^ (prefixWord ++ tailWord_1554514).sum := by decide
  have hdescent : baseEnd_1554514 < baseStart_1554514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554537 : List Nat := [1, 2, 1, 1, 1, 5, 5, 2, 1, 2, 2]
def baseStart_1554537 : Nat := 118140960795 + 1554537 * 2 ^ 59
def prefixEnd_1554537 : Nat := 4983230072969 + 3 ^ 40 * 1554537 * 2
def baseEnd_1554537 : Nat := 798224676198489600538321

theorem tailTrace_1554537 : CollatzResearch.WordTrace tailWord_1554537 prefixEnd_1554537 798224676198489600538321 := by
  unfold tailWord_1554537
  simp only [CollatzResearch.WordTrace]
  refine ⟨56698622369185417627669865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37799081579456945085113243 56698622369185417627669865)
  ·
    refine ⟨42523966776889063220752399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56698622369185417627669865 42523966776889063220752399)
    ·
      refine ⟨63785950165333594831128599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42523966776889063220752399 63785950165333594831128599)
      ·
        refine ⟨95678925248000392246692899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63785950165333594831128599 95678925248000392246692899)
        ·
          refine ⟨143518387872000588370039349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95678925248000392246692899 143518387872000588370039349)
          ·
            refine ⟨13454848863000055159691189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143518387872000588370039349 13454848863000055159691189)
            ·
              refine ⟨1261392080906255171221049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13454848863000055159691189 1261392080906255171221049)
              ·
                refine ⟨946044060679691378415787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1261392080906255171221049 946044060679691378415787)
                ·
                  refine ⟨1419066091019537067623681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 946044060679691378415787 1419066091019537067623681)
                  ·
                    refine ⟨1064299568264652800717761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1419066091019537067623681 1064299568264652800717761)
                    ·
                      refine ⟨798224676198489600538321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1064299568264652800717761 798224676198489600538321)
                      ·
                        rfl

theorem cell23_1554537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 1, 2, 2].length) (baseStart_1554537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554537 prefixEnd_1554537 := by exact prefixLift 1554537
  have htrace : WordTrace (prefixWord ++ tailWord_1554537) baseStart_1554537 baseEnd_1554537 := by
    simpa [prefixWord, tailWord_1554537, baseEnd_1554537] using wordTrace_append hprefix tailTrace_1554537
  have hstable : (prefixWord ++ tailWord_1554537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554537).length < 2 ^ (prefixWord ++ tailWord_1554537).sum := by decide
  have hdescent : baseEnd_1554537 < baseStart_1554537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554563 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 3, 3, 2]
def baseStart_1554563 : Nat := 118140960795 + 1554563 * 2 ^ 59
def prefixEnd_1554563 : Nat := 4983230072969 + 3 ^ 40 * 1554563 * 2
def baseEnd_1554563 : Nat := 798238026695506498813201

theorem tailTrace_1554563 : CollatzResearch.WordTrace tailWord_1554563 prefixEnd_1554563 798238026695506498813201 := by
  unfold tailWord_1554563
  simp only [CollatzResearch.WordTrace]
  refine ⟨56699570667091224068116343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37799713778060816045410895 56699570667091224068116343)
  ·
    refine ⟨85049356000636836102174515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56699570667091224068116343 85049356000636836102174515)
    ·
      refine ⟨127574034000955254153261773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85049356000636836102174515 127574034000955254153261773)
      ·
        refine ⟨47840262750358220307473165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127574034000955254153261773 47840262750358220307473165)
        ·
          refine ⟨17940098531384332615302437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47840262750358220307473165 17940098531384332615302437)
          ·
            refine ⟨3363768474634562365369207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17940098531384332615302437 3363768474634562365369207)
            ·
              refine ⟨5045652711951843548053811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3363768474634562365369207 5045652711951843548053811)
              ·
                refine ⟨7568479067927765322080717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5045652711951843548053811 7568479067927765322080717)
                ·
                  refine ⟨2838179650472911995780269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7568479067927765322080717 2838179650472911995780269)
                  ·
                    refine ⟨1064317368927341998417601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2838179650472911995780269 1064317368927341998417601)
                    ·
                      refine ⟨798238026695506498813201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1064317368927341998417601 798238026695506498813201)
                      ·
                        rfl

theorem cell23_1554563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 3, 2].length) (baseStart_1554563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554563 prefixEnd_1554563 := by exact prefixLift 1554563
  have htrace : WordTrace (prefixWord ++ tailWord_1554563) baseStart_1554563 baseEnd_1554563 := by
    simpa [prefixWord, tailWord_1554563, baseEnd_1554563] using wordTrace_append hprefix tailTrace_1554563
  have hstable : (prefixWord ++ tailWord_1554563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554563).length < 2 ^ (prefixWord ++ tailWord_1554563).sum := by decide
  have hdescent : baseEnd_1554563 < baseStart_1554563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554582 : List Nat := [5, 3, 2, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_1554582 : Nat := 118140960795 + 1554582 * 2 ^ 59
def prefixEnd_1554582 : Nat := 4983230072969 + 3 ^ 40 * 1554582 * 2
def baseEnd_1554582 : Nat := 798247782827941924475615

theorem tailTrace_1554582 : CollatzResearch.WordTrace tailWord_1554582 prefixEnd_1554582 798247782827941924475615 := by
  unfold tailWord_1554582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3543766478376399394566125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37800175769348260208705333 3543766478376399394566125)
  ·
    refine ⟨1328912429391149772962297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3543766478376399394566125 1328912429391149772962297)
    ·
      refine ⟨996684322043362329721723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1328912429391149772962297 996684322043362329721723)
      ·
        refine ⟨1495026483065043494582585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 996684322043362329721723 1495026483065043494582585)
        ·
          refine ⟨1121269862298782620936939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1495026483065043494582585 1121269862298782620936939)
          ·
            refine ⟨1681904793448173931405409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1121269862298782620936939 1681904793448173931405409)
            ·
              refine ⟨1261428595086130448554057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1681904793448173931405409 1261428595086130448554057)
              ·
                refine ⟨946071446314597836415543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1261428595086130448554057 946071446314597836415543)
                ·
                  refine ⟨1419107169471896754623315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 946071446314597836415543 1419107169471896754623315)
                  ·
                    refine ⟨2128660754207845131934973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1419107169471896754623315 2128660754207845131934973)
                    ·
                      refine ⟨798247782827941924475615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2128660754207845131934973 798247782827941924475615)
                      ·
                        rfl

theorem cell23_1554582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_1554582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554582 prefixEnd_1554582 := by exact prefixLift 1554582
  have htrace : WordTrace (prefixWord ++ tailWord_1554582) baseStart_1554582 baseEnd_1554582 := by
    simpa [prefixWord, tailWord_1554582, baseEnd_1554582] using wordTrace_append hprefix tailTrace_1554582
  have hstable : (prefixWord ++ tailWord_1554582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554582).length < 2 ^ (prefixWord ++ tailWord_1554582).sum := by decide
  have hdescent : baseEnd_1554582 < baseStart_1554582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554610 : List Nat := [3, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2]
def baseStart_1554610 : Nat := 118140960795 + 1554610 * 2 ^ 59
def prefixEnd_1554610 : Nat := 4983230072969 + 3 ^ 40 * 1554610 * 2
def baseEnd_1554610 : Nat := 798262160286267814925485

theorem tailTrace_1554610 : CollatzResearch.WordTrace tailWord_1554610 prefixEnd_1554610 798262160286267814925485 := by
  unfold tailWord_1554610
  simp only [CollatzResearch.WordTrace]
  refine ⟨14175321224480237773769321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37800856598613967396718189 14175321224480237773769321)
  ·
    refine ⟨10631490918360178330326991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14175321224480237773769321 10631490918360178330326991)
    ·
      refine ⟨15947236377540267495490487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10631490918360178330326991 15947236377540267495490487)
      ·
        refine ⟨23920854566310401243235731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15947236377540267495490487 23920854566310401243235731)
        ·
          refine ⟨35881281849465601864853597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23920854566310401243235731 35881281849465601864853597)
          ·
            refine ⟨13455480693549600699320099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35881281849465601864853597 13455480693549600699320099)
            ·
              refine ⟨20183221040324401048980149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13455480693549600699320099 20183221040324401048980149)
              ·
                refine ⟨1892176972530412598341889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20183221040324401048980149 1892176972530412598341889)
                ·
                  refine ⟨1419132729397809448756417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1892176972530412598341889 1419132729397809448756417)
                  ·
                    refine ⟨1064349547048357086567313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1419132729397809448756417 1064349547048357086567313)
                    ·
                      refine ⟨798262160286267814925485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1064349547048357086567313 798262160286267814925485)
                      ·
                        rfl

theorem cell23_1554610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_1554610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554610 prefixEnd_1554610 := by exact prefixLift 1554610
  have htrace : WordTrace (prefixWord ++ tailWord_1554610) baseStart_1554610 baseEnd_1554610 := by
    simpa [prefixWord, tailWord_1554610, baseEnd_1554610] using wordTrace_append hprefix tailTrace_1554610
  have hstable : (prefixWord ++ tailWord_1554610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554610).length < 2 ^ (prefixWord ++ tailWord_1554610).sum := by decide
  have hdescent : baseEnd_1554610 < baseStart_1554610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554666 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_1554666 : Nat := 118140960795 + 1554666 * 2 ^ 59
def prefixEnd_1554666 : Nat := 4983230072969 + 3 ^ 40 * 1554666 * 2
def baseEnd_1554666 : Nat := 798290915202919595825227

theorem tailTrace_1554666 : CollatzResearch.WordTrace tailWord_1554666 prefixEnd_1554666 798290915202919595825227 := by
  unfold tailWord_1554666
  simp only [CollatzResearch.WordTrace]
  refine ⟨14175831846429518164778963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37802218257145381772743901 14175831846429518164778963)
  ·
    refine ⟨21263747769644277247168445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14175831846429518164778963 21263747769644277247168445)
    ·
      refine ⟨7973905413616603967688167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21263747769644277247168445 7973905413616603967688167)
      ·
        refine ⟨11960858120424905951532251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7973905413616603967688167 11960858120424905951532251)
        ·
          refine ⟨17941287180637358927298377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11960858120424905951532251 17941287180637358927298377)
          ·
            refine ⟨13455965385478019195473783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17941287180637358927298377 13455965385478019195473783)
            ·
              refine ⟨20183948078217028793210675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13455965385478019195473783 20183948078217028793210675)
              ·
                refine ⟨30275922117325543189816013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20183948078217028793210675 30275922117325543189816013)
                ·
                  refine ⟨11353470793997078696181005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30275922117325543189816013 11353470793997078696181005)
                  ·
                    refine ⟨4257551547748904511067877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11353470793997078696181005 4257551547748904511067877)
                    ·
                      refine ⟨798290915202919595825227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4257551547748904511067877 798290915202919595825227)
                      ·
                        rfl

theorem cell23_1554666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_1554666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554666 prefixEnd_1554666 := by exact prefixLift 1554666
  have htrace : WordTrace (prefixWord ++ tailWord_1554666) baseStart_1554666 baseEnd_1554666 := by
    simpa [prefixWord, tailWord_1554666, baseEnd_1554666] using wordTrace_append hprefix tailTrace_1554666
  have hstable : (prefixWord ++ tailWord_1554666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554666).length < 2 ^ (prefixWord ++ tailWord_1554666).sum := by decide
  have hdescent : baseEnd_1554666 < baseStart_1554666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554743 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 1, 5, 2]
def baseStart_1554743 : Nat := 118140960795 + 1554743 * 2 ^ 59
def prefixEnd_1554743 : Nat := 4983230072969 + 3 ^ 40 * 1554743 * 2
def baseEnd_1554743 : Nat := 798330453213315794562373

theorem tailTrace_1554743 : CollatzResearch.WordTrace tailWord_1554743 prefixEnd_1554743 798330453213315794562373 := by
  unfold tailWord_1554743
  simp only [CollatzResearch.WordTrace]
  refine ⟨56706135806439114809668883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37804090537626076539779255 56706135806439114809668883)
  ·
    refine ⟨85059203709658672214503325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56706135806439114809668883 85059203709658672214503325)
    ·
      refine ⟨31897201391122002080438747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85059203709658672214503325 31897201391122002080438747)
      ·
        refine ⟨47845802086683003120658121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31897201391122002080438747 47845802086683003120658121)
        ·
          refine ⟨35884351565012252340493591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47845802086683003120658121 35884351565012252340493591)
          ·
            refine ⟨53826527347518378510740387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35884351565012252340493591 53826527347518378510740387)
            ·
              refine ⟨80739791021277567766110581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53826527347518378510740387 80739791021277567766110581)
              ·
                refine ⟨7569355408244771978072867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80739791021277567766110581 7569355408244771978072867)
                ·
                  refine ⟨11354033112367157967109301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7569355408244771978072867 11354033112367157967109301)
                  ·
                    refine ⟨1064440604284421059416497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11354033112367157967109301 1064440604284421059416497)
                    ·
                      refine ⟨798330453213315794562373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1064440604284421059416497 798330453213315794562373)
                      ·
                        rfl

theorem cell23_1554743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 5, 2].length) (baseStart_1554743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554743 prefixEnd_1554743 := by exact prefixLift 1554743
  have htrace : WordTrace (prefixWord ++ tailWord_1554743) baseStart_1554743 baseEnd_1554743 := by
    simpa [prefixWord, tailWord_1554743, baseEnd_1554743] using wordTrace_append hprefix tailTrace_1554743
  have hstable : (prefixWord ++ tailWord_1554743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554743).length < 2 ^ (prefixWord ++ tailWord_1554743).sum := by decide
  have hdescent : baseEnd_1554743 < baseStart_1554743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554760 : List Nat := [2, 1, 3, 1, 1, 2, 4, 2, 2, 3, 2]
def baseStart_1554760 : Nat := 118140960795 + 1554760 * 2 ^ 59
def prefixEnd_1554760 : Nat := 4983230072969 + 3 ^ 40 * 1554760 * 2
def baseEnd_1554760 : Nat := 798339182384442228049795

theorem tailTrace_1554760 : CollatzResearch.WordTrace tailWord_1554760 prefixEnd_1554760 798339182384442228049795 := by
  unfold tailWord_1554760
  simp only [CollatzResearch.WordTrace]
  refine ⟨28353377923688763356518867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37804503898251684475358489 28353377923688763356518867)
  ·
    refine ⟨42530066885533145034778301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28353377923688763356518867 42530066885533145034778301)
    ·
      refine ⟨15948775082074929388041863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42530066885533145034778301 15948775082074929388041863)
      ·
        refine ⟨23923162623112394082062795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15948775082074929388041863 23923162623112394082062795)
        ·
          refine ⟨35884743934668591123094193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23923162623112394082062795 35884743934668591123094193)
          ·
            refine ⟨26913557951001443342320645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35884743934668591123094193 26913557951001443342320645)
            ·
              refine ⟨5046292115812770626685121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26913557951001443342320645 5046292115812770626685121)
              ·
                refine ⟨3784719086859577970013841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5046292115812770626685121 3784719086859577970013841)
                ·
                  refine ⟨2838539315144683477510381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3784719086859577970013841 2838539315144683477510381)
                  ·
                    refine ⟨1064452243179256304066393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2838539315144683477510381 1064452243179256304066393)
                    ·
                      refine ⟨798339182384442228049795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1064452243179256304066393 798339182384442228049795)
                      ·
                        rfl

theorem cell23_1554760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_1554760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554760 prefixEnd_1554760 := by exact prefixLift 1554760
  have htrace : WordTrace (prefixWord ++ tailWord_1554760) baseStart_1554760 baseEnd_1554760 := by
    simpa [prefixWord, tailWord_1554760, baseEnd_1554760] using wordTrace_append hprefix tailTrace_1554760
  have hstable : (prefixWord ++ tailWord_1554760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554760).length < 2 ^ (prefixWord ++ tailWord_1554760).sum := by decide
  have hdescent : baseEnd_1554760 < baseStart_1554760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554793 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 3, 2, 3]
def baseStart_1554793 : Nat := 118140960795 + 1554793 * 2 ^ 59
def prefixEnd_1554793 : Nat := 4983230072969 + 3 ^ 40 * 1554793 * 2
def baseEnd_1554793 : Nat := 798356127246040598937143

theorem tailTrace_1554793 : CollatzResearch.WordTrace tailWord_1554793 prefixEnd_1554793 798356127246040598937143 := by
  unfold tailWord_1554793
  simp only [CollatzResearch.WordTrace]
  refine ⟨56707959456257973348989033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37805306304171982232659355 56707959456257973348989033)
  ·
    refine ⟨42530969592193480011741775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56707959456257973348989033 42530969592193480011741775)
    ·
      refine ⟨63796454388290220017612663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42530969592193480011741775 63796454388290220017612663)
      ·
        refine ⟨95694681582435330026418995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63796454388290220017612663 95694681582435330026418995)
        ·
          refine ⟨143542022373652995039628493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95694681582435330026418995 143542022373652995039628493)
          ·
            refine ⟨53828258390119873139860685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143542022373652995039628493 53828258390119873139860685)
            ·
              refine ⟨20185596896294952427447757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53828258390119873139860685 20185596896294952427447757)
              ·
                refine ⟨7569598836110607160292909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20185596896294952427447757 7569598836110607160292909)
                ·
                  refine ⟨2838599563541477685109841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7569598836110607160292909 2838599563541477685109841)
                  ·
                    refine ⟨2128949672656108263832381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2838599563541477685109841 2128949672656108263832381)
                    ·
                      refine ⟨798356127246040598937143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2128949672656108263832381 798356127246040598937143)
                      ·
                        rfl

theorem cell23_1554793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 2, 3].length) (baseStart_1554793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554793 prefixEnd_1554793 := by exact prefixLift 1554793
  have htrace : WordTrace (prefixWord ++ tailWord_1554793) baseStart_1554793 baseEnd_1554793 := by
    simpa [prefixWord, tailWord_1554793, baseEnd_1554793] using wordTrace_append hprefix tailTrace_1554793
  have hstable : (prefixWord ++ tailWord_1554793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554793).length < 2 ^ (prefixWord ++ tailWord_1554793).sum := by decide
  have hdescent : baseEnd_1554793 < baseStart_1554793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554794 : List Nat := [3, 1, 3, 3, 1, 3, 1, 1, 2, 3, 2]
def baseStart_1554794 : Nat := 118140960795 + 1554794 * 2 ^ 59
def prefixEnd_1554794 : Nat := 4983230072969 + 3 ^ 40 * 1554794 * 2
def baseEnd_1554794 : Nat := 798356640726695095024639

theorem tailTrace_1554794 : CollatzResearch.WordTrace tailWord_1554794 prefixEnd_1554794 798356640726695095024639 := by
  unfold tailWord_1554794
  simp only [CollatzResearch.WordTrace]
  refine ⟨14176998982313587629943859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37805330619502900346516957 14176998982313587629943859)
  ·
    refine ⟨21265498473470381444915789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14176998982313587629943859 21265498473470381444915789)
    ·
      refine ⟨7974561927551393041843421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21265498473470381444915789 7974561927551393041843421)
      ·
        refine ⟨2990460722831772390691283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7974561927551393041843421 2990460722831772390691283)
        ·
          refine ⟨4485691084247658586036925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2990460722831772390691283 4485691084247658586036925)
          ·
            refine ⟨1682134156592871969763847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4485691084247658586036925 1682134156592871969763847)
            ·
              refine ⟨2523201234889307954645771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1682134156592871969763847 2523201234889307954645771)
              ·
                refine ⟨3784801852333961931968657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2523201234889307954645771 3784801852333961931968657)
                ·
                  refine ⟨2838601389250471448976493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3784801852333961931968657 2838601389250471448976493)
                  ·
                    refine ⟨1064475520968926793366185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2838601389250471448976493 1064475520968926793366185)
                    ·
                      refine ⟨798356640726695095024639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1064475520968926793366185 798356640726695095024639)
                      ·
                        rfl

theorem cell23_1554794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_1554794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554794 prefixEnd_1554794 := by exact prefixLift 1554794
  have htrace : WordTrace (prefixWord ++ tailWord_1554794) baseStart_1554794 baseEnd_1554794 := by
    simpa [prefixWord, tailWord_1554794, baseEnd_1554794] using wordTrace_append hprefix tailTrace_1554794
  have hstable : (prefixWord ++ tailWord_1554794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554794).length < 2 ^ (prefixWord ++ tailWord_1554794).sum := by decide
  have hdescent : baseEnd_1554794 < baseStart_1554794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554816 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 6]
def baseStart_1554816 : Nat := 118140960795 + 1554816 * 2 ^ 59
def prefixEnd_1554816 : Nat := 4983230072969 + 3 ^ 40 * 1554816 * 2
def baseEnd_1554816 : Nat := 798367937301094008949537

theorem tailTrace_1554816 : CollatzResearch.WordTrace tailWord_1554816 prefixEnd_1554816 798367937301094008949537 := by
  unfold tailWord_1554816
  simp only [CollatzResearch.WordTrace]
  refine ⟨28354399167587324138538151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37805865556783098851384201 28354399167587324138538151)
  ·
    refine ⟨42531598751380986207807227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28354399167587324138538151 42531598751380986207807227)
    ·
      refine ⟨63797398127071479311710841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42531598751380986207807227 63797398127071479311710841)
      ·
        refine ⟨47848048595303609483783131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63797398127071479311710841 47848048595303609483783131)
        ·
          refine ⟨71772072892955414225674697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47848048595303609483783131 71772072892955414225674697)
          ·
            refine ⟨53829054669716560669256023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71772072892955414225674697 53829054669716560669256023)
            ·
              refine ⟨80743582004574841003884035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53829054669716560669256023 80743582004574841003884035)
              ·
                refine ⟨121115373006862261505826053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80743582004574841003884035 121115373006862261505826053)
                ·
                  refine ⟨22709132438786674032342385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121115373006862261505826053 22709132438786674032342385)
                  ·
                    refine ⟨17031849329090005524256789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22709132438786674032342385 17031849329090005524256789)
                    ·
                      refine ⟨798367937301094008949537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17031849329090005524256789 798367937301094008949537)
                      ·
                        rfl

theorem cell23_1554816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_1554816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554816 prefixEnd_1554816 := by exact prefixLift 1554816
  have htrace : WordTrace (prefixWord ++ tailWord_1554816) baseStart_1554816 baseEnd_1554816 := by
    simpa [prefixWord, tailWord_1554816, baseEnd_1554816] using wordTrace_append hprefix tailTrace_1554816
  have hstable : (prefixWord ++ tailWord_1554816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554816).length < 2 ^ (prefixWord ++ tailWord_1554816).sum := by decide
  have hdescent : baseEnd_1554816 < baseStart_1554816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554817 : List Nat := [1, 2, 4, 3, 1, 1, 3, 2, 2, 4]
def baseStart_1554817 : Nat := 118140960795 + 1554817 * 2 ^ 59
def prefixEnd_1554817 : Nat := 4983230072969 + 3 ^ 40 * 1554817 * 2
def baseEnd_1554817 : Nat := 266122816927249501679011

theorem tailTrace_1554817 : CollatzResearch.WordTrace tailWord_1554817 prefixEnd_1554817 266122816927249501679011 := by
  unfold tailWord_1554817
  simp only [CollatzResearch.WordTrace]
  refine ⟨56708834808171025447862705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37805889872114016965241803 56708834808171025447862705)
  ·
    refine ⟨42531626106128269085897029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56708834808171025447862705 42531626106128269085897029)
    ·
      refine ⟨7974679894899050453605693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42531626106128269085897029 7974679894899050453605693)
      ·
        refine ⟨2990504960587143920102135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7974679894899050453605693 2990504960587143920102135)
        ·
          refine ⟨4485757440880715880153203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2990504960587143920102135 4485757440880715880153203)
          ·
            refine ⟨6728636161321073820229805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4485757440880715880153203 6728636161321073820229805)
            ·
              refine ⟨2523238560495402682586177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6728636161321073820229805 2523238560495402682586177)
              ·
                refine ⟨1892428920371552011939633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2523238560495402682586177 1892428920371552011939633)
                ·
                  refine ⟨1419321690278664008954725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1892428920371552011939633 1419321690278664008954725)
                  ·
                    refine ⟨266122816927249501679011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1419321690278664008954725 266122816927249501679011)
                    ·
                      rfl

theorem cell23_1554817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_1554817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554817 prefixEnd_1554817 := by exact prefixLift 1554817
  have htrace : WordTrace (prefixWord ++ tailWord_1554817) baseStart_1554817 baseEnd_1554817 := by
    simpa [prefixWord, tailWord_1554817, baseEnd_1554817] using wordTrace_append hprefix tailTrace_1554817
  have hstable : (prefixWord ++ tailWord_1554817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554817).length < 2 ^ (prefixWord ++ tailWord_1554817).sum := by decide
  have hdescent : baseEnd_1554817 < baseStart_1554817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554824 : List Nat := [2, 1, 3, 3, 1, 1, 1, 6, 1, 2, 2]
def baseStart_1554824 : Nat := 118140960795 + 1554824 * 2 ^ 59
def prefixEnd_1554824 : Nat := 4983230072969 + 3 ^ 40 * 1554824 * 2
def baseEnd_1554824 : Nat := 798372045146329977649501

theorem tailTrace_1554824 : CollatzResearch.WordTrace tailWord_1554824 prefixEnd_1554824 798372045146329977649501 := by
  unfold tailWord_1554824
  simp only [CollatzResearch.WordTrace]
  refine ⟨28354545059572832821683763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37806060079430443762245017 28354545059572832821683763)
  ·
    refine ⟨42531817589359249232525645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28354545059572832821683763 42531817589359249232525645)
    ·
      refine ⟨15949431596009718462197117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42531817589359249232525645 15949431596009718462197117)
      ·
        refine ⟨5981036848503644423323919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15949431596009718462197117 5981036848503644423323919)
        ·
          refine ⟨8971555272755466634985879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5981036848503644423323919 8971555272755466634985879)
          ·
            refine ⟨13457332909133199952478819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8971555272755466634985879 13457332909133199952478819)
            ·
              refine ⟨20185999363699799928718229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13457332909133199952478819 20185999363699799928718229)
              ·
                refine ⟨946218720173428121658667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20185999363699799928718229 946218720173428121658667)
                ·
                  refine ⟨1419328080260142182488001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 946218720173428121658667 1419328080260142182488001)
                  ·
                    refine ⟨1064496060195106636866001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1419328080260142182488001 1064496060195106636866001)
                    ·
                      refine ⟨798372045146329977649501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1064496060195106636866001 798372045146329977649501)
                      ·
                        rfl

theorem cell23_1554824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_1554824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554824 prefixEnd_1554824 := by exact prefixLift 1554824
  have htrace : WordTrace (prefixWord ++ tailWord_1554824) baseStart_1554824 baseEnd_1554824 := by
    simpa [prefixWord, tailWord_1554824, baseEnd_1554824] using wordTrace_append hprefix tailTrace_1554824
  have hstable : (prefixWord ++ tailWord_1554824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554824).length < 2 ^ (prefixWord ++ tailWord_1554824).sum := by decide
  have hdescent : baseEnd_1554824 < baseStart_1554824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554883 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 3]
def baseStart_1554883 : Nat := 118140960795 + 1554883 * 2 ^ 59
def prefixEnd_1554883 : Nat := 4983230072969 + 3 ^ 40 * 1554883 * 2
def baseEnd_1554883 : Nat := 798402340504945246811729

theorem tailTrace_1554883 : CollatzResearch.WordTrace tailWord_1554883 prefixEnd_1554883 798402340504945246811729 := by
  unfold tailWord_1554883
  simp only [CollatzResearch.WordTrace]
  refine ⟨56711242025931918719765303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37807494683954612479843535 56711242025931918719765303)
  ·
    refine ⟨85066863038897878079647955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56711242025931918719765303 85066863038897878079647955)
    ·
      refine ⟨127600294558346817119471933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85066863038897878079647955 127600294558346817119471933)
      ·
        refine ⟨47850110459380056419801975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127600294558346817119471933 47850110459380056419801975)
        ·
          refine ⟨71775165689070084629702963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47850110459380056419801975 71775165689070084629702963)
          ·
            refine ⟨107662748533605126944554445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71775165689070084629702963 107662748533605126944554445)
            ·
              refine ⟨40373530700101922604207917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107662748533605126944554445 40373530700101922604207917)
              ·
                refine ⟨15140074012538220976577969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40373530700101922604207917 15140074012538220976577969)
                ·
                  refine ⟨11355055509403665732433477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15140074012538220976577969 11355055509403665732433477)
                  ·
                    refine ⟨2129072908013187324831277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11355055509403665732433477 2129072908013187324831277)
                    ·
                      refine ⟨798402340504945246811729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2129072908013187324831277 798402340504945246811729)
                      ·
                        rfl

theorem cell23_1554883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_1554883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554883 prefixEnd_1554883 := by exact prefixLift 1554883
  have htrace : WordTrace (prefixWord ++ tailWord_1554883) baseStart_1554883 baseEnd_1554883 := by
    simpa [prefixWord, tailWord_1554883, baseEnd_1554883] using wordTrace_append hprefix tailTrace_1554883
  have hstable : (prefixWord ++ tailWord_1554883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554883).length < 2 ^ (prefixWord ++ tailWord_1554883).sum := by decide
  have hdescent : baseEnd_1554883 < baseStart_1554883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554900 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1554900 : Nat := 118140960795 + 1554900 * 2 ^ 59
def prefixEnd_1554900 : Nat := 4983230072969 + 3 ^ 40 * 1554900 * 2
def baseEnd_1554900 : Nat := 798411069676071680299151

theorem tailTrace_1554900 : CollatzResearch.WordTrace tailWord_1554900 prefixEnd_1554900 798411069676071680299151 := by
  unfold tailWord_1554900
  simp only [CollatzResearch.WordTrace]
  refine ⟨28355931033435165311567077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37807908044580220415422769 28355931033435165311567077)
  ·
    refine ⟨5316737068769093495918827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28355931033435165311567077 5316737068769093495918827)
    ·
      refine ⟨7975105603153640243878241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5316737068769093495918827 7975105603153640243878241)
      ·
        refine ⟨5981329202365230182908681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7975105603153640243878241 5981329202365230182908681)
        ·
          refine ⟨4485996901773922637181511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5981329202365230182908681 4485996901773922637181511)
          ·
            refine ⟨6728995352660883955772267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4485996901773922637181511 6728995352660883955772267)
            ·
              refine ⟨10093493028991325933658401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6728995352660883955772267 10093493028991325933658401)
              ·
                refine ⟨7570119771743494450243801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10093493028991325933658401 7570119771743494450243801)
                ·
                  refine ⟨5677589828807620837682851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7570119771743494450243801 5677589828807620837682851)
                  ·
                    refine ⟨8516384743211431256524277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5677589828807620837682851 8516384743211431256524277)
                    ·
                      refine ⟨798411069676071680299151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8516384743211431256524277 798411069676071680299151)
                      ·
                        rfl

theorem cell23_1554900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1554900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554900 prefixEnd_1554900 := by exact prefixLift 1554900
  have htrace : WordTrace (prefixWord ++ tailWord_1554900) baseStart_1554900 baseEnd_1554900 := by
    simpa [prefixWord, tailWord_1554900, baseEnd_1554900] using wordTrace_append hprefix tailTrace_1554900
  have hstable : (prefixWord ++ tailWord_1554900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554900).length < 2 ^ (prefixWord ++ tailWord_1554900).sum := by decide
  have hdescent : baseEnd_1554900 < baseStart_1554900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554937 : List Nat := [1, 2, 1, 3, 1, 2, 6, 2, 5]
def baseStart_1554937 : Nat := 118140960795 + 1554937 * 2 ^ 59
def prefixEnd_1554937 : Nat := 4983230072969 + 3 ^ 40 * 1554937 * 2
def baseEnd_1554937 : Nat := 88714452051143115059609

theorem tailTrace_1554937 : CollatzResearch.WordTrace tailWord_1554937 prefixEnd_1554937 88714452051143115059609 := by
  unfold tailWord_1554937
  simp only [CollatzResearch.WordTrace]
  refine ⟨56713211567736285942231065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37808807711824190628154043 56713211567736285942231065)
  ·
    refine ⟨42534908675802214456673299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56713211567736285942231065 42534908675802214456673299)
    ·
      refine ⟨63802363013703321685009949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42534908675802214456673299 63802363013703321685009949)
      ·
        refine ⟨23925886130138745631878731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63802363013703321685009949 23925886130138745631878731)
        ·
          refine ⟨35888829195208118447818097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23925886130138745631878731 35888829195208118447818097)
          ·
            refine ⟨26916621896406088835863573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35888829195208118447818097 26916621896406088835863573)
            ·
              refine ⟨1261716651394035414181105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26916621896406088835863573 1261716651394035414181105)
              ·
                refine ⟨946287488545526560635829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1261716651394035414181105 946287488545526560635829)
                ·
                  refine ⟨88714452051143115059609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 946287488545526560635829 88714452051143115059609)
                  ·
                    rfl

theorem cell23_1554937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 5].length) (baseStart_1554937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554937 prefixEnd_1554937 := by exact prefixLift 1554937
  have htrace : WordTrace (prefixWord ++ tailWord_1554937) baseStart_1554937 baseEnd_1554937 := by
    simpa [prefixWord, tailWord_1554937, baseEnd_1554937] using wordTrace_append hprefix tailTrace_1554937
  have hstable : (prefixWord ++ tailWord_1554937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554937).length < 2 ^ (prefixWord ++ tailWord_1554937).sum := by decide
  have hdescent : baseEnd_1554937 < baseStart_1554937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554943 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 5]
def baseStart_1554943 : Nat := 118140960795 + 1554943 * 2 ^ 59
def prefixEnd_1554943 : Nat := 4983230072969 + 3 ^ 40 * 1554943 * 2
def baseEnd_1554943 : Nat := 798433149344215012061453

theorem tailTrace_1554943 : CollatzResearch.WordTrace tailWord_1554943 prefixEnd_1554943 798433149344215012061453 := by
  unfold tailWord_1554943
  simp only [CollatzResearch.WordTrace]
  refine ⟨56713430405714548966949483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37808953603809699311299655 56713430405714548966949483)
  ·
    refine ⟨85070145608571823450424225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56713430405714548966949483 85070145608571823450424225)
    ·
      refine ⟨63802609206428867587818169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85070145608571823450424225 63802609206428867587818169)
      ·
        refine ⟨47851956904821650690863627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63802609206428867587818169 47851956904821650690863627)
        ·
          refine ⟨71777935357232476036295441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47851956904821650690863627 71777935357232476036295441)
          ·
            refine ⟨53833451517924357027221581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71777935357232476036295441 53833451517924357027221581)
            ·
              refine ⟨20187544319221633885208093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53833451517924357027221581 20187544319221633885208093)
              ·
                refine ⟨7570329119708112706953035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20187544319221633885208093 7570329119708112706953035)
                ·
                  refine ⟨11355493679562169060429553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7570329119708112706953035 11355493679562169060429553)
                  ·
                    refine ⟨8516620259671626795322165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11355493679562169060429553 8516620259671626795322165)
                    ·
                      refine ⟨798433149344215012061453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8516620259671626795322165 798433149344215012061453)
                      ·
                        rfl

theorem cell23_1554943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_1554943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554943 prefixEnd_1554943 := by exact prefixLift 1554943
  have htrace : WordTrace (prefixWord ++ tailWord_1554943) baseStart_1554943 baseEnd_1554943 := by
    simpa [prefixWord, tailWord_1554943, baseEnd_1554943] using wordTrace_append hprefix tailTrace_1554943
  have hstable : (prefixWord ++ tailWord_1554943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554943).length < 2 ^ (prefixWord ++ tailWord_1554943).sum := by decide
  have hdescent : baseEnd_1554943 < baseStart_1554943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554967 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 1, 7]
def baseStart_1554967 : Nat := 118140960795 + 1554967 * 2 ^ 59
def prefixEnd_1554967 : Nat := 4983230072969 + 3 ^ 40 * 1554967 * 2
def baseEnd_1554967 : Nat := 266148490959974306053781

theorem tailTrace_1554967 : CollatzResearch.WordTrace tailWord_1554967 prefixEnd_1554967 266148490959974306053781 := by
  unfold tailWord_1554967
  simp only [CollatzResearch.WordTrace]
  refine ⟨56714305757627601065823155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37809537171751734043882103 56714305757627601065823155)
  ·
    refine ⟨85071458636441401598734733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56714305757627601065823155 85071458636441401598734733)
    ·
      refine ⟨31901796988665525599525525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85071458636441401598734733 31901796988665525599525525)
      ·
        refine ⟨1495396733843696512477759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31901796988665525599525525 1495396733843696512477759)
        ·
          refine ⟨2243095100765544768716639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1495396733843696512477759 2243095100765544768716639)
          ·
            refine ⟨3364642651148317153074959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2243095100765544768716639 3364642651148317153074959)
            ·
              refine ⟨5046963976722475729612439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3364642651148317153074959 5046963976722475729612439)
              ·
                refine ⟨7570445965083713594418659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5046963976722475729612439 7570445965083713594418659)
                ·
                  refine ⟨11355668947625570391627989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7570445965083713594418659 11355668947625570391627989)
                  ·
                    refine ⟨266148490959974306053781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11355668947625570391627989 266148490959974306053781)
                    ·
                      rfl

theorem cell23_1554967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_1554967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554967 prefixEnd_1554967 := by exact prefixLift 1554967
  have htrace : WordTrace (prefixWord ++ tailWord_1554967) baseStart_1554967 baseEnd_1554967 := by
    simpa [prefixWord, tailWord_1554967, baseEnd_1554967] using wordTrace_append hprefix tailTrace_1554967
  have hstable : (prefixWord ++ tailWord_1554967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554967).length < 2 ^ (prefixWord ++ tailWord_1554967).sum := by decide
  have hdescent : baseEnd_1554967 < baseStart_1554967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554997 : List Nat := [1, 3, 3, 1, 1, 2, 4, 1, 3, 4]
def baseStart_1554997 : Nat := 118140960795 + 1554997 * 2 ^ 59
def prefixEnd_1554997 : Nat := 4983230072969 + 3 ^ 40 * 1554997 * 2
def baseEnd_1554997 : Nat := 266153625766519266928735

theorem tailTrace_1554997 : CollatzResearch.WordTrace tailWord_1554997 prefixEnd_1554997 266153625766519266928735 := by
  unfold tailWord_1554997
  simp only [CollatzResearch.WordTrace]
  refine ⟨56715399947518916189415245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37810266631679277459610163 56715399947518916189415245)
  ·
    refine ⟨21268274980319593571030717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56715399947518916189415245 21268274980319593571030717)
    ·
      refine ⟨7975603117619847589136519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21268274980319593571030717 7975603117619847589136519)
      ·
        refine ⟨11963404676429771383704779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7975603117619847589136519 11963404676429771383704779)
        ·
          refine ⟨17945107014644657075557169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11963404676429771383704779 17945107014644657075557169)
          ·
            refine ⟨13458830260983492806667877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17945107014644657075557169 13458830260983492806667877)
            ·
              refine ⟨2523530673934404901250227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13458830260983492806667877 2523530673934404901250227)
              ·
                refine ⟨3785296010901607351875341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2523530673934404901250227 3785296010901607351875341)
                ·
                  refine ⟨1419486004088102756953253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3785296010901607351875341 1419486004088102756953253)
                  ·
                    refine ⟨266153625766519266928735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1419486004088102756953253 266153625766519266928735)
                    ·
                      rfl

theorem cell23_1554997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_1554997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1554997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1554997 prefixEnd_1554997 := by exact prefixLift 1554997
  have htrace : WordTrace (prefixWord ++ tailWord_1554997) baseStart_1554997 baseEnd_1554997 := by
    simpa [prefixWord, tailWord_1554997, baseEnd_1554997] using wordTrace_append hprefix tailTrace_1554997
  have hstable : (prefixWord ++ tailWord_1554997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554997).length < 2 ^ (prefixWord ++ tailWord_1554997).sum := by decide
  have hdescent : baseEnd_1554997 < baseStart_1554997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555020 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 2, 5, 3]
def baseStart_1555020 : Nat := 118140960795 + 1555020 * 2 ^ 59
def prefixEnd_1555020 : Nat := 4983230072969 + 3 ^ 40 * 1555020 * 2
def baseEnd_1555020 : Nat := 798472687354611210798599

theorem tailTrace_1555020 : CollatzResearch.WordTrace tailWord_1555020 prefixEnd_1555020 798472687354611210798599 := by
  unfold tailWord_1555020
  simp only [CollatzResearch.WordTrace]
  refine ⟨28358119413217795558751257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37810825884290394078335009 28358119413217795558751257)
  ·
    refine ⟨21268589559913346669063443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28358119413217795558751257 21268589559913346669063443)
    ·
      refine ⟨31902884339870020003595165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21268589559913346669063443 31902884339870020003595165)
      ·
        refine ⟨11963581627451257501348187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31902884339870020003595165 11963581627451257501348187)
        ·
          refine ⟨17945372441176886252022281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11963581627451257501348187 17945372441176886252022281)
          ·
            refine ⟨13459029330882664689016711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17945372441176886252022281 13459029330882664689016711)
            ·
              refine ⟨20188543996323997033525067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13459029330882664689016711 20188543996323997033525067)
              ·
                refine ⟨30282815994485995550287601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20188543996323997033525067 30282815994485995550287601)
                ·
                  refine ⟨22712111995864496662715701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30282815994485995550287601 22712111995864496662715701)
                  ·
                    refine ⟨2129260499612296562129597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22712111995864496662715701 2129260499612296562129597)
                    ·
                      refine ⟨798472687354611210798599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2129260499612296562129597 798472687354611210798599)
                      ·
                        rfl

theorem cell23_1555020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_1555020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555020 prefixEnd_1555020 := by exact prefixLift 1555020
  have htrace : WordTrace (prefixWord ++ tailWord_1555020) baseStart_1555020 baseEnd_1555020 := by
    simpa [prefixWord, tailWord_1555020, baseEnd_1555020] using wordTrace_append hprefix tailTrace_1555020
  have hstable : (prefixWord ++ tailWord_1555020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555020).length < 2 ^ (prefixWord ++ tailWord_1555020).sum := by decide
  have hdescent : baseEnd_1555020 < baseStart_1555020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555038 : List Nat := [4, 4, 1, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_1555038 : Nat := 118140960795 + 1555038 * 2 ^ 59
def prefixEnd_1555038 : Nat := 4983230072969 + 3 ^ 40 * 1555038 * 2
def baseEnd_1555038 : Nat := 798481930006392140373517

theorem tailTrace_1555038 : CollatzResearch.WordTrace tailWord_1555038 prefixEnd_1555038 798481930006392140373517 := by
  unfold tailWord_1555038
  simp only [CollatzResearch.WordTrace]
  refine ⟨7089611917546297523957221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37811263560246920127771845 7089611917546297523957221)
  ·
    refine ⟨1329302234539930785741979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7089611917546297523957221 1329302234539930785741979)
    ·
      refine ⟨1993953351809896178612969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1329302234539930785741979 1993953351809896178612969)
      ·
        refine ⟨1495465013857422133959727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1993953351809896178612969 1495465013857422133959727)
        ·
          refine ⟨2243197520786133200939591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1495465013857422133959727 2243197520786133200939591)
          ·
            refine ⟨3364796281179199801409387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2243197520786133200939591 3364796281179199801409387)
            ·
              refine ⟨5047194421768799702114081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3364796281179199801409387 5047194421768799702114081)
              ·
                refine ⟨3785395816326599776585561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5047194421768799702114081 3785395816326599776585561)
                ·
                  refine ⟨2839046862244949832439171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3785395816326599776585561 2839046862244949832439171)
                  ·
                    refine ⟨4258570293367424748658757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2839046862244949832439171 4258570293367424748658757)
                    ·
                      refine ⟨798481930006392140373517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4258570293367424748658757 798481930006392140373517)
                      ·
                        rfl

theorem cell23_1555038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_1555038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555038 prefixEnd_1555038 := by exact prefixLift 1555038
  have htrace : WordTrace (prefixWord ++ tailWord_1555038) baseStart_1555038 baseEnd_1555038 := by
    simpa [prefixWord, tailWord_1555038, baseEnd_1555038] using wordTrace_append hprefix tailTrace_1555038
  have hstable : (prefixWord ++ tailWord_1555038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555038).length < 2 ^ (prefixWord ++ tailWord_1555038).sum := by decide
  have hdescent : baseEnd_1555038 < baseStart_1555038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555048 : List Nat := [2, 1, 4, 3, 2, 1, 3, 2, 1, 4]
def baseStart_1555048 : Nat := 118140960795 + 1555048 * 2 ^ 59
def prefixEnd_1555048 : Nat := 4983230072969 + 3 ^ 40 * 1555048 * 2
def baseEnd_1555048 : Nat := 266162354937645700416157

theorem tailTrace_1555048 : CollatzResearch.WordTrace tailWord_1555048 prefixEnd_1555048 266162354937645700416157 := by
  unfold tailWord_1555048
  simp only [CollatzResearch.WordTrace]
  refine ⟨28358630035167075949760899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37811506713556101266347865 28358630035167075949760899)
  ·
    refine ⟨42537945052750613924641349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28358630035167075949760899 42537945052750613924641349)
    ·
      refine ⟨7975864697390740110870253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42537945052750613924641349 7975864697390740110870253)
      ·
        refine ⟨2990949261521527541576345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7975864697390740110870253 2990949261521527541576345)
        ·
          refine ⟨2243211946141145656182259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2990949261521527541576345 2243211946141145656182259)
          ·
            refine ⟨3364817919211718484273389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2243211946141145656182259 3364817919211718484273389)
            ·
              refine ⟨1261806719704394431602521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3364817919211718484273389 1261806719704394431602521)
              ·
                refine ⟨946355039778295823701891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1261806719704394431602521 946355039778295823701891)
                ·
                  refine ⟨1419532559667443735552837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 946355039778295823701891 1419532559667443735552837)
                  ·
                    refine ⟨266162354937645700416157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1419532559667443735552837 266162354937645700416157)
                    ·
                      rfl

theorem cell23_1555048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_1555048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555048 prefixEnd_1555048 := by exact prefixLift 1555048
  have htrace : WordTrace (prefixWord ++ tailWord_1555048) baseStart_1555048 baseEnd_1555048 := by
    simpa [prefixWord, tailWord_1555048, baseEnd_1555048] using wordTrace_append hprefix tailTrace_1555048
  have hstable : (prefixWord ++ tailWord_1555048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555048).length < 2 ^ (prefixWord ++ tailWord_1555048).sum := by decide
  have hdescent : baseEnd_1555048 < baseStart_1555048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555061 : List Nat := [1, 3, 4, 2, 2, 2, 2, 1, 6]
def baseStart_1555061 : Nat := 118140960795 + 1555061 * 2 ^ 59
def prefixEnd_1555061 : Nat := 4983230072969 + 3 ^ 40 * 1555061 * 2
def baseEnd_1555061 : Nat := 88721526673493950042879

theorem tailTrace_1555061 : CollatzResearch.WordTrace tailWord_1555061 prefixEnd_1555061 88721526673493950042879 := by
  unfold tailWord_1555061
  simp only [CollatzResearch.WordTrace]
  refine ⟨56717734219287055119745037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37811822812858036746496691 56717734219287055119745037)
  ·
    refine ⟨21269150332232645669904389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56717734219287055119745037 21269150332232645669904389)
    ·
      refine ⟨3987965687293621063107073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21269150332232645669904389 3987965687293621063107073)
      ·
        refine ⟨2990974265470215797330305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3987965687293621063107073 2990974265470215797330305)
        ·
          refine ⟨2243230699102661847997729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2990974265470215797330305 2243230699102661847997729)
          ·
            refine ⟨1682423024326996385998297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2243230699102661847997729 1682423024326996385998297)
            ·
              refine ⟨1261817268245247289498723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1682423024326996385998297 1261817268245247289498723)
              ·
                refine ⟨1892725902367870934248085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261817268245247289498723 1892725902367870934248085)
                ·
                  refine ⟨88721526673493950042879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1892725902367870934248085 88721526673493950042879)
                  ·
                    rfl

theorem cell23_1555061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 6].length) (baseStart_1555061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555061 prefixEnd_1555061 := by exact prefixLift 1555061
  have htrace : WordTrace (prefixWord ++ tailWord_1555061) baseStart_1555061 baseEnd_1555061 := by
    simpa [prefixWord, tailWord_1555061, baseEnd_1555061] using wordTrace_append hprefix tailTrace_1555061
  have hstable : (prefixWord ++ tailWord_1555061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555061).length < 2 ^ (prefixWord ++ tailWord_1555061).sum := by decide
  have hdescent : baseEnd_1555061 < baseStart_1555061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555077 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 3, 1, 4]
def baseStart_1555077 : Nat := 118140960795 + 1555077 * 2 ^ 59
def prefixEnd_1555077 : Nat := 4983230072969 + 3 ^ 40 * 1555077 * 2
def baseEnd_1555077 : Nat := 798501955751917487785837

theorem tailTrace_1555077 : CollatzResearch.WordTrace tailWord_1555077 prefixEnd_1555077 798501955751917487785837 := by
  unfold tailWord_1555077
  simp only [CollatzResearch.WordTrace]
  refine ⟨56718317787229089852327485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37812211858152726568218323 56718317787229089852327485)
  ·
    refine ⟨21269369170210908694622807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56718317787229089852327485 21269369170210908694622807)
    ·
      refine ⟨31904053755316363041934211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21269369170210908694622807 31904053755316363041934211)
      ·
        refine ⟨47856080632974544562901317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31904053755316363041934211 47856080632974544562901317)
        ·
          refine ⟨8973015118682727105543997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47856080632974544562901317 8973015118682727105543997)
          ·
            refine ⟨3364880669506022664578999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8973015118682727105543997 3364880669506022664578999)
            ·
              refine ⟨5047321004259033996868499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3364880669506022664578999 5047321004259033996868499)
              ·
                refine ⟨7570981506388550995302749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5047321004259033996868499 7570981506388550995302749)
                ·
                  refine ⟨2839118064895706623238531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7570981506388550995302749 2839118064895706623238531)
                  ·
                    refine ⟨4258677097343559934857797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2839118064895706623238531 4258677097343559934857797)
                    ·
                      refine ⟨798501955751917487785837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4258677097343559934857797 798501955751917487785837)
                      ·
                        rfl

theorem cell23_1555077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_1555077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555077 prefixEnd_1555077 := by exact prefixLift 1555077
  have htrace : WordTrace (prefixWord ++ tailWord_1555077) baseStart_1555077 baseEnd_1555077 := by
    simpa [prefixWord, tailWord_1555077, baseEnd_1555077] using wordTrace_append hprefix tailTrace_1555077
  have hstable : (prefixWord ++ tailWord_1555077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555077).length < 2 ^ (prefixWord ++ tailWord_1555077).sum := by decide
  have hdescent : baseEnd_1555077 < baseStart_1555077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555100 : List Nat := [2, 2, 3, 2, 2, 12]
def baseStart_1555100 : Nat := 118140960795 + 1555100 * 2 ^ 59
def prefixEnd_1555100 : Nat := 4983230072969 + 3 ^ 40 * 1555100 * 2
def baseEnd_1555100 : Nat := 3286064879864077768717

theorem tailTrace_1555100 : CollatzResearch.WordTrace tailWord_1555100 prefixEnd_1555100 3286064879864077768717 := by
  unfold tailWord_1555100
  simp only [CollatzResearch.WordTrace]
  refine ⟨28359578333072882390207377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37812771110763843186943169 28359578333072882390207377)
  ·
    refine ⟨21269683749804661792655533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28359578333072882390207377 21269683749804661792655533)
    ·
      refine ⟨7976131406176748172245825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21269683749804661792655533 7976131406176748172245825)
      ·
        refine ⟨5982098554632561129184369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7976131406176748172245825 5982098554632561129184369)
        ·
          refine ⟨4486573915974420846888277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5982098554632561129184369 4486573915974420846888277)
          ·
            refine ⟨3286064879864077768717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4486573915974420846888277 3286064879864077768717)
            ·
              rfl

theorem cell23_1555100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 12].length) (baseStart_1555100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555100 prefixEnd_1555100 := by exact prefixLift 1555100
  have htrace : WordTrace (prefixWord ++ tailWord_1555100) baseStart_1555100 baseEnd_1555100 := by
    simpa [prefixWord, tailWord_1555100, baseEnd_1555100] using wordTrace_append hprefix tailTrace_1555100
  have hstable : (prefixWord ++ tailWord_1555100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555100).length < 2 ^ (prefixWord ++ tailWord_1555100).sum := by decide
  have hdescent : baseEnd_1555100 < baseStart_1555100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555105 : List Nat := [1, 2, 3, 3, 3, 2, 2, 2, 1, 1, 3]
def baseStart_1555105 : Nat := 118140960795 + 1555105 * 2 ^ 59
def prefixEnd_1555105 : Nat := 4983230072969 + 3 ^ 40 * 1555105 * 2
def baseEnd_1555105 : Nat := 798516333210243378235709

theorem tailTrace_1555105 : CollatzResearch.WordTrace tailWord_1555105 prefixEnd_1555105 798516333210243378235709 := by
  unfold tailWord_1555105
  simp only [CollatzResearch.WordTrace]
  refine ⟨56719339031127650634346769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37812892687418433756231179 56719339031127650634346769)
  ·
    refine ⟨42539504273345737975760077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56719339031127650634346769 42539504273345737975760077)
    ·
      refine ⟨15952314102504651740910029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42539504273345737975760077 15952314102504651740910029)
      ·
        refine ⟨5982117788439244402841261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15952314102504651740910029 5982117788439244402841261)
        ·
          refine ⟨2243294170664716651065473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5982117788439244402841261 2243294170664716651065473)
          ·
            refine ⟨1682470627998537488299105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2243294170664716651065473 1682470627998537488299105)
            ·
              refine ⟨1261852970998903116224329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1682470627998537488299105 1261852970998903116224329)
              ·
                refine ⟨946389728249177337168247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1261852970998903116224329 946389728249177337168247)
                ·
                  refine ⟨1419584592373766005752371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 946389728249177337168247 1419584592373766005752371)
                  ·
                    refine ⟨2129376888560649008628557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1419584592373766005752371 2129376888560649008628557)
                    ·
                      refine ⟨798516333210243378235709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2129376888560649008628557 798516333210243378235709)
                      ·
                        rfl

theorem cell23_1555105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_1555105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555105 prefixEnd_1555105 := by exact prefixLift 1555105
  have htrace : WordTrace (prefixWord ++ tailWord_1555105) baseStart_1555105 baseEnd_1555105 := by
    simpa [prefixWord, tailWord_1555105, baseEnd_1555105] using wordTrace_append hprefix tailTrace_1555105
  have hstable : (prefixWord ++ tailWord_1555105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555105).length < 2 ^ (prefixWord ++ tailWord_1555105).sum := by decide
  have hdescent : baseEnd_1555105 < baseStart_1555105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555117 : List Nat := [1, 5, 2, 1, 1, 2, 3, 8]
def baseStart_1555117 : Nat := 118140960795 + 1555117 * 2 ^ 59
def prefixEnd_1555117 : Nat := 4983230072969 + 3 ^ 40 * 1555117 * 2
def baseEnd_1555117 : Nat := 29574907221411012269839

theorem tailTrace_1555117 : CollatzResearch.WordTrace tailWord_1555117 prefixEnd_1555117 29574907221411012269839 := by
  unfold tailWord_1555117
  simp only [CollatzResearch.WordTrace]
  refine ⟨56719776707084176683783605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37813184471389451122522403 56719776707084176683783605)
  ·
    refine ⟨5317479066289141564104713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56719776707084176683783605 5317479066289141564104713)
    ·
      refine ⟨3988109299716856173078535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5317479066289141564104713 3988109299716856173078535)
      ·
        refine ⟨5982163949575284259617803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3988109299716856173078535 5982163949575284259617803)
        ·
          refine ⟨8973245924362926389426705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5982163949575284259617803 8973245924362926389426705)
          ·
            refine ⟨6729934443272194792070029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8973245924362926389426705 6729934443272194792070029)
            ·
              refine ⟨2523725416227073047026261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6729934443272194792070029 2523725416227073047026261)
              ·
                refine ⟨29574907221411012269839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2523725416227073047026261 29574907221411012269839)
                ·
                  rfl

theorem cell23_1555117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 8].length) (baseStart_1555117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555117 prefixEnd_1555117 := by exact prefixLift 1555117
  have htrace : WordTrace (prefixWord ++ tailWord_1555117) baseStart_1555117 baseEnd_1555117 := by
    simpa [prefixWord, tailWord_1555117, baseEnd_1555117] using wordTrace_append hprefix tailTrace_1555117
  have hstable : (prefixWord ++ tailWord_1555117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555117).length < 2 ^ (prefixWord ++ tailWord_1555117).sum := by decide
  have hdescent : baseEnd_1555117 < baseStart_1555117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555130 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 2, 7]
def baseStart_1555130 : Nat := 118140960795 + 1555130 * 2 ^ 59
def prefixEnd_1555130 : Nat := 4983230072969 + 3 ^ 40 * 1555130 * 2
def baseEnd_1555130 : Nat := 266176390075535260141031

theorem tailTrace_1555130 : CollatzResearch.WordTrace tailWord_1555130 prefixEnd_1555130 266176390075535260141031 := by
  unfold tailWord_1555130
  simp only [CollatzResearch.WordTrace]
  refine ⟨14180062714009269976001711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37813500570691386602671229 14180062714009269976001711)
  ·
    refine ⟨21270094071013904964002567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14180062714009269976001711 21270094071013904964002567)
    ·
      refine ⟨31905141106520857446003851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21270094071013904964002567 31905141106520857446003851)
      ·
        refine ⟨47857711659781286169005777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31905141106520857446003851 47857711659781286169005777)
        ·
          refine ⟨35893283744835964626754333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47857711659781286169005777 35893283744835964626754333)
          ·
            refine ⟨13459981404313486735032875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35893283744835964626754333 13459981404313486735032875)
            ·
              refine ⟨20189972106470230102549313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13459981404313486735032875 20189972106470230102549313)
              ·
                refine ⟨15142479079852672576911985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20189972106470230102549313 15142479079852672576911985)
                ·
                  refine ⟨11356859309889504432683989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15142479079852672576911985 11356859309889504432683989)
                  ·
                    refine ⟨266176390075535260141031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11356859309889504432683989 266176390075535260141031)
                    ·
                      rfl

theorem cell23_1555130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_1555130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555130 prefixEnd_1555130 := by exact prefixLift 1555130
  have htrace : WordTrace (prefixWord ++ tailWord_1555130) baseStart_1555130 baseEnd_1555130 := by
    simpa [prefixWord, tailWord_1555130, baseEnd_1555130] using wordTrace_append hprefix tailTrace_1555130
  have hstable : (prefixWord ++ tailWord_1555130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555130).length < 2 ^ (prefixWord ++ tailWord_1555130).sum := by decide
  have hdescent : baseEnd_1555130 < baseStart_1555130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555142 : List Nat := [6, 1, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_1555142 : Nat := 118140960795 + 1555142 * 2 ^ 59
def prefixEnd_1555142 : Nat := 4983230072969 + 3 ^ 40 * 1555142 * 2
def baseEnd_1555142 : Nat := 266178443998153244491013

theorem tailTrace_1555142 : CollatzResearch.WordTrace tailWord_1555142 prefixEnd_1555142 266178443998153244491013 := by
  unfold tailWord_1555142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1772521516624800186045115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37813792354662403968962453 1772521516624800186045115)
  ·
    refine ⟨2658782274937200279067673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1772521516624800186045115 2658782274937200279067673)
    ·
      refine ⟨1994086706202900209300755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2658782274937200279067673 1994086706202900209300755)
      ·
        refine ⟨2991130059304350313951133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1994086706202900209300755 2991130059304350313951133)
        ·
          refine ⟨1121673772239131367731675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2991130059304350313951133 1121673772239131367731675)
          ·
            refine ⟨1682510658358697051597513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1121673772239131367731675 1682510658358697051597513)
            ·
              refine ⟨1261882993769022788698135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1682510658358697051597513 1261882993769022788698135)
              ·
                refine ⟨1892824490653534183047203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261882993769022788698135 1892824490653534183047203)
                ·
                  refine ⟨2839236735980301274570805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1892824490653534183047203 2839236735980301274570805)
                  ·
                    refine ⟨266178443998153244491013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2839236735980301274570805 266178443998153244491013)
                    ·
                      rfl

theorem cell23_1555142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_1555142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555142 prefixEnd_1555142 := by exact prefixLift 1555142
  have htrace : WordTrace (prefixWord ++ tailWord_1555142) baseStart_1555142 baseEnd_1555142 := by
    simpa [prefixWord, tailWord_1555142, baseEnd_1555142] using wordTrace_append hprefix tailTrace_1555142
  have hstable : (prefixWord ++ tailWord_1555142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555142).length < 2 ^ (prefixWord ++ tailWord_1555142).sum := by decide
  have hdescent : baseEnd_1555142 < baseStart_1555142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555148 : List Nat := [2, 2, 1, 5, 1, 3, 2, 1, 1, 2, 3]
def baseStart_1555148 : Nat := 118140960795 + 1555148 * 2 ^ 59
def prefixEnd_1555148 : Nat := 4983230072969 + 3 ^ 40 * 1555148 * 2
def baseEnd_1555148 : Nat := 798538412878386709998011

theorem tailTrace_1555148 : CollatzResearch.WordTrace tailWord_1555148 prefixEnd_1555148 798538412878386709998011 := by
  unfold tailWord_1555148
  simp only [CollatzResearch.WordTrace]
  refine ⟨28360453684985934489081049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37813938246647912652108065 28360453684985934489081049)
  ·
    refine ⟨21270340263739450866810787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28360453684985934489081049 21270340263739450866810787)
    ·
      refine ⟨31905510395609176300216181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21270340263739450866810787 31905510395609176300216181)
      ·
        refine ⟨2991141599588360278145267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31905510395609176300216181 2991141599588360278145267)
        ·
          refine ⟨4486712399382540417217901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2991141599588360278145267 4486712399382540417217901)
          ·
            refine ⟨1682517149768452656456713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4486712399382540417217901 1682517149768452656456713)
            ·
              refine ⟨1261887862326339492342535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1682517149768452656456713 1261887862326339492342535)
              ·
                refine ⟨1892831793489509238513803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261887862326339492342535 1892831793489509238513803)
                ·
                  refine ⟨2839247690234263857770705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1892831793489509238513803 2839247690234263857770705)
                  ·
                    refine ⟨2129435767675697893328029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2839247690234263857770705 2129435767675697893328029)
                    ·
                      refine ⟨798538412878386709998011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2129435767675697893328029 798538412878386709998011)
                      ·
                        rfl

theorem cell23_1555148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_1555148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555148 prefixEnd_1555148 := by exact prefixLift 1555148
  have htrace : WordTrace (prefixWord ++ tailWord_1555148) baseStart_1555148 baseEnd_1555148 := by
    simpa [prefixWord, tailWord_1555148, baseEnd_1555148] using wordTrace_append hprefix tailTrace_1555148
  have hstable : (prefixWord ++ tailWord_1555148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555148).length < 2 ^ (prefixWord ++ tailWord_1555148).sum := by decide
  have hdescent : baseEnd_1555148 < baseStart_1555148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555200 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 7]
def baseStart_1555200 : Nat := 118140960795 + 1555200 * 2 ^ 59
def prefixEnd_1555200 : Nat := 4983230072969 + 3 ^ 40 * 1555200 * 2
def baseEnd_1555200 : Nat := 798565113872420506547771

theorem tailTrace_1555200 : CollatzResearch.WordTrace tailWord_1555200 prefixEnd_1555200 798565113872420506547771 := by
  unfold tailWord_1555200
  simp only [CollatzResearch.WordTrace]
  refine ⟨28361401982891740929527527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37815202643855654572703369 28361401982891740929527527)
  ·
    refine ⟨42542102974337611394291291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28361401982891740929527527 42542102974337611394291291)
    ·
      refine ⟨63813154461506417091436937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42542102974337611394291291 63813154461506417091436937)
      ·
        refine ⟨47859865846129812818577703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63813154461506417091436937 47859865846129812818577703)
        ·
          refine ⟨71789798769194719227866555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47859865846129812818577703 71789798769194719227866555)
          ·
            refine ⟨107684698153792078841799833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71789798769194719227866555 107684698153792078841799833)
            ·
              refine ⟨80763523615344059131349875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107684698153792078841799833 80763523615344059131349875)
              ·
                refine ⟨121145285423016088697024813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80763523615344059131349875 121145285423016088697024813)
                ·
                  refine ⟨45429482033631033261384305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121145285423016088697024813 45429482033631033261384305)
                  ·
                    refine ⟨34072111525223274946038229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45429482033631033261384305 34072111525223274946038229)
                    ·
                      refine ⟨798565113872420506547771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34072111525223274946038229 798565113872420506547771)
                      ·
                        rfl

theorem cell23_1555200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_1555200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555200 prefixEnd_1555200 := by exact prefixLift 1555200
  have htrace : WordTrace (prefixWord ++ tailWord_1555200) baseStart_1555200 baseEnd_1555200 := by
    simpa [prefixWord, tailWord_1555200, baseEnd_1555200] using wordTrace_append hprefix tailTrace_1555200
  have hstable : (prefixWord ++ tailWord_1555200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555200).length < 2 ^ (prefixWord ++ tailWord_1555200).sum := by decide
  have hdescent : baseEnd_1555200 < baseStart_1555200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555217 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 3]
def baseStart_1555217 : Nat := 118140960795 + 1555217 * 2 ^ 59
def prefixEnd_1555217 : Nat := 4983230072969 + 3 ^ 40 * 1555217 * 2
def baseEnd_1555217 : Nat := 798573843043546940035193

theorem tailTrace_1555217 : CollatzResearch.WordTrace tailWord_1555217 prefixEnd_1555217 798573843043546940035193 := by
  unfold tailWord_1555217
  simp only [CollatzResearch.WordTrace]
  refine ⟨56723424006721893762423905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37815616004481262508282603 56723424006721893762423905)
  ·
    refine ⟨42542568005041420321817929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56723424006721893762423905 42542568005041420321817929)
    ·
      refine ⟨31906926003781065241363447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42542568005041420321817929 31906926003781065241363447)
      ·
        refine ⟨47860389005671597862045171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31906926003781065241363447 47860389005671597862045171)
        ·
          refine ⟨71790583508507396793067757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47860389005671597862045171 71790583508507396793067757)
          ·
            refine ⟨26921468815690273797400409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71790583508507396793067757 26921468815690273797400409)
            ·
              refine ⟨20191101611767705348050307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26921468815690273797400409 20191101611767705348050307)
              ·
                refine ⟨30286652417651558022075461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20191101611767705348050307 30286652417651558022075461)
                ·
                  refine ⟨5678747328309667129139149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30286652417651558022075461 5678747328309667129139149)
                  ·
                    refine ⟨2129530248116125173427181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5678747328309667129139149 2129530248116125173427181)
                    ·
                      refine ⟨798573843043546940035193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2129530248116125173427181 798573843043546940035193)
                      ·
                        rfl

theorem cell23_1555217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_1555217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555217 prefixEnd_1555217 := by exact prefixLift 1555217
  have htrace : WordTrace (prefixWord ++ tailWord_1555217) baseStart_1555217 baseEnd_1555217 := by
    simpa [prefixWord, tailWord_1555217, baseEnd_1555217] using wordTrace_append hprefix tailTrace_1555217
  have hstable : (prefixWord ++ tailWord_1555217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555217).length < 2 ^ (prefixWord ++ tailWord_1555217).sum := by decide
  have hdescent : baseEnd_1555217 < baseStart_1555217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555237 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 4, 5]
def baseStart_1555237 : Nat := 118140960795 + 1555237 * 2 ^ 59
def prefixEnd_1555237 : Nat := 4983230072969 + 3 ^ 40 * 1555237 * 2
def baseEnd_1555237 : Nat := 266194704218878953928367

theorem tailTrace_1555237 : CollatzResearch.WordTrace tailWord_1555237 prefixEnd_1555237 266194704218878953928367 := by
  unfold tailWord_1555237
  simp only [CollatzResearch.WordTrace]
  refine ⟨56724153466649437178151965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37816102311099624785434643 56724153466649437178151965)
  ·
    refine ⟨21271557549993538941806987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56724153466649437178151965 21271557549993538941806987)
    ·
      refine ⟨31907336324990308412710481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21271557549993538941806987 31907336324990308412710481)
      ·
        refine ⟨23930502243742731309532861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31907336324990308412710481 23930502243742731309532861)
        ·
          refine ⟨8973938341403524241074823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23930502243742731309532861 8973938341403524241074823)
          ·
            refine ⟨13460907512105286361612235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8973938341403524241074823 13460907512105286361612235)
            ·
              refine ⟨20191361268157929542418353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13460907512105286361612235 20191361268157929542418353)
              ·
                refine ⟨15143520951118447156813765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20191361268157929542418353 15143520951118447156813765)
                ·
                  refine ⟨2839410178334708841902581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15143520951118447156813765 2839410178334708841902581)
                  ·
                    refine ⟨266194704218878953928367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2839410178334708841902581 266194704218878953928367)
                    ·
                      rfl

theorem cell23_1555237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_1555237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555237 prefixEnd_1555237 := by exact prefixLift 1555237
  have htrace : WordTrace (prefixWord ++ tailWord_1555237) baseStart_1555237 baseEnd_1555237 := by
    simpa [prefixWord, tailWord_1555237, baseEnd_1555237] using wordTrace_append hprefix tailTrace_1555237
  have hstable : (prefixWord ++ tailWord_1555237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555237).length < 2 ^ (prefixWord ++ tailWord_1555237).sum := by decide
  have hdescent : baseEnd_1555237 < baseStart_1555237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555347 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 4]
def baseStart_1555347 : Nat := 118140960795 + 1555347 * 2 ^ 59
def prefixEnd_1555347 : Nat := 4983230072969 + 3 ^ 40 * 1555347 * 2
def baseEnd_1555347 : Nat := 798640595528631431409595

theorem tailTrace_1555347 : CollatzResearch.WordTrace tailWord_1555347 prefixEnd_1555347 798640595528631431409595 := by
  unfold tailWord_1555347
  simp only [CollatzResearch.WordTrace]
  refine ⟨56728165496250925964656295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37818776997500617309770863 56728165496250925964656295)
  ·
    refine ⟨85092248244376388946984443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56728165496250925964656295 85092248244376388946984443)
    ·
      refine ⟨127638372366564583420476665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85092248244376388946984443 127638372366564583420476665)
      ·
        refine ⟨95728779274923437565357499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127638372366564583420476665 95728779274923437565357499)
        ·
          refine ⟨143593168912385156348036249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95728779274923437565357499 143593168912385156348036249)
          ·
            refine ⟨107694876684288867261027187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143593168912385156348036249 107694876684288867261027187)
            ·
              refine ⟨161542315026433300891540781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107694876684288867261027187 161542315026433300891540781)
              ·
                refine ⟨60578368134912487834327793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161542315026433300891540781 60578368134912487834327793)
                ·
                  refine ⟨45433776101184365875745845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60578368134912487834327793 45433776101184365875745845)
                  ·
                    refine ⟨4259416509486034300851173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45433776101184365875745845 4259416509486034300851173)
                    ·
                      refine ⟨798640595528631431409595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4259416509486034300851173 798640595528631431409595)
                      ·
                        rfl

theorem cell23_1555347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_1555347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555347 prefixEnd_1555347 := by exact prefixLift 1555347
  have htrace : WordTrace (prefixWord ++ tailWord_1555347) baseStart_1555347 baseEnd_1555347 := by
    simpa [prefixWord, tailWord_1555347, baseEnd_1555347] using wordTrace_append hprefix tailTrace_1555347
  have hstable : (prefixWord ++ tailWord_1555347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555347).length < 2 ^ (prefixWord ++ tailWord_1555347).sum := by decide
  have hdescent : baseEnd_1555347 < baseStart_1555347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555361 : List Nat := [1, 2, 3, 4, 1, 1, 1, 4, 1, 5]
def baseStart_1555361 : Nat := 118140960795 + 1555361 * 2 ^ 59
def prefixEnd_1555361 : Nat := 4983230072969 + 3 ^ 40 * 1555361 * 2
def baseEnd_1555361 : Nat := 266215928085931458878177

theorem tailTrace_1555361 : CollatzResearch.WordTrace tailWord_1555361 prefixEnd_1555361 266215928085931458878177 := by
  unfold tailWord_1555361
  simp only [CollatzResearch.WordTrace]
  refine ⟨56728676118200206355665937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37819117412133470903777291 56728676118200206355665937)
  ·
    refine ⟨42546507088650154766749453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56728676118200206355665937 42546507088650154766749453)
    ·
      refine ⟨15954940158243808037531045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42546507088650154766749453 15954940158243808037531045)
      ·
        refine ⟨2991551279670714007037071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15954940158243808037531045 2991551279670714007037071)
        ·
          refine ⟨4487326919506071010555607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2991551279670714007037071 4487326919506071010555607)
          ·
            refine ⟨6730990379259106515833411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4487326919506071010555607 6730990379259106515833411)
            ·
              refine ⟨10096485568888659773750117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6730990379259106515833411 10096485568888659773750117)
              ·
                refine ⟨1893091044166623707578147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10096485568888659773750117 1893091044166623707578147)
                ·
                  refine ⟨2839636566249935561367221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1893091044166623707578147 2839636566249935561367221)
                  ·
                    refine ⟨266215928085931458878177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2839636566249935561367221 266215928085931458878177)
                    ·
                      rfl

theorem cell23_1555361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_1555361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555361 prefixEnd_1555361 := by exact prefixLift 1555361
  have htrace : WordTrace (prefixWord ++ tailWord_1555361) baseStart_1555361 baseEnd_1555361 := by
    simpa [prefixWord, tailWord_1555361, baseEnd_1555361] using wordTrace_append hprefix tailTrace_1555361
  have hstable : (prefixWord ++ tailWord_1555361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555361).length < 2 ^ (prefixWord ++ tailWord_1555361).sum := by decide
  have hdescent : baseEnd_1555361 < baseStart_1555361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555381 : List Nat := [1, 3, 3, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_1555381 : Nat := 118140960795 + 1555381 * 2 ^ 59
def prefixEnd_1555381 : Nat := 4983230072969 + 3 ^ 40 * 1555381 * 2
def baseEnd_1555381 : Nat := 798658053870884298384439

theorem tailTrace_1555381 : CollatzResearch.WordTrace tailWord_1555381 prefixEnd_1555381 798658053870884298384439 := by
  unfold tailWord_1555381
  simp only [CollatzResearch.WordTrace]
  refine ⟨56729405578127749771393997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37819603718751833180929331 56729405578127749771393997)
  ·
    refine ⟨21273527091797906164272749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56729405578127749771393997 21273527091797906164272749)
    ·
      refine ⟨7977572659424214811602281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21273527091797906164272749 7977572659424214811602281)
      ·
        refine ⟨5983179494568161108701711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7977572659424214811602281 5983179494568161108701711)
        ·
          refine ⟨8974769241852241663052567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5983179494568161108701711 8974769241852241663052567)
          ·
            refine ⟨13462153862778362494578851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8974769241852241663052567 13462153862778362494578851)
            ·
              refine ⟨20193230794167543741868277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13462153862778362494578851 20193230794167543741868277)
              ·
                refine ⟨1893115386953207225800151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20193230794167543741868277 1893115386953207225800151)
                ·
                  refine ⟨2839673080429810838700227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1893115386953207225800151 2839673080429810838700227)
                  ·
                    refine ⟨4259509620644716258050341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2839673080429810838700227 4259509620644716258050341)
                    ·
                      refine ⟨798658053870884298384439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4259509620644716258050341 798658053870884298384439)
                      ·
                        rfl

theorem cell23_1555381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_1555381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555381 prefixEnd_1555381 := by exact prefixLift 1555381
  have htrace : WordTrace (prefixWord ++ tailWord_1555381) baseStart_1555381 baseEnd_1555381 := by
    simpa [prefixWord, tailWord_1555381, baseEnd_1555381] using wordTrace_append hprefix tailTrace_1555381
  have hstable : (prefixWord ++ tailWord_1555381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555381).length < 2 ^ (prefixWord ++ tailWord_1555381).sum := by decide
  have hdescent : baseEnd_1555381 < baseStart_1555381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555384 : List Nat := [2, 1, 2, 1, 2, 4, 1, 3, 1, 1, 5]
def baseStart_1555384 : Nat := 118140960795 + 1555384 * 2 ^ 59
def prefixEnd_1555384 : Nat := 4983230072969 + 3 ^ 40 * 1555384 * 2
def baseEnd_1555384 : Nat := 798659594312847786646925

theorem tailTrace_1555384 : CollatzResearch.WordTrace tailWord_1555384 prefixEnd_1555384 798659594312847786646925 := by
  unfold tailWord_1555384
  simp only [CollatzResearch.WordTrace]
  refine ⟨28364757498558440641876603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37819676664744587522502137 28364757498558440641876603)
  ·
    refine ⟨42547136247837660962814905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28364757498558440641876603 42547136247837660962814905)
    ·
      refine ⟨31910352185878245722111179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42547136247837660962814905 31910352185878245722111179)
      ·
        refine ⟨47865528278817368583166769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31910352185878245722111179 47865528278817368583166769)
        ·
          refine ⟨35899146209113026437375077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47865528278817368583166769 35899146209113026437375077)
          ·
            refine ⟨6731089914208692457007827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35899146209113026437375077 6731089914208692457007827)
            ·
              refine ⟨10096634871313038685511741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6731089914208692457007827 10096634871313038685511741)
              ·
                refine ⟨3786238076742389507066903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10096634871313038685511741 3786238076742389507066903)
                ·
                  refine ⟨5679357115113584260600355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3786238076742389507066903 5679357115113584260600355)
                  ·
                    refine ⟨8519035672670376390900533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5679357115113584260600355 8519035672670376390900533)
                    ·
                      refine ⟨798659594312847786646925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8519035672670376390900533 798659594312847786646925)
                      ·
                        rfl

theorem cell23_1555384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_1555384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555384 prefixEnd_1555384 := by exact prefixLift 1555384
  have htrace : WordTrace (prefixWord ++ tailWord_1555384) baseStart_1555384 baseEnd_1555384 := by
    simpa [prefixWord, tailWord_1555384, baseEnd_1555384] using wordTrace_append hprefix tailTrace_1555384
  have hstable : (prefixWord ++ tailWord_1555384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555384).length < 2 ^ (prefixWord ++ tailWord_1555384).sum := by decide
  have hdescent : baseEnd_1555384 < baseStart_1555384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555404 : List Nat := [2, 2, 1, 4, 1, 1, 4, 8]
def baseStart_1555404 : Nat := 118140960795 + 1555404 * 2 ^ 59
def prefixEnd_1555404 : Nat := 4983230072969 + 3 ^ 40 * 1555404 * 2
def baseEnd_1555404 : Nat := 29580365330590285496179

theorem tailTrace_1555404 : CollatzResearch.WordTrace tailWord_1555404 prefixEnd_1555404 29580365330590285496179 := by
  unfold tailWord_1555404
  simp only [CollatzResearch.WordTrace]
  refine ⟨28365122228522212349740633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37820162971362949799654177 28365122228522212349740633)
  ·
    refine ⟨21273841671391659262305475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28365122228522212349740633 21273841671391659262305475)
    ·
      refine ⟨31910762507087488893458213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21273841671391659262305475 31910762507087488893458213)
      ·
        refine ⟨5983267970078904167523415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31910762507087488893458213 5983267970078904167523415)
        ·
          refine ⟨8974901955118356251285123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5983267970078904167523415 8974901955118356251285123)
          ·
            refine ⟨13462352932677534376927685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8974901955118356251285123 13462352932677534376927685)
            ·
              refine ⟨2524191174877037695673941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13462352932677534376927685 2524191174877037695673941)
              ·
                refine ⟨29580365330590285496179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2524191174877037695673941 29580365330590285496179)
                ·
                  rfl

theorem cell23_1555404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 8].length) (baseStart_1555404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555404 prefixEnd_1555404 := by exact prefixLift 1555404
  have htrace : WordTrace (prefixWord ++ tailWord_1555404) baseStart_1555404 baseEnd_1555404 := by
    simpa [prefixWord, tailWord_1555404, baseEnd_1555404] using wordTrace_append hprefix tailTrace_1555404
  have hstable : (prefixWord ++ tailWord_1555404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555404).length < 2 ^ (prefixWord ++ tailWord_1555404).sum := by decide
  have hdescent : baseEnd_1555404 < baseStart_1555404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555418 : List Nat := [3, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3]
def baseStart_1555418 : Nat := 118140960795 + 1555418 * 2 ^ 59
def prefixEnd_1555418 : Nat := 4983230072969 + 3 ^ 40 * 1555418 * 2
def baseEnd_1555418 : Nat := 798677052655100653621769

theorem tailTrace_1555418 : CollatzResearch.WordTrace tailWord_1555418 prefixEnd_1555418 798677052655100653621769 := by
  unfold tailWord_1555418
  simp only [CollatzResearch.WordTrace]
  refine ⟨14182688769748426272622727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37820503385995803393660605 14182688769748426272622727)
  ·
    refine ⟨21274033154622639408934091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14182688769748426272622727 21274033154622639408934091)
    ·
      refine ⟨31911049731933959113401137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21274033154622639408934091 31911049731933959113401137)
      ·
        refine ⟨23933287298950469335050853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31911049731933959113401137 23933287298950469335050853)
        ·
          refine ⟨4487491368553213000322035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23933287298950469335050853 4487491368553213000322035)
          ·
            refine ⟨6731237052829819500483053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4487491368553213000322035 6731237052829819500483053)
            ·
              refine ⟨2524213894811182312681145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6731237052829819500483053 2524213894811182312681145)
              ·
                refine ⟨1893160421108386734510859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2524213894811182312681145 1893160421108386734510859)
                ·
                  refine ⟨2839740631662580101766289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1893160421108386734510859 2839740631662580101766289)
                  ·
                    refine ⟨2129805473746935076324717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2839740631662580101766289 2129805473746935076324717)
                    ·
                      refine ⟨798677052655100653621769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2129805473746935076324717 798677052655100653621769)
                      ·
                        rfl

theorem cell23_1555418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_1555418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555418 prefixEnd_1555418 := by exact prefixLift 1555418
  have htrace : WordTrace (prefixWord ++ tailWord_1555418) baseStart_1555418 baseEnd_1555418 := by
    simpa [prefixWord, tailWord_1555418, baseEnd_1555418] using wordTrace_append hprefix tailTrace_1555418
  have hstable : (prefixWord ++ tailWord_1555418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555418).length < 2 ^ (prefixWord ++ tailWord_1555418).sum := by decide
  have hdescent : baseEnd_1555418 < baseStart_1555418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555431 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_1555431 : Nat := 118140960795 + 1555431 * 2 ^ 59
def prefixEnd_1555431 : Nat := 4983230072969 + 3 ^ 40 * 1555431 * 2
def baseEnd_1555431 : Nat := 798683727903609102759209

theorem tailTrace_1555431 : CollatzResearch.WordTrace tailWord_1555431 prefixEnd_1555431 798683727903609102759209 := by
  unfold tailWord_1555431
  simp only [CollatzResearch.WordTrace]
  refine ⟨56731229227946608310714147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37820819485297738873809431 56731229227946608310714147)
  ·
    refine ⟨85096843841919912466071221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56731229227946608310714147 85096843841919912466071221)
    ·
      refine ⟨7977829110179991793694177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85096843841919912466071221 7977829110179991793694177)
      ·
        refine ⟨5983371832634993845270633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7977829110179991793694177 5983371832634993845270633)
        ·
          refine ⟨4487528874476245383952975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5983371832634993845270633 4487528874476245383952975)
          ·
            refine ⟨6731293311714368075929463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4487528874476245383952975 6731293311714368075929463)
            ·
              refine ⟨10096939967571552113894195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6731293311714368075929463 10096939967571552113894195)
              ·
                refine ⟨15145409951357328170841293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10096939967571552113894195 15145409951357328170841293)
                ·
                  refine ⟨5679528731758998064065485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15145409951357328170841293 5679528731758998064065485)
                  ·
                    refine ⟨2129823274409624274024557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5679528731758998064065485 2129823274409624274024557)
                    ·
                      refine ⟨798683727903609102759209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2129823274409624274024557 798683727903609102759209)
                      ·
                        rfl

theorem cell23_1555431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_1555431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555431 prefixEnd_1555431 := by exact prefixLift 1555431
  have htrace : WordTrace (prefixWord ++ tailWord_1555431) baseStart_1555431 baseEnd_1555431 := by
    simpa [prefixWord, tailWord_1555431, baseEnd_1555431] using wordTrace_append hprefix tailTrace_1555431
  have hstable : (prefixWord ++ tailWord_1555431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555431).length < 2 ^ (prefixWord ++ tailWord_1555431).sum := by decide
  have hdescent : baseEnd_1555431 < baseStart_1555431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555464 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 1, 8]
def baseStart_1555464 : Nat := 118140960795 + 1555464 * 2 ^ 59
def prefixEnd_1555464 : Nat := 4983230072969 + 3 ^ 40 * 1555464 * 2
def baseEnd_1555464 : Nat := 266233557588402491215519

theorem tailTrace_1555464 : CollatzResearch.WordTrace tailWord_1555464 prefixEnd_1555464 266233557588402491215519 := by
  unfold tailWord_1555464
  simp only [CollatzResearch.WordTrace]
  refine ⟨28366216418413527473332723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37821621891218036631110297 28366216418413527473332723)
  ·
    refine ⟨42549324627620291209999085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28366216418413527473332723 42549324627620291209999085)
    ·
      refine ⟨15955996735357609203749657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42549324627620291209999085 15955996735357609203749657)
      ·
        refine ⟨11966997551518206902812243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15955996735357609203749657 11966997551518206902812243)
        ·
          refine ⟨17950496327277310354218365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11966997551518206902812243 17950496327277310354218365)
          ·
            refine ⟨6731436122728991382831887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17950496327277310354218365 6731436122728991382831887)
            ·
              refine ⟨10097154184093487074247831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6731436122728991382831887 10097154184093487074247831)
              ·
                refine ⟨15145731276140230611371747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10097154184093487074247831 15145731276140230611371747)
                ·
                  refine ⟨22718596914210345917057621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15145731276140230611371747 22718596914210345917057621)
                  ·
                    refine ⟨266233557588402491215519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22718596914210345917057621 266233557588402491215519)
                    ·
                      rfl

theorem cell23_1555464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_1555464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555464 prefixEnd_1555464 := by exact prefixLift 1555464
  have htrace : WordTrace (prefixWord ++ tailWord_1555464) baseStart_1555464 baseEnd_1555464 := by
    simpa [prefixWord, tailWord_1555464, baseEnd_1555464] using wordTrace_append hprefix tailTrace_1555464
  have hstable : (prefixWord ++ tailWord_1555464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555464).length < 2 ^ (prefixWord ++ tailWord_1555464).sum := by decide
  have hdescent : baseEnd_1555464 < baseStart_1555464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555492 : List Nat := [2, 3, 1, 4, 1, 1, 4, 1, 1, 3, 2]
def baseStart_1555492 : Nat := 118140960795 + 1555492 * 2 ^ 59
def prefixEnd_1555492 : Nat := 4983230072969 + 3 ^ 40 * 1555492 * 2
def baseEnd_1555492 : Nat := 798715050223533364096429

theorem tailTrace_1555492 : CollatzResearch.WordTrace tailWord_1555492 prefixEnd_1555492 798715050223533364096429 := by
  unfold tailWord_1555492
  simp only [CollatzResearch.WordTrace]
  refine ⟨28366727040362807864342365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37822302720483743819123153 28366727040362807864342365)
  ·
    refine ⟨10637522640136052949128387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28366727040362807864342365 10637522640136052949128387)
    ·
      refine ⟨15956283960204079423692581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10637522640136052949128387 15956283960204079423692581)
      ·
        refine ⟨2991803242538264891942359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15956283960204079423692581 2991803242538264891942359)
        ·
          refine ⟨4487704863807397337913539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2991803242538264891942359 4487704863807397337913539)
          ·
            refine ⟨6731557295711096006870309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4487704863807397337913539 6731557295711096006870309)
            ·
              refine ⟨1262166992945830501288183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6731557295711096006870309 1262166992945830501288183)
              ·
                refine ⟨1893250489418745751932275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262166992945830501288183 1893250489418745751932275)
                ·
                  refine ⟨2839875734128118627898413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1893250489418745751932275 2839875734128118627898413)
                  ·
                    refine ⟨1064953400298044485461905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2839875734128118627898413 1064953400298044485461905)
                    ·
                      refine ⟨798715050223533364096429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1064953400298044485461905 798715050223533364096429)
                      ·
                        rfl

theorem cell23_1555492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_1555492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555492 prefixEnd_1555492 := by exact prefixLift 1555492
  have htrace : WordTrace (prefixWord ++ tailWord_1555492) baseStart_1555492 baseEnd_1555492 := by
    simpa [prefixWord, tailWord_1555492, baseEnd_1555492] using wordTrace_append hprefix tailTrace_1555492
  have hstable : (prefixWord ++ tailWord_1555492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555492).length < 2 ^ (prefixWord ++ tailWord_1555492).sum := by decide
  have hdescent : baseEnd_1555492 < baseStart_1555492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555518 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_1555518 : Nat := 118140960795 + 1555518 * 2 ^ 59
def prefixEnd_1555518 : Nat := 4983230072969 + 3 ^ 40 * 1555518 * 2
def baseEnd_1555518 : Nat := 798728400720550262371309

theorem tailTrace_1555518 : CollatzResearch.WordTrace tailWord_1555518 prefixEnd_1555518 798728400720550262371309 := by
  unfold tailWord_1555518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7091800297328927771141401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37822934919087614779420805 7091800297328927771141401)
  ·
    refine ⟨5318850222996695828356051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7091800297328927771141401 5318850222996695828356051)
    ·
      refine ⟨7978275334495043742534077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5318850222996695828356051 7978275334495043742534077)
      ·
        refine ⟨2991853250435641403450279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7978275334495043742534077 2991853250435641403450279)
        ·
          refine ⟨4487779875653462105175419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2991853250435641403450279 4487779875653462105175419)
          ·
            refine ⟨6731669813480193157763129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4487779875653462105175419 6731669813480193157763129)
            ·
              refine ⟨5048752360110144868322347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6731669813480193157763129 5048752360110144868322347)
              ·
                refine ⟨7573128540165217302483521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5048752360110144868322347 7573128540165217302483521)
                ·
                  refine ⟨5679846405123912976862641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7573128540165217302483521 5679846405123912976862641)
                  ·
                    refine ⟨4259884803842934732646981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5679846405123912976862641 4259884803842934732646981)
                    ·
                      refine ⟨798728400720550262371309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4259884803842934732646981 798728400720550262371309)
                      ·
                        rfl

theorem cell23_1555518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_1555518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555518 prefixEnd_1555518 := by exact prefixLift 1555518
  have htrace : WordTrace (prefixWord ++ tailWord_1555518) baseStart_1555518 baseEnd_1555518 := by
    simpa [prefixWord, tailWord_1555518, baseEnd_1555518] using wordTrace_append hprefix tailTrace_1555518
  have hstable : (prefixWord ++ tailWord_1555518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555518).length < 2 ^ (prefixWord ++ tailWord_1555518).sum := by decide
  have hdescent : baseEnd_1555518 < baseStart_1555518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555541 : List Nat := [1, 3, 2, 2, 1, 2, 2, 3, 2, 5]
def baseStart_1555541 : Nat := 118140960795 + 1555541 * 2 ^ 59
def prefixEnd_1555541 : Nat := 4983230072969 + 3 ^ 40 * 1555541 * 2
def baseEnd_1555541 : Nat := 266246736925201224127901

theorem tailTrace_1555541 : CollatzResearch.WordTrace tailWord_1555541 prefixEnd_1555541 266246736925201224127901 := by
  unfold tailWord_1555541
  simp only [CollatzResearch.WordTrace]
  refine ⟨56735241257548097097218477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37823494171698731398145651 56735241257548097097218477)
  ·
    refine ⟨21275715471580536411456929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56735241257548097097218477 21275715471580536411456929)
    ·
      refine ⟨15956786603685402308592697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21275715471580536411456929 15956786603685402308592697)
      ·
        refine ⟨11967589952764051731444523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15956786603685402308592697 11967589952764051731444523)
        ·
          refine ⟨17951384929146077597166785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11967589952764051731444523 17951384929146077597166785)
          ·
            refine ⟨13463538696859558197875089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17951384929146077597166785 13463538696859558197875089)
            ·
              refine ⟨10097654022644668648406317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13463538696859558197875089 10097654022644668648406317)
              ·
                refine ⟨3786620258491750743152369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10097654022644668648406317 3786620258491750743152369)
                ·
                  refine ⟨2839965193868813057364277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3786620258491750743152369 2839965193868813057364277)
                  ·
                    refine ⟨266246736925201224127901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2839965193868813057364277 266246736925201224127901)
                    ·
                      rfl

theorem cell23_1555541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_1555541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555541 prefixEnd_1555541 := by exact prefixLift 1555541
  have htrace : WordTrace (prefixWord ++ tailWord_1555541) baseStart_1555541 baseEnd_1555541 := by
    simpa [prefixWord, tailWord_1555541, baseEnd_1555541] using wordTrace_append hprefix tailTrace_1555541
  have hstable : (prefixWord ++ tailWord_1555541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555541).length < 2 ^ (prefixWord ++ tailWord_1555541).sum := by decide
  have hdescent : baseEnd_1555541 < baseStart_1555541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555561 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 4, 1, 4]
def baseStart_1555561 : Nat := 118140960795 + 1555561 * 2 ^ 59
def prefixEnd_1555561 : Nat := 4983230072969 + 3 ^ 40 * 1555561 * 2
def baseEnd_1555561 : Nat := 798750480388693594133611

theorem tailTrace_1555561 : CollatzResearch.WordTrace tailWord_1555561 prefixEnd_1555561 798750480388693594133611 := by
  unfold tailWord_1555561
  simp only [CollatzResearch.WordTrace]
  refine ⟨56735970717475640512946537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37823980478317093675297691 56735970717475640512946537)
  ·
    refine ⟨42551978038106730384709903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56735970717475640512946537 42551978038106730384709903)
    ·
      refine ⟨63827967057160095577064855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42551978038106730384709903 63827967057160095577064855)
      ·
        refine ⟨95741950585740143365597283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63827967057160095577064855 95741950585740143365597283)
        ·
          refine ⟨143612925878610215048395925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95741950585740143365597283 143612925878610215048395925)
          ·
            refine ⟨6731855900559853830393559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 143612925878610215048395925 6731855900559853830393559)
            ·
              refine ⟨10097783850839780745590339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6731855900559853830393559 10097783850839780745590339)
              ·
                refine ⟨15146675776259671118385509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10097783850839780745590339 15146675776259671118385509)
                ·
                  refine ⟨2840001708048688334697283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15146675776259671118385509 2840001708048688334697283)
                  ·
                    refine ⟨4260002562073032502045925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2840001708048688334697283 4260002562073032502045925)
                    ·
                      refine ⟨798750480388693594133611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4260002562073032502045925 798750480388693594133611)
                      ·
                        rfl

theorem cell23_1555561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 1, 4].length) (baseStart_1555561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555561 prefixEnd_1555561 := by exact prefixLift 1555561
  have htrace : WordTrace (prefixWord ++ tailWord_1555561) baseStart_1555561 baseEnd_1555561 := by
    simpa [prefixWord, tailWord_1555561, baseEnd_1555561] using wordTrace_append hprefix tailTrace_1555561
  have hstable : (prefixWord ++ tailWord_1555561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555561).length < 2 ^ (prefixWord ++ tailWord_1555561).sum := by decide
  have hdescent : baseEnd_1555561 < baseStart_1555561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555573 : List Nat := [1, 3, 4, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_1555573 : Nat := 118140960795 + 1555573 * 2 ^ 59
def prefixEnd_1555573 : Nat := 4983230072969 + 3 ^ 40 * 1555573 * 2
def baseEnd_1555573 : Nat := 798756642156547547183557

theorem tailTrace_1555573 : CollatzResearch.WordTrace tailWord_1555573 prefixEnd_1555573 798756642156547547183557 := by
  unfold tailWord_1555573
  simp only [CollatzResearch.WordTrace]
  refine ⟨56736408393432166562383373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37824272262288111041588915 56736408393432166562383373)
  ·
    refine ⟨21276153147537062460893765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56736408393432166562383373 21276153147537062460893765)
    ·
      refine ⟨3989278715163199211417581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21276153147537062460893765 3989278715163199211417581)
      ·
        refine ⟨1495979518186199704281593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3989278715163199211417581 1495979518186199704281593)
        ·
          refine ⟨1121984638639649778211195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1495979518186199704281593 1121984638639649778211195)
          ·
            refine ⟨1682976957959474667316793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1121984638639649778211195 1682976957959474667316793)
            ·
              refine ⟨1262232718469606000487595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1682976957959474667316793 1262232718469606000487595)
              ·
                refine ⟨1893349077704409000731393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262232718469606000487595 1893349077704409000731393)
                ·
                  refine ⟨1420011808278306750548545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1893349077704409000731393 1420011808278306750548545)
                  ·
                    refine ⟨1065008856208730062911409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1420011808278306750548545 1065008856208730062911409)
                    ·
                      refine ⟨798756642156547547183557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1065008856208730062911409 798756642156547547183557)
                      ·
                        rfl

theorem cell23_1555573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_1555573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555573 prefixEnd_1555573 := by exact prefixLift 1555573
  have htrace : WordTrace (prefixWord ++ tailWord_1555573) baseStart_1555573 baseEnd_1555573 := by
    simpa [prefixWord, tailWord_1555573, baseEnd_1555573] using wordTrace_append hprefix tailTrace_1555573
  have hstable : (prefixWord ++ tailWord_1555573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555573).length < 2 ^ (prefixWord ++ tailWord_1555573).sum := by decide
  have hdescent : baseEnd_1555573 < baseStart_1555573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555631 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 3, 5]
def baseStart_1555631 : Nat := 118140960795 + 1555631 * 2 ^ 59
def prefixEnd_1555631 : Nat := 4983230072969 + 3 ^ 40 * 1555631 * 2
def baseEnd_1555631 : Nat := 266262141344836106752763

theorem tailTrace_1555631 : CollatzResearch.WordTrace tailWord_1555631 prefixEnd_1555631 266262141344836106752763 := by
  unfold tailWord_1555631
  simp only [CollatzResearch.WordTrace]
  refine ⟨56738523827222042467994747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37825682551481361645329831 56738523827222042467994747)
  ·
    refine ⟨85107785740833063701992121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56738523827222042467994747 85107785740833063701992121)
    ·
      refine ⟨63830839305624797776494091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85107785740833063701992121 63830839305624797776494091)
      ·
        refine ⟨95746258958437196664741137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63830839305624797776494091 95746258958437196664741137)
        ·
          refine ⟨71809694218827897498555853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95746258958437196664741137 71809694218827897498555853)
          ·
            refine ⟨26928635332060461561958445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71809694218827897498555853 26928635332060461561958445)
            ·
              refine ⟨10098238249522673085734417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26928635332060461561958445 10098238249522673085734417)
              ·
                refine ⟨7573678687142004814300813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10098238249522673085734417 7573678687142004814300813)
                ·
                  refine ⟨2840129507678251805362805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7573678687142004814300813 2840129507678251805362805)
                  ·
                    refine ⟨266262141344836106752763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2840129507678251805362805 266262141344836106752763)
                    ·
                      rfl

theorem cell23_1555631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 5].length) (baseStart_1555631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555631 prefixEnd_1555631 := by exact prefixLift 1555631
  have htrace : WordTrace (prefixWord ++ tailWord_1555631) baseStart_1555631 baseEnd_1555631 := by
    simpa [prefixWord, tailWord_1555631, baseEnd_1555631] using wordTrace_append hprefix tailTrace_1555631
  have hstable : (prefixWord ++ tailWord_1555631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555631).length < 2 ^ (prefixWord ++ tailWord_1555631).sum := by decide
  have hdescent : baseEnd_1555631 < baseStart_1555631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555688 : List Nat := [2, 1, 4, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_1555688 : Nat := 118140960795 + 1555688 * 2 ^ 59
def prefixEnd_1555688 : Nat := 4983230072969 + 3 ^ 40 * 1555688 * 2
def baseEnd_1555688 : Nat := 798815692431814597245527

theorem tailTrace_1555688 : CollatzResearch.WordTrace tailWord_1555688 prefixEnd_1555688 798815692431814597245527 := by
  unfold tailWord_1555688
  simp only [CollatzResearch.WordTrace]
  refine ⟨28370301394007770601409859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37827068525343694135213145 28370301394007770601409859)
  ·
    refine ⟨42555452091011655902114789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28370301394007770601409859 42555452091011655902114789)
    ·
      refine ⟨7979147267064685481646523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42555452091011655902114789 7979147267064685481646523)
      ·
        refine ⟨11968720900597028222469785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7979147267064685481646523 11968720900597028222469785)
        ·
          refine ⟨8976540675447771166852339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11968720900597028222469785 8976540675447771166852339)
          ·
            refine ⟨13464811013171656750278509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8976540675447771166852339 13464811013171656750278509)
            ·
              refine ⟨5049304129939371281354441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13464811013171656750278509 5049304129939371281354441)
              ·
                refine ⟨3786978097454528461015831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5049304129939371281354441 3786978097454528461015831)
                ·
                  refine ⟨5680467146181792691523747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3786978097454528461015831 5680467146181792691523747)
                  ·
                    refine ⟨8520700719272689037285621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5680467146181792691523747 8520700719272689037285621)
                    ·
                      refine ⟨798815692431814597245527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8520700719272689037285621 798815692431814597245527)
                      ·
                        rfl

theorem cell23_1555688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_1555688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555688 prefixEnd_1555688 := by exact prefixLift 1555688
  have htrace : WordTrace (prefixWord ++ tailWord_1555688) baseStart_1555688 baseEnd_1555688 := by
    simpa [prefixWord, tailWord_1555688, baseEnd_1555688] using wordTrace_append hprefix tailTrace_1555688
  have hstable : (prefixWord ++ tailWord_1555688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555688).length < 2 ^ (prefixWord ++ tailWord_1555688).sum := by decide
  have hdescent : baseEnd_1555688 < baseStart_1555688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555695 : List Nat := [1, 1, 2, 1, 7, 2, 1, 1, 1, 6]
def baseStart_1555695 : Nat := 118140960795 + 1555695 * 2 ^ 59
def prefixEnd_1555695 : Nat := 4983230072969 + 3 ^ 40 * 1555695 * 2
def baseEnd_1555695 : Nat := 266273095598798689952665

theorem tailTrace_1555695 : CollatzResearch.WordTrace tailWord_1555695 prefixEnd_1555695 266273095598798689952665 := by
  unfold tailWord_1555695
  simp only [CollatzResearch.WordTrace]
  refine ⟨56740858098990181398324539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37827238732660120932216359 56740858098990181398324539)
  ·
    refine ⟨85111287148485272097486809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56740858098990181398324539 85111287148485272097486809)
    ·
      refine ⟨63833465361363954073115107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85111287148485272097486809 63833465361363954073115107)
      ·
        refine ⟨95750198042045931109672661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63833465361363954073115107 95750198042045931109672661)
        ·
          refine ⟨2244145266610451510382953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 95750198042045931109672661 2244145266610451510382953)
          ·
            refine ⟨1683108949957838632787215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2244145266610451510382953 1683108949957838632787215)
            ·
              refine ⟨2524663424936757949180823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1683108949957838632787215 2524663424936757949180823)
              ·
                refine ⟨3786995137405136923771235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2524663424936757949180823 3786995137405136923771235)
                ·
                  refine ⟨5680492706107705385656853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3786995137405136923771235 5680492706107705385656853)
                  ·
                    refine ⟨266273095598798689952665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5680492706107705385656853 266273095598798689952665)
                    ·
                      rfl

theorem cell23_1555695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 6].length) (baseStart_1555695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555695 prefixEnd_1555695 := by exact prefixLift 1555695
  have htrace : WordTrace (prefixWord ++ tailWord_1555695) baseStart_1555695 baseEnd_1555695 := by
    simpa [prefixWord, tailWord_1555695, baseEnd_1555695] using wordTrace_append hprefix tailTrace_1555695
  have hstable : (prefixWord ++ tailWord_1555695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555695).length < 2 ^ (prefixWord ++ tailWord_1555695).sum := by decide
  have hdescent : baseEnd_1555695 < baseStart_1555695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555705 : List Nat := [1, 2, 1, 3, 1, 1, 6, 2, 1, 2, 3]
def baseStart_1555705 : Nat := 118140960795 + 1555705 * 2 ^ 59
def prefixEnd_1555705 : Nat := 4983230072969 + 3 ^ 40 * 1555705 * 2
def baseEnd_1555705 : Nat := 798824421602941030732949

theorem tailTrace_1555705 : CollatzResearch.WordTrace tailWord_1555705 prefixEnd_1555705 798824421602941030732949 := by
  unfold tailWord_1555705
  simp only [CollatzResearch.WordTrace]
  refine ⟨56741222828953953106188569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37827481885969302070792379 56741222828953953106188569)
  ·
    refine ⟨42555917121715464829641427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56741222828953953106188569 42555917121715464829641427)
    ·
      refine ⟨63833875682573197244462141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42555917121715464829641427 63833875682573197244462141)
      ·
        refine ⟨23937703380964948966673303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63833875682573197244462141 23937703380964948966673303)
        ·
          refine ⟨35906555071447423450009955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23937703380964948966673303 35906555071447423450009955)
          ·
            refine ⟨53859832607171135175014933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35906555071447423450009955 53859832607171135175014933)
            ·
              refine ⟨2524679653461146961328825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53859832607171135175014933 2524679653461146961328825)
              ·
                refine ⟨1893509740095860220996619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2524679653461146961328825 1893509740095860220996619)
                ·
                  refine ⟨2840264610143790331494929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1893509740095860220996619 2840264610143790331494929)
                  ·
                    refine ⟨2130198457607842748621197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2840264610143790331494929 2130198457607842748621197)
                    ·
                      refine ⟨798824421602941030732949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2130198457607842748621197 798824421602941030732949)
                      ·
                        rfl

theorem cell23_1555705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_1555705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555705 prefixEnd_1555705 := by exact prefixLift 1555705
  have htrace : WordTrace (prefixWord ++ tailWord_1555705) baseStart_1555705 baseEnd_1555705 := by
    simpa [prefixWord, tailWord_1555705, baseEnd_1555705] using wordTrace_append hprefix tailTrace_1555705
  have hstable : (prefixWord ++ tailWord_1555705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555705).length < 2 ^ (prefixWord ++ tailWord_1555705).sum := by decide
  have hdescent : baseEnd_1555705 < baseStart_1555705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555708 : List Nat := [2, 2, 2, 1, 5, 1, 1, 9]
def baseStart_1555708 : Nat := 118140960795 + 1555708 * 2 ^ 59
def prefixEnd_1555708 : Nat := 4983230072969 + 3 ^ 40 * 1555708 * 2
def baseEnd_1555708 : Nat := 29586146742403871073905

theorem tailTrace_1555708 : CollatzResearch.WordTrace tailWord_1555708 prefixEnd_1555708 29586146742403871073905 := by
  unfold tailWord_1555708
  simp only [CollatzResearch.WordTrace]
  refine ⟨28370666123971542309273889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37827554831962056412365185 28370666123971542309273889)
  ·
    refine ⟨21277999592978656731955417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28370666123971542309273889 21277999592978656731955417)
    ·
      refine ⟨15958499694733992548966563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21277999592978656731955417 15958499694733992548966563)
      ·
        refine ⟨23937749542100988823449845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15958499694733992548966563 23937749542100988823449845)
        ·
          refine ⟨2244164019571967702198423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23937749542100988823449845 2244164019571967702198423)
          ·
            refine ⟨3366246029357951553297635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244164019571967702198423 3366246029357951553297635)
            ·
              refine ⟨5049369044036927329946453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3366246029357951553297635 5049369044036927329946453)
              ·
                refine ⟨29586146742403871073905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5049369044036927329946453 29586146742403871073905)
                ·
                  rfl

theorem cell23_1555708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 9].length) (baseStart_1555708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555708 prefixEnd_1555708 := by exact prefixLift 1555708
  have htrace : WordTrace (prefixWord ++ tailWord_1555708) baseStart_1555708 baseEnd_1555708 := by
    simpa [prefixWord, tailWord_1555708, baseEnd_1555708] using wordTrace_append hprefix tailTrace_1555708
  have hstable : (prefixWord ++ tailWord_1555708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555708).length < 2 ^ (prefixWord ++ tailWord_1555708).sum := by decide
  have hdescent : baseEnd_1555708 < baseStart_1555708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555728 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 3, 9, 2]
def baseStart_1555728 : Nat := 118140960795 + 1555728 * 2 ^ 59
def prefixEnd_1555728 : Nat := 4983230072969 + 3 ^ 40 * 1555728 * 2
def baseEnd_1555728 : Nat := 798836231657994440745343

theorem tailTrace_1555728 : CollatzResearch.WordTrace tailWord_1555728 prefixEnd_1555728 798836231657994440745343 := by
  unfold tailWord_1555728
  simp only [CollatzResearch.WordTrace]
  refine ⟨28371030853935314017137919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37828041138580418689517225 28371030853935314017137919)
  ·
    refine ⟨42556546280902971025706879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28371030853935314017137919 42556546280902971025706879)
    ·
      refine ⟨63834819421354456538560319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42556546280902971025706879 63834819421354456538560319)
      ·
        refine ⟨95752229132031684807840479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63834819421354456538560319 95752229132031684807840479)
        ·
          refine ⟨143628343698047527211760719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95752229132031684807840479 143628343698047527211760719)
          ·
            refine ⟨215442515547071290817641079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143628343698047527211760719 215442515547071290817641079)
            ·
              refine ⟨323163773320606936226461619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215442515547071290817641079 323163773320606936226461619)
              ·
                refine ⟨484745659980910404339692429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323163773320606936226461619 484745659980910404339692429)
                ·
                  refine ⟨181779622492841401627384661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 484745659980910404339692429 181779622492841401627384661)
                  ·
                    refine ⟨1065114975543992587660457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 181779622492841401627384661 1065114975543992587660457)
                    ·
                      refine ⟨798836231657994440745343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1065114975543992587660457 798836231657994440745343)
                      ·
                        rfl

theorem cell23_1555728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 9, 2].length) (baseStart_1555728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555728 prefixEnd_1555728 := by exact prefixLift 1555728
  have htrace : WordTrace (prefixWord ++ tailWord_1555728) baseStart_1555728 baseEnd_1555728 := by
    simpa [prefixWord, tailWord_1555728, baseEnd_1555728] using wordTrace_append hprefix tailTrace_1555728
  have hstable : (prefixWord ++ tailWord_1555728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555728).length < 2 ^ (prefixWord ++ tailWord_1555728).sum := by decide
  have hdescent : baseEnd_1555728 < baseStart_1555728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555735 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 4, 1, 3]
def baseStart_1555735 : Nat := 118140960795 + 1555735 * 2 ^ 59
def prefixEnd_1555735 : Nat := 4983230072969 + 3 ^ 40 * 1555735 * 2
def baseEnd_1555735 : Nat := 798839826022575913357811

theorem tailTrace_1555735 : CollatzResearch.WordTrace tailWord_1555735 prefixEnd_1555735 798839826022575913357811 := by
  unfold tailWord_1555735
  simp only [CollatzResearch.WordTrace]
  refine ⟨56742317018845268229780659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37828211345896845486520439 56742317018845268229780659)
  ·
    refine ⟨85113475528267902344670989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56742317018845268229780659 85113475528267902344670989)
    ·
      refine ⟨31917553323100463379251621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85113475528267902344670989 31917553323100463379251621)
      ·
        refine ⟨5984541248081336883609679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31917553323100463379251621 5984541248081336883609679)
        ·
          refine ⟨8976811872122005325414519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5984541248081336883609679 8976811872122005325414519)
          ·
            refine ⟨13465217808183007988121779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8976811872122005325414519 13465217808183007988121779)
            ·
              refine ⟨20197826712274511982182669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13465217808183007988121779 20197826712274511982182669)
              ·
                refine ⟨7574185017102941993318501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20197826712274511982182669 7574185017102941993318501)
                ·
                  refine ⟨1420159690706801623747219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7574185017102941993318501 1420159690706801623747219)
                  ·
                    refine ⟨2130239536060202435620829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1420159690706801623747219 2130239536060202435620829)
                    ·
                      refine ⟨798839826022575913357811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2130239536060202435620829 798839826022575913357811)
                      ·
                        rfl

theorem cell23_1555735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_1555735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555735 prefixEnd_1555735 := by exact prefixLift 1555735
  have htrace : WordTrace (prefixWord ++ tailWord_1555735) baseStart_1555735 baseEnd_1555735 := by
    simpa [prefixWord, tailWord_1555735, baseEnd_1555735] using wordTrace_append hprefix tailTrace_1555735
  have hstable : (prefixWord ++ tailWord_1555735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555735).length < 2 ^ (prefixWord ++ tailWord_1555735).sum := by decide
  have hdescent : baseEnd_1555735 < baseStart_1555735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555736 : List Nat := [2, 1, 2, 3, 1, 4, 3, 2, 1, 2, 2]
def baseStart_1555736 : Nat := 118140960795 + 1555736 * 2 ^ 59
def prefixEnd_1555736 : Nat := 4983230072969 + 3 ^ 40 * 1555736 * 2
def baseEnd_1555736 : Nat := 798840339503230409445307

theorem tailTrace_1555736 : CollatzResearch.WordTrace tailWord_1555736 prefixEnd_1555736 798840339503230409445307 := by
  unfold tailWord_1555736
  simp only [CollatzResearch.WordTrace]
  refine ⟨28371176745920822700283531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37828235661227763600378041 28371176745920822700283531)
  ·
    refine ⟨42556765118881234050425297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28371176745920822700283531 42556765118881234050425297)
    ·
      refine ⟨31917573839160925537818973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42556765118881234050425297 31917573839160925537818973)
      ·
        refine ⟨11969090189685347076682115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31917573839160925537818973 11969090189685347076682115)
        ·
          refine ⟨17953635284528020615023173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11969090189685347076682115 17953635284528020615023173)
          ·
            refine ⟨3366306615849003865316845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17953635284528020615023173 3366306615849003865316845)
            ·
              refine ⟨1262364980943376449493817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3366306615849003865316845 1262364980943376449493817)
              ·
                refine ⟨946773735707532337120363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1262364980943376449493817 946773735707532337120363)
                ·
                  refine ⟨1420160603561298505680545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 946773735707532337120363 1420160603561298505680545)
                  ·
                    refine ⟨1065120452670973879260409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1420160603561298505680545 1065120452670973879260409)
                    ·
                      refine ⟨798840339503230409445307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1065120452670973879260409 798840339503230409445307)
                      ·
                        rfl

theorem cell23_1555736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_1555736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555736 prefixEnd_1555736 := by exact prefixLift 1555736
  have htrace : WordTrace (prefixWord ++ tailWord_1555736) baseStart_1555736 baseEnd_1555736 := by
    simpa [prefixWord, tailWord_1555736, baseEnd_1555736] using wordTrace_append hprefix tailTrace_1555736
  have hstable : (prefixWord ++ tailWord_1555736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555736).length < 2 ^ (prefixWord ++ tailWord_1555736).sum := by decide
  have hdescent : baseEnd_1555736 < baseStart_1555736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555742 : List Nat := [4, 3, 2, 1, 2, 1, 2, 8]
def baseStart_1555742 : Nat := 118140960795 + 1555742 * 2 ^ 59
def prefixEnd_1555742 : Nat := 4983230072969 + 3 ^ 40 * 1555742 * 2
def baseEnd_1555742 : Nat := 29586793347672495776677

theorem tailTrace_1555742 : CollatzResearch.WordTrace tailWord_1555742 prefixEnd_1555742 29586793347672495776677 := by
  unfold tailWord_1555742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7092821541227488553160685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37828381553213272283523653 7092821541227488553160685)
  ·
    refine ⟨2659808077960308207435257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7092821541227488553160685 2659808077960308207435257)
    ·
      refine ⟨1994856058470231155576443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2659808077960308207435257 1994856058470231155576443)
      ·
        refine ⟨2992284087705346733364665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1994856058470231155576443 2992284087705346733364665)
        ·
          refine ⟨2244213065779010050023499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2992284087705346733364665 2244213065779010050023499)
          ·
            refine ⟨3366319598668515075035249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244213065779010050023499 3366319598668515075035249)
            ·
              refine ⟨2524739699001386306276437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3366319598668515075035249 2524739699001386306276437)
              ·
                refine ⟨29586793347672495776677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2524739699001386306276437 29586793347672495776677)
                ·
                  rfl

theorem cell23_1555742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 8].length) (baseStart_1555742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555742 prefixEnd_1555742 := by exact prefixLift 1555742
  have htrace : WordTrace (prefixWord ++ tailWord_1555742) baseStart_1555742 baseEnd_1555742 := by
    simpa [prefixWord, tailWord_1555742, baseEnd_1555742] using wordTrace_append hprefix tailTrace_1555742
  have hstable : (prefixWord ++ tailWord_1555742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555742).length < 2 ^ (prefixWord ++ tailWord_1555742).sum := by decide
  have hdescent : baseEnd_1555742 < baseStart_1555742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555745 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 3, 3, 2]
def baseStart_1555745 : Nat := 118140960795 + 1555745 * 2 ^ 59
def prefixEnd_1555745 : Nat := 4983230072969 + 3 ^ 40 * 1555745 * 2
def baseEnd_1555745 : Nat := 798844960829120874232765

theorem tailTrace_1555745 : CollatzResearch.WordTrace tailWord_1555745 prefixEnd_1555745 798844960829120874232765 := by
  unfold tailWord_1555745
  simp only [CollatzResearch.WordTrace]
  refine ⟨56742681748809039937644689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37828454499206026625096459 56742681748809039937644689)
  ·
    refine ⟨42557011311606779953233517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56742681748809039937644689 42557011311606779953233517)
    ·
      refine ⟨15958879241852542482462569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42557011311606779953233517 15958879241852542482462569)
      ·
        refine ⟨11969159431389406861846927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15958879241852542482462569 11969159431389406861846927)
        ·
          refine ⟨17953739147084110292770391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11969159431389406861846927 17953739147084110292770391)
          ·
            refine ⟨26930608720626165439155587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17953739147084110292770391 26930608720626165439155587)
            ·
              refine ⟨40395913080939248158733381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26930608720626165439155587 40395913080939248158733381)
              ·
                refine ⟨7574233702676109029762509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40395913080939248158733381 7574233702676109029762509)
                ·
                  refine ⟨2840337638503540886160941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7574233702676109029762509 2840337638503540886160941)
                  ·
                    refine ⟨1065126614438827832310353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2840337638503540886160941 1065126614438827832310353)
                    ·
                      refine ⟨798844960829120874232765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1065126614438827832310353 798844960829120874232765)
                      ·
                        rfl

theorem cell23_1555745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_1555745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555745 prefixEnd_1555745 := by exact prefixLift 1555745
  have htrace : WordTrace (prefixWord ++ tailWord_1555745) baseStart_1555745 baseEnd_1555745 := by
    simpa [prefixWord, tailWord_1555745, baseEnd_1555745] using wordTrace_append hprefix tailTrace_1555745
  have hstable : (prefixWord ++ tailWord_1555745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555745).length < 2 ^ (prefixWord ++ tailWord_1555745).sum := by decide
  have hdescent : baseEnd_1555745 < baseStart_1555745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555746 : List Nat := [3, 3, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_1555746 : Nat := 118140960795 + 1555746 * 2 ^ 59
def prefixEnd_1555746 : Nat := 4983230072969 + 3 ^ 40 * 1555746 * 2
def baseEnd_1555746 : Nat := 266281824769925123440087

theorem tailTrace_1555746 : CollatzResearch.WordTrace tailWord_1555746 prefixEnd_1555746 266281824769925123440087 := by
  unfold tailWord_1555746
  simp only [CollatzResearch.WordTrace]
  refine ⟨14185679555451354277107773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37828478814536944738954061 14185679555451354277107773)
  ·
    refine ⟨5319629833294257853915415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14185679555451354277107773 5319629833294257853915415)
    ·
      refine ⟨7979444749941386780873123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5319629833294257853915415 7979444749941386780873123)
      ·
        refine ⟨11969167124912080171309685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7979444749941386780873123 11969167124912080171309685)
        ·
          refine ⟨1122109417960507516060283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11969167124912080171309685 1122109417960507516060283)
          ·
            refine ⟨1683164126940761274090425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1122109417960507516060283 1683164126940761274090425)
            ·
              refine ⟨1262373095205570955567819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1683164126940761274090425 1262373095205570955567819)
              ·
                refine ⟨1893559642808356433351729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262373095205570955567819 1893559642808356433351729)
                ·
                  refine ⟨1420169732106267325013797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1893559642808356433351729 1420169732106267325013797)
                  ·
                    refine ⟨266281824769925123440087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1420169732106267325013797 266281824769925123440087)
                    ·
                      rfl

theorem cell23_1555746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_1555746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555746 prefixEnd_1555746 := by exact prefixLift 1555746
  have htrace : WordTrace (prefixWord ++ tailWord_1555746) baseStart_1555746 baseEnd_1555746 := by
    simpa [prefixWord, tailWord_1555746, baseEnd_1555746] using wordTrace_append hprefix tailTrace_1555746
  have hstable : (prefixWord ++ tailWord_1555746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555746).length < 2 ^ (prefixWord ++ tailWord_1555746).sum := by decide
  have hdescent : baseEnd_1555746 < baseStart_1555746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555762 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2]
def baseStart_1555762 : Nat := 118140960795 + 1555762 * 2 ^ 59
def prefixEnd_1555762 : Nat := 4983230072969 + 3 ^ 40 * 1555762 * 2
def baseEnd_1555762 : Nat := 798853690000247307720187

theorem tailTrace_1555762 : CollatzResearch.WordTrace tailWord_1555762 prefixEnd_1555762 798853690000247307720187 := by
  unfold tailWord_1555762
  simp only [CollatzResearch.WordTrace]
  refine ⟨14185825447436862960253385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37828867859831634560675693 14185825447436862960253385)
  ·
    refine ⟨10639369085577647220190039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14185825447436862960253385 10639369085577647220190039)
    ·
      refine ⟨15959053628366470830285059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10639369085577647220190039 15959053628366470830285059)
      ·
        refine ⟨23938580442549706245427589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15959053628366470830285059 23938580442549706245427589)
        ·
          refine ⟨4488483832978069921017673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23938580442549706245427589 4488483832978069921017673)
          ·
            refine ⟨3366362874733552440763255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4488483832978069921017673 3366362874733552440763255)
            ·
              refine ⟨5049544312100328661144883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3366362874733552440763255 5049544312100328661144883)
              ·
                refine ⟨7574316468150492991717325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5049544312100328661144883 7574316468150492991717325)
                ·
                  refine ⟨2840368675556434871893997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7574316468150492991717325 2840368675556434871893997)
                  ·
                    refine ⟨1065138253333663076960249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2840368675556434871893997 1065138253333663076960249)
                    ·
                      refine ⟨798853690000247307720187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1065138253333663076960249 798853690000247307720187)
                      ·
                        rfl

theorem cell23_1555762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_1555762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555762 prefixEnd_1555762 := by exact prefixLift 1555762
  have htrace : WordTrace (prefixWord ++ tailWord_1555762) baseStart_1555762 baseEnd_1555762 := by
    simpa [prefixWord, tailWord_1555762, baseEnd_1555762] using wordTrace_append hprefix tailTrace_1555762
  have hstable : (prefixWord ++ tailWord_1555762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555762).length < 2 ^ (prefixWord ++ tailWord_1555762).sum := by decide
  have hdescent : baseEnd_1555762 < baseStart_1555762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555771 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 6]
def baseStart_1555771 : Nat := 118140960795 + 1555771 * 2 ^ 59
def prefixEnd_1555771 : Nat := 4983230072969 + 3 ^ 40 * 1555771 * 2
def baseEnd_1555771 : Nat := 798858311326137772507645

theorem tailTrace_1555771 : CollatzResearch.WordTrace tailWord_1555771 prefixEnd_1555771 798858311326137772507645 := by
  unfold tailWord_1555771
  simp only [CollatzResearch.WordTrace]
  refine ⟨56743630046714846378091167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37829086697809897585394111 56743630046714846378091167)
  ·
    refine ⟨85115445070072269567136751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56743630046714846378091167 85115445070072269567136751)
    ·
      refine ⟨127673167605108404350705127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85115445070072269567136751 127673167605108404350705127)
      ·
        refine ⟨191509751407662606526057691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127673167605108404350705127 191509751407662606526057691)
        ·
          refine ⟨287264627111493909789086537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191509751407662606526057691 287264627111493909789086537)
          ·
            refine ⟨215448470333620432341814903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287264627111493909789086537 215448470333620432341814903)
            ·
              refine ⟨323172705500430648512722355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215448470333620432341814903 323172705500430648512722355)
              ·
                refine ⟨484759058250645972769083533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323172705500430648512722355 484759058250645972769083533)
                ·
                  refine ⟨181784646843992239788406325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 484759058250645972769083533 181784646843992239788406325)
                  ·
                    refine ⟨17042310641624272480163093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 181784646843992239788406325 17042310641624272480163093)
                    ·
                      refine ⟨798858311326137772507645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17042310641624272480163093 798858311326137772507645)
                      ·
                        rfl

theorem cell23_1555771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 6].length) (baseStart_1555771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555771 prefixEnd_1555771 := by exact prefixLift 1555771
  have htrace : WordTrace (prefixWord ++ tailWord_1555771) baseStart_1555771 baseEnd_1555771 := by
    simpa [prefixWord, tailWord_1555771, baseEnd_1555771] using wordTrace_append hprefix tailTrace_1555771
  have hstable : (prefixWord ++ tailWord_1555771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555771).length < 2 ^ (prefixWord ++ tailWord_1555771).sum := by decide
  have hdescent : baseEnd_1555771 < baseStart_1555771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555775 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 3, 4, 2]
def baseStart_1555775 : Nat := 118140960795 + 1555775 * 2 ^ 59
def prefixEnd_1555775 : Nat := 4983230072969 + 3 ^ 40 * 1555775 * 2
def baseEnd_1555775 : Nat := 798860365248755756857627

theorem tailTrace_1555775 : CollatzResearch.WordTrace tailWord_1555775 prefixEnd_1555775 798860365248755756857627 := by
  unfold tailWord_1555775
  simp only [CollatzResearch.WordTrace]
  refine ⟨56743775938700355061236779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37829183959133570040824519 56743775938700355061236779)
  ·
    refine ⟨85115663908050532591855169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56743775938700355061236779 85115663908050532591855169)
    ·
      refine ⟨63836747931037899443891377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85115663908050532591855169 63836747931037899443891377)
      ·
        refine ⟨47877560948278424582918533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63836747931037899443891377 47877560948278424582918533)
        ·
          refine ⟨8977042677802204609297225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47877560948278424582918533 8977042677802204609297225)
          ·
            refine ⟨6732782008351653456972919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8977042677802204609297225 6732782008351653456972919)
            ·
              refine ⟨10099173012527480185459379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6732782008351653456972919 10099173012527480185459379)
              ·
                refine ⟨15148759518791220278189069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10099173012527480185459379 15148759518791220278189069)
                ·
                  refine ⟨5680784819546707604320901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15148759518791220278189069 5680784819546707604320901)
                  ·
                    refine ⟨1065147153665007675810169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5680784819546707604320901 1065147153665007675810169)
                    ·
                      refine ⟨798860365248755756857627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1065147153665007675810169 798860365248755756857627)
                      ·
                        rfl

theorem cell23_1555775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 4, 2].length) (baseStart_1555775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555775 prefixEnd_1555775 := by exact prefixLift 1555775
  have htrace : WordTrace (prefixWord ++ tailWord_1555775) baseStart_1555775 baseEnd_1555775 := by
    simpa [prefixWord, tailWord_1555775, baseEnd_1555775] using wordTrace_append hprefix tailTrace_1555775
  have hstable : (prefixWord ++ tailWord_1555775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555775).length < 2 ^ (prefixWord ++ tailWord_1555775).sum := by decide
  have hdescent : baseEnd_1555775 < baseStart_1555775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555815 : List Nat := [1, 1, 5, 1, 4, 1, 1, 2, 7]
def baseStart_1555815 : Nat := 118140960795 + 1555815 * 2 ^ 59
def prefixEnd_1555815 : Nat := 4983230072969 + 3 ^ 40 * 1555815 * 2
def baseEnd_1555815 : Nat := 88764544941659511150827

theorem tailTrace_1555815 : CollatzResearch.WordTrace tailWord_1555815 prefixEnd_1555815 88764544941659511150827 := by
  unfold tailWord_1555815
  simp only [CollatzResearch.WordTrace]
  refine ⟨56745234858555441892692899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37830156572370294595128599 56745234858555441892692899)
  ·
    refine ⟨85117852287833162839039349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56745234858555441892692899 85117852287833162839039349)
    ·
      refine ⟨7979798651984359016159939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85117852287833162839039349 7979798651984359016159939)
      ·
        refine ⟨11969697977976538524239909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7979798651984359016159939 11969697977976538524239909)
        ·
          refine ⟨2244318370870600973294983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11969697977976538524239909 2244318370870600973294983)
          ·
            refine ⟨3366477556305901459942475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244318370870600973294983 3366477556305901459942475)
            ·
              refine ⟨5049716334458852189913713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3366477556305901459942475 5049716334458852189913713)
              ·
                refine ⟨3787287250844139142435285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5049716334458852189913713 3787287250844139142435285)
                ·
                  refine ⟨88764544941659511150827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3787287250844139142435285 88764544941659511150827)
                  ·
                    rfl

theorem cell23_1555815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 7].length) (baseStart_1555815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555815 prefixEnd_1555815 := by exact prefixLift 1555815
  have htrace : WordTrace (prefixWord ++ tailWord_1555815) baseStart_1555815 baseEnd_1555815 := by
    simpa [prefixWord, tailWord_1555815, baseEnd_1555815] using wordTrace_append hprefix tailTrace_1555815
  have hstable : (prefixWord ++ tailWord_1555815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555815).length < 2 ^ (prefixWord ++ tailWord_1555815).sum := by decide
  have hdescent : baseEnd_1555815 < baseStart_1555815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555875 : List Nat := [1, 1, 1, 4, 1, 3, 1, 4, 3, 4]
def baseStart_1555875 : Nat := 118140960795 + 1555875 * 2 ^ 59
def prefixEnd_1555875 : Nat := 4983230072969 + 3 ^ 40 * 1555875 * 2
def baseEnd_1555875 : Nat := 266303904438068455202389

theorem tailTrace_1555875 : CollatzResearch.WordTrace tailWord_1555875 prefixEnd_1555875 266303904438068455202389 := by
  unfold tailWord_1555875
  simp only [CollatzResearch.WordTrace]
  refine ⟨56747423238338072139877079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37831615492225381426584719 56747423238338072139877079)
  ·
    refine ⟨85121134857507108209815619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56747423238338072139877079 85121134857507108209815619)
    ·
      refine ⟨127681702286260662314723429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85121134857507108209815619 127681702286260662314723429)
      ·
        refine ⟨23940319178673874184010643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127681702286260662314723429 23940319178673874184010643)
        ·
          refine ⟨35910478768010811276015965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23940319178673874184010643 35910478768010811276015965)
          ·
            refine ⟨13466429538004054228505987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35910478768010811276015965 13466429538004054228505987)
            ·
              refine ⟨20199644307006081342758981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13466429538004054228505987 20199644307006081342758981)
              ·
                refine ⟨3787433307563640251767309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20199644307006081342758981 3787433307563640251767309)
                ·
                  refine ⟨1420287490336365094412741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3787433307563640251767309 1420287490336365094412741)
                  ·
                    refine ⟨266303904438068455202389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1420287490336365094412741 266303904438068455202389)
                    ·
                      rfl

theorem cell23_1555875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 4].length) (baseStart_1555875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555875 prefixEnd_1555875 := by exact prefixLift 1555875
  have htrace : WordTrace (prefixWord ++ tailWord_1555875) baseStart_1555875 baseEnd_1555875 := by
    simpa [prefixWord, tailWord_1555875, baseEnd_1555875] using wordTrace_append hprefix tailTrace_1555875
  have hstable : (prefixWord ++ tailWord_1555875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555875).length < 2 ^ (prefixWord ++ tailWord_1555875).sum := by decide
  have hdescent : baseEnd_1555875 < baseStart_1555875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555935 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 3, 5]
def baseStart_1555935 : Nat := 118140960795 + 1555935 * 2 ^ 59
def prefixEnd_1555935 : Nat := 4983230072969 + 3 ^ 40 * 1555935 * 2
def baseEnd_1555935 : Nat := 266314174051158376952297

theorem tailTrace_1555935 : CollatzResearch.WordTrace tailWord_1555935 prefixEnd_1555935 266314174051158376952297 := by
  unfold tailWord_1555935
  simp only [CollatzResearch.WordTrace]
  refine ⟨56749611618120702387061259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37833074412080468258040839 56749611618120702387061259)
  ·
    refine ⟨85124417427181053580591889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56749611618120702387061259 85124417427181053580591889)
    ·
      refine ⟨63843313070385790185443917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85124417427181053580591889 63843313070385790185443917)
      ·
        refine ⟨23941242401394671319541469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63843313070385790185443917 23941242401394671319541469)
        ·
          refine ⟨8977965900523001744828051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23941242401394671319541469 8977965900523001744828051)
          ·
            refine ⟨13466948850784502617242077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8977965900523001744828051 13466948850784502617242077)
            ·
              refine ⟨5050105819044188481465779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13466948850784502617242077 5050105819044188481465779)
              ·
                refine ⟨7575158728566282722198669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5050105819044188481465779 7575158728566282722198669)
                ·
                  refine ⟨2840684523212356020824501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7575158728566282722198669 2840684523212356020824501)
                  ·
                    refine ⟨266314174051158376952297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2840684523212356020824501 266314174051158376952297)
                    ·
                      rfl

theorem cell23_1555935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 5].length) (baseStart_1555935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555935 prefixEnd_1555935 := by exact prefixLift 1555935
  have htrace : WordTrace (prefixWord ++ tailWord_1555935) baseStart_1555935 baseEnd_1555935 := by
    simpa [prefixWord, tailWord_1555935, baseEnd_1555935] using wordTrace_append hprefix tailTrace_1555935
  have hstable : (prefixWord ++ tailWord_1555935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555935).length < 2 ^ (prefixWord ++ tailWord_1555935).sum := by decide
  have hdescent : baseEnd_1555935 < baseStart_1555935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1555989 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 5, 2, 2]
def baseStart_1555989 : Nat := 118140960795 + 1555989 * 2 ^ 59
def prefixEnd_1555989 : Nat := 4983230072969 + 3 ^ 40 * 1555989 * 2
def baseEnd_1555989 : Nat := 798970250108817919581643

theorem tailTrace_1555989 : CollatzResearch.WordTrace tailWord_1555989 prefixEnd_1555989 798970250108817919581643 := by
  unfold tailWord_1555989
  simp only [CollatzResearch.WordTrace]
  refine ⟨56751581159925069609527021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37834387439950046406351347 56751581159925069609527021)
  ·
    refine ⟨21281842934971901103572633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56751581159925069609527021 21281842934971901103572633)
    ·
      refine ⟨15961382201228925827679475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21281842934971901103572633 15961382201228925827679475)
      ·
        refine ⟨23942073301843388741519213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15961382201228925827679475 23942073301843388741519213)
        ·
          refine ⟨8978277488191270778069705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23942073301843388741519213 8978277488191270778069705)
          ·
            refine ⟨6733708116143453083552279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8978277488191270778069705 6733708116143453083552279)
            ·
              refine ⟨10100562174215179625328419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6733708116143453083552279 10100562174215179625328419)
              ·
                refine ⟨15150843261322769437992629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10100562174215179625328419 15150843261322769437992629)
                ·
                  refine ⟨1420391555749009634811809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15150843261322769437992629 1420391555749009634811809)
                  ·
                    refine ⟨1065293666811757226108857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1420391555749009634811809 1065293666811757226108857)
                    ·
                      refine ⟨798970250108817919581643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1065293666811757226108857 798970250108817919581643)
                      ·
                        rfl

theorem cell23_1555989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_1555989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1555989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1555989 prefixEnd_1555989 := by exact prefixLift 1555989
  have htrace : WordTrace (prefixWord ++ tailWord_1555989) baseStart_1555989 baseEnd_1555989 := by
    simpa [prefixWord, tailWord_1555989, baseEnd_1555989] using wordTrace_append hprefix tailTrace_1555989
  have hstable : (prefixWord ++ tailWord_1555989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1555989).length < 2 ^ (prefixWord ++ tailWord_1555989).sum := by decide
  have hdescent : baseEnd_1555989 < baseStart_1555989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1555989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556002 : List Nat := [3, 3, 1, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_1556002 : Nat := 118140960795 + 1556002 * 2 ^ 59
def prefixEnd_1556002 : Nat := 4983230072969 + 3 ^ 40 * 1556002 * 2
def baseEnd_1556002 : Nat := 798976925357326368719083

theorem tailTrace_1556002 : CollatzResearch.WordTrace tailWord_1556002 prefixEnd_1556002 798976925357326368719083 := by
  unfold tailWord_1556002
  simp only [CollatzResearch.WordTrace]
  refine ⟨14188013827219493207437565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37834703539251981886500173 14188013827219493207437565)
  ·
    refine ⟨5320505185207309952789087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14188013827219493207437565 5320505185207309952789087)
    ·
      refine ⟨7980757777810964929183631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5320505185207309952789087 7980757777810964929183631)
      ·
        refine ⟨11971136666716447393775447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7980757777810964929183631 11971136666716447393775447)
        ·
          refine ⟨17956705000074671090663171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11971136666716447393775447 17956705000074671090663171)
          ·
            refine ⟨26935057500112006635994757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17956705000074671090663171 26935057500112006635994757)
            ·
              refine ⟨5050323281271001244249017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26935057500112006635994757 5050323281271001244249017)
              ·
                refine ⟨3787742460953250933186763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5050323281271001244249017 3787742460953250933186763)
                ·
                  refine ⟨5681613691429876399780145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3787742460953250933186763 5681613691429876399780145)
                  ·
                    refine ⟨4261210268572407299835109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5681613691429876399780145 4261210268572407299835109)
                    ·
                      refine ⟨798976925357326368719083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4261210268572407299835109 798976925357326368719083)
                      ·
                        rfl

theorem cell23_1556002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_1556002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556002 prefixEnd_1556002 := by exact prefixLift 1556002
  have htrace : WordTrace (prefixWord ++ tailWord_1556002) baseStart_1556002 baseEnd_1556002 := by
    simpa [prefixWord, tailWord_1556002, baseEnd_1556002] using wordTrace_append hprefix tailTrace_1556002
  have hstable : (prefixWord ++ tailWord_1556002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556002).length < 2 ^ (prefixWord ++ tailWord_1556002).sum := by decide
  have hdescent : baseEnd_1556002 < baseStart_1556002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556096 : List Nat := [2, 1, 1, 2, 1, 4, 3, 3, 2, 2, 2]
def baseStart_1556096 : Nat := 118140960795 + 1556096 * 2 ^ 59
def prefixEnd_1556096 : Nat := 4983230072969 + 3 ^ 40 * 1556096 * 2
def baseEnd_1556096 : Nat := 799025192538849000943651

theorem tailTrace_1556096 : CollatzResearch.WordTrace tailWord_1556096 prefixEnd_1556096 799025192538849000943651 := by
  unfold tailWord_1556096
  simp only [CollatzResearch.WordTrace]
  refine ⟨28377741885268713441836071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37836989180358284589114761 28377741885268713441836071)
  ·
    refine ⟨42566612827903070162754107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28377741885268713441836071 42566612827903070162754107)
    ·
      refine ⟨63849919241854605244131161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42566612827903070162754107 63849919241854605244131161)
      ·
        refine ⟨47887439431390953933098371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63849919241854605244131161 47887439431390953933098371)
        ·
          refine ⟨71831159147086430899647557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47887439431390953933098371 71831159147086430899647557)
          ·
            refine ⟨13468342340078705793683917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71831159147086430899647557 13468342340078705793683917)
            ·
              refine ⟨5050628377529514672631469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13468342340078705793683917 5050628377529514672631469)
              ·
                refine ⟨1893985641573568002236801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5050628377529514672631469 1893985641573568002236801)
                ·
                  refine ⟨1420489231180176001677601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1893985641573568002236801 1420489231180176001677601)
                  ·
                    refine ⟨1065366923385132001258201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1420489231180176001677601 1065366923385132001258201)
                    ·
                      refine ⟨799025192538849000943651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1065366923385132001258201 799025192538849000943651)
                      ·
                        rfl

theorem cell23_1556096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 2, 2, 2].length) (baseStart_1556096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556096 prefixEnd_1556096 := by exact prefixLift 1556096
  have htrace : WordTrace (prefixWord ++ tailWord_1556096) baseStart_1556096 baseEnd_1556096 := by
    simpa [prefixWord, tailWord_1556096, baseEnd_1556096] using wordTrace_append hprefix tailTrace_1556096
  have hstable : (prefixWord ++ tailWord_1556096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556096).length < 2 ^ (prefixWord ++ tailWord_1556096).sum := by decide
  have hdescent : baseEnd_1556096 < baseStart_1556096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556100 : List Nat := [2, 3, 2, 1, 5, 1, 1, 2, 1, 3, 2]
def baseStart_1556100 : Nat := 118140960795 + 1556100 * 2 ^ 59
def prefixEnd_1556100 : Nat := 4983230072969 + 3 ^ 40 * 1556100 * 2
def baseEnd_1556100 : Nat := 799027246461466985293633

theorem tailTrace_1556100 : CollatzResearch.WordTrace tailWord_1556100 prefixEnd_1556100 799027246461466985293633 := by
  unfold tailWord_1556100
  simp only [CollatzResearch.WordTrace]
  refine ⟨28377814831261467783408877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37837086441681957044545169 28377814831261467783408877)
  ·
    refine ⟨10641680561723050418778329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28377814831261467783408877 10641680561723050418778329)
    ·
      refine ⟨7981260421292287814083747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10641680561723050418778329 7981260421292287814083747)
      ·
        refine ⟨11971890631938431721125621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7981260421292287814083747 11971890631938431721125621)
        ·
          refine ⟨1122364746744227973855527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11971890631938431721125621 1122364746744227973855527)
          ·
            refine ⟨1683547120116341960783291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1122364746744227973855527 1683547120116341960783291)
            ·
              refine ⟨2525320680174512941174937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1683547120116341960783291 2525320680174512941174937)
              ·
                refine ⟨1893990510130884705881203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2525320680174512941174937 1893990510130884705881203)
                ·
                  refine ⟨2840985765196327058821805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1893990510130884705881203 2840985765196327058821805)
                  ·
                    refine ⟨1065369661948622647058177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2840985765196327058821805 1065369661948622647058177)
                    ·
                      refine ⟨799027246461466985293633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1065369661948622647058177 799027246461466985293633)
                      ·
                        rfl

theorem cell23_1556100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_1556100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556100 prefixEnd_1556100 := by exact prefixLift 1556100
  have htrace : WordTrace (prefixWord ++ tailWord_1556100) baseStart_1556100 baseEnd_1556100 := by
    simpa [prefixWord, tailWord_1556100, baseEnd_1556100] using wordTrace_append hprefix tailTrace_1556100
  have hstable : (prefixWord ++ tailWord_1556100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556100).length < 2 ^ (prefixWord ++ tailWord_1556100).sum := by decide
  have hdescent : baseEnd_1556100 < baseStart_1556100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1556152 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 4, 1, 4]
def baseStart_1556152 : Nat := 118140960795 + 1556152 * 2 ^ 59
def prefixEnd_1556152 : Nat := 4983230072969 + 3 ^ 40 * 1556152 * 2
def baseEnd_1556152 : Nat := 799053947455500781843393

theorem tailTrace_1556152 : CollatzResearch.WordTrace tailWord_1556152 prefixEnd_1556152 799053947455500781843393 := by
  unfold tailWord_1556152
  simp only [CollatzResearch.WordTrace]
  refine ⟨28378763129167274223855355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37838350838889698965140473 28378763129167274223855355)
  ·
    refine ⟨42568144693750911335783033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28378763129167274223855355 42568144693750911335783033)
    ·
      refine ⟨31926108520313183501837275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42568144693750911335783033 31926108520313183501837275)
      ·
        refine ⟨47889162780469775252755913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31926108520313183501837275 47889162780469775252755913)
        ·
          refine ⟨35916872085352331439566935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47889162780469775252755913 35916872085352331439566935)
          ·
            refine ⟨53875308128028497159350403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35916872085352331439566935 53875308128028497159350403)
            ·
              refine ⟨80812962192042745739025605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53875308128028497159350403 80812962192042745739025605)
              ·
                refine ⟨15152430411008014826067301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80812962192042745739025605 15152430411008014826067301)
                ·
                  refine ⟨2841080702064002779887619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15152430411008014826067301 2841080702064002779887619)
                  ·
                    refine ⟨4261621053096004169831429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2841080702064002779887619 4261621053096004169831429)
                    ·
                      refine ⟨799053947455500781843393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4261621053096004169831429 799053947455500781843393)
                      ·
                        rfl

theorem cell23_1556152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_1556152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1556152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1556152 prefixEnd_1556152 := by exact prefixLift 1556152
  have htrace : WordTrace (prefixWord ++ tailWord_1556152) baseStart_1556152 baseEnd_1556152 := by
    simpa [prefixWord, tailWord_1556152, baseEnd_1556152] using wordTrace_append hprefix tailTrace_1556152
  have hstable : (prefixWord ++ tailWord_1556152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1556152).length < 2 ^ (prefixWord ++ tailWord_1556152).sum := by decide
  have hdescent : baseEnd_1556152 < baseStart_1556152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1556152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
