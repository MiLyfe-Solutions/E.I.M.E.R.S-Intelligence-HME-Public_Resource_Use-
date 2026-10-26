import V185TrunkScan23Chunk0086

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_516895 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 6]
def baseStart_516895 : Nat := 118140960795 + 516895 * 2 ^ 59
def prefixEnd_516895 : Nat := 4983230072969 + 3 ^ 40 * 516895 * 2
def baseEnd_516895 : Nat := 265415582905860379635349

theorem tailTrace_516895 : CollatzResearch.WordTrace tailWord_516895 prefixEnd_516895 265415582905860379635349 := by
  unfold tailWord_516895
  simp only [CollatzResearch.WordTrace]
  refine ⟨18852709462385168482888139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12568472974923445655258759 18852709462385168482888139)
  ·
    refine ⟨28279064193577752724332209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18852709462385168482888139 28279064193577752724332209)
    ·
      refine ⟨21209298145183314543249157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28279064193577752724332209 21209298145183314543249157)
      ·
        refine ⟨3976743402221871476859217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21209298145183314543249157 3976743402221871476859217)
        ·
          refine ⟨2982557551666403607644413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3976743402221871476859217 2982557551666403607644413)
          ·
            refine ⟨1118459081874901352866655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2982557551666403607644413 1118459081874901352866655)
            ·
              refine ⟨1677688622812352029299983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118459081874901352866655 1677688622812352029299983)
              ·
                refine ⟨2516532934218528043949975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1677688622812352029299983 2516532934218528043949975)
                ·
                  refine ⟨3774799401327792065924963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2516532934218528043949975 3774799401327792065924963)
                  ·
                    refine ⟨5662199101991688098887445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3774799401327792065924963 5662199101991688098887445)
                    ·
                      refine ⟨265415582905860379635349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5662199101991688098887445 265415582905860379635349)
                      ·
                        rfl

theorem cell23_516895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_516895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516895 prefixEnd_516895 := by exact prefixLift 516895
  have htrace : WordTrace (prefixWord ++ tailWord_516895) baseStart_516895 baseEnd_516895 := by
    simpa [prefixWord, tailWord_516895, baseEnd_516895] using wordTrace_append hprefix tailTrace_516895
  have hstable : (prefixWord ++ tailWord_516895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516895).length < 2 ^ (prefixWord ++ tailWord_516895).sum := by decide
  have hdescent : baseEnd_516895 < baseStart_516895 := by decide
  rcases family_descends (prefixWord ++ tailWord_516895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516922 : List Nat := [3, 1, 1, 1, 7, 1, 9]
def baseStart_516922 : Nat := 118140960795 + 516922 * 2 ^ 59
def prefixEnd_516922 : Nat := 4983230072969 + 3 ^ 40 * 516922 * 2
def baseEnd_516922 : Nat := 3276906751648540419725

theorem tailTrace_516922 : CollatzResearch.WordTrace tailWord_516922 prefixEnd_516922 3276906751648540419725 := by
  unfold tailWord_516922
  simp only [CollatzResearch.WordTrace]
  refine ⟨4713423558321838023530255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12569129488858234729414013 4713423558321838023530255)
  ·
    refine ⟨7070135337482757035295383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4713423558321838023530255 7070135337482757035295383)
    ·
      refine ⟨10605203006224135552943075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7070135337482757035295383 10605203006224135552943075)
      ·
        refine ⟨15907804509336203329414613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10605203006224135552943075 15907804509336203329414613)
        ·
          refine ⟨372839168187567265533155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 15907804509336203329414613 372839168187567265533155)
          ·
            refine ⟨559258752281350898299733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372839168187567265533155 559258752281350898299733)
            ·
              refine ⟨3276906751648540419725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 559258752281350898299733 3276906751648540419725)
              ·
                rfl

theorem cell23_516922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 9].length) (baseStart_516922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516922 prefixEnd_516922 := by exact prefixLift 516922
  have htrace : WordTrace (prefixWord ++ tailWord_516922) baseStart_516922 baseEnd_516922 := by
    simpa [prefixWord, tailWord_516922, baseEnd_516922] using wordTrace_append hprefix tailTrace_516922
  have hstable : (prefixWord ++ tailWord_516922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516922).length < 2 ^ (prefixWord ++ tailWord_516922).sum := by decide
  have hdescent : baseEnd_516922 < baseStart_516922 := by decide
  rcases family_descends (prefixWord ++ tailWord_516922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516949 : List Nat := [1, 3, 2, 2, 2, 1, 3, 3, 2, 1, 3]
def baseStart_516949 : Nat := 118140960795 + 516949 * 2 ^ 59
def prefixEnd_516949 : Nat := 4983230072969 + 3 ^ 40 * 516949 * 2
def baseEnd_516949 : Nat := 265443310861203168360101

theorem tailTrace_516949 : CollatzResearch.WordTrace tailWord_516949 prefixEnd_516949 265443310861203168360101 := by
  unfold tailWord_516949
  simp only [CollatzResearch.WordTrace]
  refine ⟨18854679004189535705353901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12569786002793023803569267 18854679004189535705353901)
  ·
    refine ⟨7070504626571075889507713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18854679004189535705353901 7070504626571075889507713)
    ·
      refine ⟨5302878469928306917130785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7070504626571075889507713 5302878469928306917130785)
      ·
        refine ⟨3977158852446230187848089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5302878469928306917130785 3977158852446230187848089)
        ·
          refine ⟨2982869139334672640886067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3977158852446230187848089 2982869139334672640886067)
          ·
            refine ⟨4474303709002008961329101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2982869139334672640886067 4474303709002008961329101)
            ·
              refine ⟨1677863890875753360498413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4474303709002008961329101 1677863890875753360498413)
              ·
                refine ⟨629198959078407510186905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1677863890875753360498413 629198959078407510186905)
                ·
                  refine ⟨471899219308805632640179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629198959078407510186905 471899219308805632640179)
                  ·
                    refine ⟨707848828963208448960269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 471899219308805632640179 707848828963208448960269)
                    ·
                      refine ⟨265443310861203168360101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 707848828963208448960269 265443310861203168360101)
                      ·
                        rfl

theorem cell23_516949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_516949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516949 prefixEnd_516949 := by exact prefixLift 516949
  have htrace : WordTrace (prefixWord ++ tailWord_516949) baseStart_516949 baseEnd_516949 := by
    simpa [prefixWord, tailWord_516949, baseEnd_516949] using wordTrace_append hprefix tailTrace_516949
  have hstable : (prefixWord ++ tailWord_516949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516949).length < 2 ^ (prefixWord ++ tailWord_516949).sum := by decide
  have hdescent : baseEnd_516949 < baseStart_516949 := by decide
  rcases family_descends (prefixWord ++ tailWord_516949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516975 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 3]
def baseStart_516975 : Nat := 118140960795 + 516975 * 2 ^ 59
def prefixEnd_516975 : Nat := 4983230072969 + 3 ^ 40 * 516975 * 2
def baseEnd_516975 : Nat := 265456661358220066634981

theorem tailTrace_516975 : CollatzResearch.WordTrace tailWord_516975 prefixEnd_516975 265456661358220066634981 := by
  unfold tailWord_516975
  simp only [CollatzResearch.WordTrace]
  refine ⟨18855627302095342145800379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12570418201396894763866919 18855627302095342145800379)
  ·
    refine ⟨28283440953143013218700569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18855627302095342145800379 28283440953143013218700569)
    ·
      refine ⟨21212580714857259914025427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28283440953143013218700569 21212580714857259914025427)
      ·
        refine ⟨31818871072285889871038141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21212580714857259914025427 31818871072285889871038141)
        ·
          refine ⟨11932076652107208701639303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31818871072285889871038141 11932076652107208701639303)
          ·
            refine ⟨17898114978160813052458955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11932076652107208701639303 17898114978160813052458955)
            ·
              refine ⟨26847172467241219578688433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17898114978160813052458955 26847172467241219578688433)
              ·
                refine ⟨20135379350430914684016325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26847172467241219578688433 20135379350430914684016325)
                ·
                  refine ⟨3775383628205796503253061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20135379350430914684016325 3775383628205796503253061)
                  ·
                    refine ⟨707884430288586844359949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3775383628205796503253061 707884430288586844359949)
                    ·
                      refine ⟨265456661358220066634981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 707884430288586844359949 265456661358220066634981)
                      ·
                        rfl

theorem cell23_516975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 3].length) (baseStart_516975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516975 prefixEnd_516975 := by exact prefixLift 516975
  have htrace : WordTrace (prefixWord ++ tailWord_516975) baseStart_516975 baseEnd_516975 := by
    simpa [prefixWord, tailWord_516975, baseEnd_516975] using wordTrace_append hprefix tailTrace_516975
  have hstable : (prefixWord ++ tailWord_516975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516975).length < 2 ^ (prefixWord ++ tailWord_516975).sum := by decide
  have hdescent : baseEnd_516975 < baseStart_516975 := by decide
  rcases family_descends (prefixWord ++ tailWord_516975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516989 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 4, 2, 2]
def baseStart_516989 : Nat := 118140960795 + 516989 * 2 ^ 59
def prefixEnd_516989 : Nat := 4983230072969 + 3 ^ 40 * 516989 * 2
def baseEnd_516989 : Nat := 265463850087383011859917

theorem tailTrace_516989 : CollatzResearch.WordTrace tailWord_516989 prefixEnd_516989 265463850087383011859917 := by
  unfold tailWord_516989
  simp only [CollatzResearch.WordTrace]
  refine ⟨18856137924044622536810021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12570758616029748357873347 18856137924044622536810021)
  ·
    refine ⟨3535525860758366725651879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18856137924044622536810021 3535525860758366725651879)
    ·
      refine ⟨5303288791137550088477819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3535525860758366725651879 5303288791137550088477819)
      ·
        refine ⟨7954933186706325132716729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5303288791137550088477819 7954933186706325132716729)
        ·
          refine ⟨5966199890029743849537547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7954933186706325132716729 5966199890029743849537547)
          ·
            refine ⟨8949299835044615774306321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5966199890029743849537547 8949299835044615774306321)
            ·
              refine ⟨6711974876283461830729741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8949299835044615774306321 6711974876283461830729741)
              ·
                refine ⟨2516990578606298186523653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6711974876283461830729741 2516990578606298186523653)
                ·
                  refine ⟨471935733488680909973185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2516990578606298186523653 471935733488680909973185)
                  ·
                    refine ⟨353951800116510682479889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 471935733488680909973185 353951800116510682479889)
                    ·
                      refine ⟨265463850087383011859917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 353951800116510682479889 265463850087383011859917)
                      ·
                        rfl

theorem cell23_516989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_516989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516989 prefixEnd_516989 := by exact prefixLift 516989
  have htrace : WordTrace (prefixWord ++ tailWord_516989) baseStart_516989 baseEnd_516989 := by
    simpa [prefixWord, tailWord_516989, baseEnd_516989] using wordTrace_append hprefix tailTrace_516989
  have hstable : (prefixWord ++ tailWord_516989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516989).length < 2 ^ (prefixWord ++ tailWord_516989).sum := by decide
  have hdescent : baseEnd_516989 < baseStart_516989 := by decide
  rcases family_descends (prefixWord ++ tailWord_516989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516995 : List Nat := [1, 1, 1, 3, 4, 1, 2, 3, 7]
def baseStart_516995 : Nat := 118140960795 + 516995 * 2 ^ 59
def prefixEnd_516995 : Nat := 4983230072969 + 3 ^ 40 * 516995 * 2
def baseEnd_516995 : Nat := 29496325663478887598321

theorem tailTrace_516995 : CollatzResearch.WordTrace tailWord_516995 prefixEnd_516995 29496325663478887598321 := by
  unfold tailWord_516995
  simp only [CollatzResearch.WordTrace]
  refine ⟨18856356762022885561528439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12570904508015257041018959 18856356762022885561528439)
  ·
    refine ⟨28284535143034328342292659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18856356762022885561528439 28284535143034328342292659)
    ·
      refine ⟨42426802714551492513438989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28284535143034328342292659 42426802714551492513438989)
      ·
        refine ⟨15910051017956809692539621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42426802714551492513438989 15910051017956809692539621)
        ·
          refine ⟨2983134565866901817351179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15910051017956809692539621 2983134565866901817351179)
          ·
            refine ⟨4474701848800352726026769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2983134565866901817351179 4474701848800352726026769)
            ·
              refine ⟨3356026386600264544520077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4474701848800352726026769 3356026386600264544520077)
              ·
                refine ⟨1258509894975099204195029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3356026386600264544520077 1258509894975099204195029)
                ·
                  refine ⟨29496325663478887598321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1258509894975099204195029 29496325663478887598321)
                  ·
                    rfl

theorem cell23_516995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 7].length) (baseStart_516995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516995 prefixEnd_516995 := by exact prefixLift 516995
  have htrace : WordTrace (prefixWord ++ tailWord_516995) baseStart_516995 baseEnd_516995 := by
    simpa [prefixWord, tailWord_516995, baseEnd_516995] using wordTrace_append hprefix tailTrace_516995
  have hstable : (prefixWord ++ tailWord_516995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516995).length < 2 ^ (prefixWord ++ tailWord_516995).sum := by decide
  have hdescent : baseEnd_516995 < baseStart_516995 := by decide
  rcases family_descends (prefixWord ++ tailWord_516995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517002 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_517002 : Nat := 118140960795 + 517002 * 2 ^ 59
def prefixEnd_517002 : Nat := 4983230072969 + 3 ^ 40 * 517002 * 2
def baseEnd_517002 : Nat := 265470525335891460997357

theorem tailTrace_517002 : CollatzResearch.WordTrace tailWord_517002 prefixEnd_517002 265470525335891460997357 := by
  unfold tailWord_517002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4714153018249381439258315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12571074715331683838022173 4714153018249381439258315)
  ·
    refine ⟨7071229527374072158887473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4714153018249381439258315 7071229527374072158887473)
    ·
      refine ⟨5303422145530554119165605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7071229527374072158887473 5303422145530554119165605)
      ·
        refine ⟨994391652286978897343551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5303422145530554119165605 994391652286978897343551)
        ·
          refine ⟨1491587478430468346015327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994391652286978897343551 1491587478430468346015327)
          ·
            refine ⟨2237381217645702519022991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491587478430468346015327 2237381217645702519022991)
            ·
              refine ⟨3356071826468553778534487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2237381217645702519022991 3356071826468553778534487)
              ·
                refine ⟨5034107739702830667801731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3356071826468553778534487 5034107739702830667801731)
                ·
                  refine ⟨7551161609554246001702597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5034107739702830667801731 7551161609554246001702597)
                  ·
                    refine ⟨1415842801791421125319237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7551161609554246001702597 1415842801791421125319237)
                    ·
                      refine ⟨265470525335891460997357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1415842801791421125319237 265470525335891460997357)
                      ·
                        rfl

theorem cell23_517002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_517002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517002 prefixEnd_517002 := by exact prefixLift 517002
  have htrace : WordTrace (prefixWord ++ tailWord_517002) baseStart_517002 baseEnd_517002 := by
    simpa [prefixWord, tailWord_517002, baseEnd_517002] using wordTrace_append hprefix tailTrace_517002
  have hstable : (prefixWord ++ tailWord_517002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517002).length < 2 ^ (prefixWord ++ tailWord_517002).sum := by decide
  have hdescent : baseEnd_517002 < baseStart_517002 := by decide
  rcases family_descends (prefixWord ++ tailWord_517002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517012 : List Nat := [2, 4, 2, 1, 1, 1, 3, 2, 7]
def baseStart_517012 : Nat := 118140960795 + 517012 * 2 ^ 59
def prefixEnd_517012 : Nat := 4983230072969 + 3 ^ 40 * 517012 * 2
def baseEnd_517012 : Nat := 29497295571381824652479

theorem tailTrace_517012 : CollatzResearch.WordTrace tailWord_517012 prefixEnd_517012 29497295571381824652479 := by
  unfold tailWord_517012
  simp only [CollatzResearch.WordTrace]
  refine ⟨9428488401480648732448645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12571317868640864976598193 9428488401480648732448645)
  ·
    refine ⟨1767841575277621637334121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9428488401480648732448645 1767841575277621637334121)
    ·
      refine ⟨1325881181458216228000591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1767841575277621637334121 1325881181458216228000591)
      ·
        refine ⟨1988821772187324342000887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1325881181458216228000591 1988821772187324342000887)
        ·
          refine ⟨2983232658280986513001331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1988821772187324342000887 2983232658280986513001331)
          ·
            refine ⟨4474848987421479769501997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2983232658280986513001331 4474848987421479769501997)
            ·
              refine ⟨1678068370283054913563249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4474848987421479769501997 1678068370283054913563249)
              ·
                refine ⟨1258551277712291185172437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1678068370283054913563249 1258551277712291185172437)
                ·
                  refine ⟨29497295571381824652479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1258551277712291185172437 29497295571381824652479)
                  ·
                    rfl

theorem cell23_517012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_517012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517012 prefixEnd_517012 := by exact prefixLift 517012
  have htrace : WordTrace (prefixWord ++ tailWord_517012) baseStart_517012 baseEnd_517012 := by
    simpa [prefixWord, tailWord_517012, baseEnd_517012] using wordTrace_append hprefix tailTrace_517012
  have hstable : (prefixWord ++ tailWord_517012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517012).length < 2 ^ (prefixWord ++ tailWord_517012).sum := by decide
  have hdescent : baseEnd_517012 < baseStart_517012 := by decide
  rcases family_descends (prefixWord ++ tailWord_517012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517108 : List Nat := [2, 6, 2, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_517108 : Nat := 118140960795 + 517108 * 2 ^ 59
def prefixEnd_517108 : Nat := 4983230072969 + 3 ^ 40 * 517108 * 2
def baseEnd_517108 : Nat := 265524954285268046271871

theorem tailTrace_517108 : CollatzResearch.WordTrace tailWord_517108 prefixEnd_517108 265524954285268046271871 := by
  unfold tailWord_517108
  simp only [CollatzResearch.WordTrace]
  refine ⟨9430239105306752930195989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12573652140409003906927985 9430239105306752930195989)
  ·
    refine ⟨442042458061254043602937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9430239105306752930195989 442042458061254043602937)
    ·
      refine ⟨331531843545940532702203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442042458061254043602937 331531843545940532702203)
      ·
        refine ⟨497297765318910799053305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331531843545940532702203 497297765318910799053305)
        ·
          refine ⟨372973323989183099289979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497297765318910799053305 372973323989183099289979)
          ·
            refine ⟨559459985983774648934969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372973323989183099289979 559459985983774648934969)
            ·
              refine ⟨419594989487830986701227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 559459985983774648934969 419594989487830986701227)
              ·
                refine ⟨629392484231746480051841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419594989487830986701227 629392484231746480051841)
                ·
                  refine ⟨472044363173809860038881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629392484231746480051841 472044363173809860038881)
                  ·
                    refine ⟨354033272380357395029161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 472044363173809860038881 354033272380357395029161)
                    ·
                      refine ⟨265524954285268046271871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 354033272380357395029161 265524954285268046271871)
                      ·
                        rfl

theorem cell23_517108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_517108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517108 prefixEnd_517108 := by exact prefixLift 517108
  have htrace : WordTrace (prefixWord ++ tailWord_517108) baseStart_517108 baseEnd_517108 := by
    simpa [prefixWord, tailWord_517108, baseEnd_517108] using wordTrace_append hprefix tailTrace_517108
  have hstable : (prefixWord ++ tailWord_517108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517108).length < 2 ^ (prefixWord ++ tailWord_517108).sum := by decide
  have hdescent : baseEnd_517108 < baseStart_517108 := by decide
  rcases family_descends (prefixWord ++ tailWord_517108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517115 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 2, 9]
def baseStart_517115 : Nat := 118140960795 + 517115 * 2 ^ 59
def prefixEnd_517115 : Nat := 4983230072969 + 3 ^ 40 * 517115 * 2
def baseEnd_517115 : Nat := 88509516216616506294779

theorem tailTrace_517115 : CollatzResearch.WordTrace tailWord_517115 prefixEnd_517115 88509516216616506294779 := by
  unfold tailWord_517115
  simp only [CollatzResearch.WordTrace]
  refine ⟨18860733521588146055896799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12573822347725430703931199 18860733521588146055896799)
  ·
    refine ⟨28291100282382219083845199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18860733521588146055896799 28291100282382219083845199)
    ·
      refine ⟨42436650423573328625767799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28291100282382219083845199 42436650423573328625767799)
      ·
        refine ⟨63654975635359992938651699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42436650423573328625767799 63654975635359992938651699)
        ·
          refine ⟨95482463453039989407977549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63654975635359992938651699 95482463453039989407977549)
          ·
            refine ⟨35805923794889996027991581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95482463453039989407977549 35805923794889996027991581)
            ·
              refine ⟨13427221423083748510496843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35805923794889996027991581 13427221423083748510496843)
              ·
                refine ⟨20140832134625622765745265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13427221423083748510496843 20140832134625622765745265)
                ·
                  refine ⟨15105624100969217074308949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20140832134625622765745265 15105624100969217074308949)
                  ·
                    refine ⟨88509516216616506294779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 15105624100969217074308949 88509516216616506294779)
                    ·
                      rfl

theorem cell23_517115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 9].length) (baseStart_517115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517115 prefixEnd_517115 := by exact prefixLift 517115
  have htrace : WordTrace (prefixWord ++ tailWord_517115) baseStart_517115 baseEnd_517115 := by
    simpa [prefixWord, tailWord_517115, baseEnd_517115] using wordTrace_append hprefix tailTrace_517115
  have hstable : (prefixWord ++ tailWord_517115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517115).length < 2 ^ (prefixWord ++ tailWord_517115).sum := by decide
  have hdescent : baseEnd_517115 < baseStart_517115 := by decide
  rcases family_descends (prefixWord ++ tailWord_517115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517129 : List Nat := [1, 2, 1, 1, 3, 1, 1, 6, 3, 1, 3]
def baseStart_517129 : Nat := 118140960795 + 517129 * 2 ^ 59
def prefixEnd_517129 : Nat := 4983230072969 + 3 ^ 40 * 517129 * 2
def baseEnd_517129 : Nat := 265535737379012464109273

theorem tailTrace_517129 : CollatzResearch.WordTrace tailWord_517129 prefixEnd_517129 265535737379012464109273 := by
  unfold tailWord_517129
  simp only [CollatzResearch.WordTrace]
  refine ⟨18861244143537426446906441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12574162762358284297937627 18861244143537426446906441)
  ·
    refine ⟨14145933107653069835179831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18861244143537426446906441 14145933107653069835179831)
    ·
      refine ⟨21218899661479604752769747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14145933107653069835179831 21218899661479604752769747)
      ·
        refine ⟨31828349492219407129154621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21218899661479604752769747 31828349492219407129154621)
        ·
          refine ⟨11935631059582277673432983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31828349492219407129154621 11935631059582277673432983)
          ·
            refine ⟨17903446589373416510149475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11935631059582277673432983 17903446589373416510149475)
            ·
              refine ⟨26855169884060124765224213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17903446589373416510149475 26855169884060124765224213)
              ·
                refine ⟨1258836088315318348369885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26855169884060124765224213 1258836088315318348369885)
                ·
                  refine ⟨472063533118244380638707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1258836088315318348369885 472063533118244380638707)
                  ·
                    refine ⟨708095299677366570958061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 472063533118244380638707 708095299677366570958061)
                    ·
                      refine ⟨265535737379012464109273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 708095299677366570958061 265535737379012464109273)
                      ·
                        rfl

theorem cell23_517129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 1, 3].length) (baseStart_517129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517129 prefixEnd_517129 := by exact prefixLift 517129
  have htrace : WordTrace (prefixWord ++ tailWord_517129) baseStart_517129 baseEnd_517129 := by
    simpa [prefixWord, tailWord_517129, baseEnd_517129] using wordTrace_append hprefix tailTrace_517129
  have hstable : (prefixWord ++ tailWord_517129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517129).length < 2 ^ (prefixWord ++ tailWord_517129).sum := by decide
  have hdescent : baseEnd_517129 < baseStart_517129 := by decide
  rcases family_descends (prefixWord ++ tailWord_517129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517189 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 3, 2, 3]
def baseStart_517189 : Nat := 118140960795 + 517189 * 2 ^ 59
def prefixEnd_517189 : Nat := 4983230072969 + 3 ^ 40 * 517189 * 2
def baseEnd_517189 : Nat := 265566546218282229358997

theorem tailTrace_517189 : CollatzResearch.WordTrace tailWord_517189 prefixEnd_517189 265566546218282229358997 := by
  unfold tailWord_517189
  simp only [CollatzResearch.WordTrace]
  refine ⟨18863432523320056694090621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12575621682213371129393747 18863432523320056694090621)
  ·
    refine ⟨7073787196245021260283983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18863432523320056694090621 7073787196245021260283983)
    ·
      refine ⟨10610680794367531890425975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7073787196245021260283983 10610680794367531890425975)
      ·
        refine ⟨15916021191551297835638963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10610680794367531890425975 15916021191551297835638963)
        ·
          refine ⟨23874031787326946753458445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15916021191551297835638963 23874031787326946753458445)
          ·
            refine ⟨8952761920247605032546917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23874031787326946753458445 8952761920247605032546917)
            ·
              refine ⟨1678642860046425943602547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8952761920247605032546917 1678642860046425943602547)
              ·
                refine ⟨2517964290069638915403821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1678642860046425943602547 2517964290069638915403821)
                ·
                  refine ⟨944236608776114593276433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2517964290069638915403821 944236608776114593276433)
                  ·
                    refine ⟨708177456582085944957325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 944236608776114593276433 708177456582085944957325)
                    ·
                      refine ⟨265566546218282229358997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 708177456582085944957325 265566546218282229358997)
                      ·
                        rfl

theorem cell23_517189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_517189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517189 prefixEnd_517189 := by exact prefixLift 517189
  have htrace : WordTrace (prefixWord ++ tailWord_517189) baseStart_517189 baseEnd_517189 := by
    simpa [prefixWord, tailWord_517189, baseEnd_517189] using wordTrace_append hprefix tailTrace_517189
  have hstable : (prefixWord ++ tailWord_517189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517189).length < 2 ^ (prefixWord ++ tailWord_517189).sum := by decide
  have hdescent : baseEnd_517189 < baseStart_517189 := by decide
  rcases family_descends (prefixWord ++ tailWord_517189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517190 : List Nat := [6, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_517190 : Nat := 118140960795 + 517190 * 2 ^ 59
def prefixEnd_517190 : Nat := 4983230072969 + 3 ^ 40 * 517190 * 2
def baseEnd_517190 : Nat := 265567059698936725446493

theorem tailTrace_517190 : CollatzResearch.WordTrace tailWord_517190 prefixEnd_517190 265567059698936725446493 := by
  unfold tailWord_517190
  simp only [CollatzResearch.WordTrace]
  refine ⟨589483406134888558277407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12575645997544289243251349 589483406134888558277407)
  ·
    refine ⟨884225109202332837416111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 589483406134888558277407 884225109202332837416111)
    ·
      refine ⟨1326337663803499256124167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 884225109202332837416111 1326337663803499256124167)
      ·
        refine ⟨1989506495705248884186251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1326337663803499256124167 1989506495705248884186251)
        ·
          refine ⟨2984259743557873326279377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1989506495705248884186251 2984259743557873326279377)
          ·
            refine ⟨2238194807668404994709533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2984259743557873326279377 2238194807668404994709533)
            ·
              refine ⟨839323052875651873016075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2238194807668404994709533 839323052875651873016075)
              ·
                refine ⟨1258984579313477809524113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 839323052875651873016075 1258984579313477809524113)
                ·
                  refine ⟨944238434485108357143085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1258984579313477809524113 944238434485108357143085)
                  ·
                    refine ⟨354089412931915633928657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 944238434485108357143085 354089412931915633928657)
                    ·
                      refine ⟨265567059698936725446493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 354089412931915633928657 265567059698936725446493)
                      ·
                        rfl

theorem cell23_517190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_517190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517190 prefixEnd_517190 := by exact prefixLift 517190
  have htrace : WordTrace (prefixWord ++ tailWord_517190) baseStart_517190 baseEnd_517190 := by
    simpa [prefixWord, tailWord_517190, baseEnd_517190] using wordTrace_append hprefix tailTrace_517190
  have hstable : (prefixWord ++ tailWord_517190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517190).length < 2 ^ (prefixWord ++ tailWord_517190).sum := by decide
  have hdescent : baseEnd_517190 < baseStart_517190 := by decide
  rcases family_descends (prefixWord ++ tailWord_517190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517203 : List Nat := [1, 1, 1, 2, 1, 1, 2, 9, 1, 2, 2]
def baseStart_517203 : Nat := 118140960795 + 517203 * 2 ^ 59
def prefixEnd_517203 : Nat := 4983230072969 + 3 ^ 40 * 517203 * 2
def baseEnd_517203 : Nat := 265573734947445174583933

theorem tailTrace_517203 : CollatzResearch.WordTrace tailWord_517203 prefixEnd_517203 265573734947445174583933 := by
  unfold tailWord_517203
  simp only [CollatzResearch.WordTrace]
  refine ⟨18863943145269337085100263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12575962096846224723400175 18863943145269337085100263)
  ·
    refine ⟨28295914717904005627650395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18863943145269337085100263 28295914717904005627650395)
    ·
      refine ⟨42443872076856008441475593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28295914717904005627650395 42443872076856008441475593)
      ·
        refine ⟨31832904057642006331106695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42443872076856008441475593 31832904057642006331106695)
        ·
          refine ⟨47749356086463009496660043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31832904057642006331106695 47749356086463009496660043)
          ·
            refine ⟨71624034129694514244990065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47749356086463009496660043 71624034129694514244990065)
            ·
              refine ⟨53718025597270885683742549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71624034129694514244990065 53718025597270885683742549)
              ·
                refine ⟨314754056234009095803179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 53718025597270885683742549 314754056234009095803179)
                ·
                  refine ⟨472131084351013643704769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314754056234009095803179 472131084351013643704769)
                  ·
                    refine ⟨354098313263260232778577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 472131084351013643704769 354098313263260232778577)
                    ·
                      refine ⟨265573734947445174583933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 354098313263260232778577 265573734947445174583933)
                      ·
                        rfl

theorem cell23_517203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 1, 2, 2].length) (baseStart_517203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517203 prefixEnd_517203 := by exact prefixLift 517203
  have htrace : WordTrace (prefixWord ++ tailWord_517203) baseStart_517203 baseEnd_517203 := by
    simpa [prefixWord, tailWord_517203, baseEnd_517203] using wordTrace_append hprefix tailTrace_517203
  have hstable : (prefixWord ++ tailWord_517203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517203).length < 2 ^ (prefixWord ++ tailWord_517203).sum := by decide
  have hdescent : baseEnd_517203 < baseStart_517203 := by decide
  rcases family_descends (prefixWord ++ tailWord_517203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517213 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 4, 4]
def baseStart_517213 : Nat := 118140960795 + 517213 * 2 ^ 59
def prefixEnd_517213 : Nat := 4983230072969 + 3 ^ 40 * 517213 * 2
def baseEnd_517213 : Nat := 88526289917996711819629

theorem tailTrace_517213 : CollatzResearch.WordTrace tailWord_517213 prefixEnd_517213 88526289917996711819629 := by
  unfold tailWord_517213
  simp only [CollatzResearch.WordTrace]
  refine ⟨18864307875233108792964293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12576205250155405861976195 18864307875233108792964293)
  ·
    refine ⟨3537057726606207898680805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18864307875233108792964293 3537057726606207898680805)
    ·
      refine ⟨663198323738663981002651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3537057726606207898680805 663198323738663981002651)
      ·
        refine ⟨994797485607995971503977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663198323738663981002651 994797485607995971503977)
        ·
          refine ⟨746098114205996978627983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 994797485607995971503977 746098114205996978627983)
          ·
            refine ⟨1119147171308995467941975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746098114205996978627983 1119147171308995467941975)
            ·
              refine ⟨1678720756963493201912963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119147171308995467941975 1678720756963493201912963)
              ·
                refine ⟨2518081135445239802869445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1678720756963493201912963 2518081135445239802869445)
                ·
                  refine ⟨472140212895982463038021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2518081135445239802869445 472140212895982463038021)
                  ·
                    refine ⟨88526289917996711819629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 472140212895982463038021 88526289917996711819629)
                    ·
                      rfl

theorem cell23_517213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_517213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517213 prefixEnd_517213 := by exact prefixLift 517213
  have htrace : WordTrace (prefixWord ++ tailWord_517213) baseStart_517213 baseEnd_517213 := by
    simpa [prefixWord, tailWord_517213, baseEnd_517213] using wordTrace_append hprefix tailTrace_517213
  have hstable : (prefixWord ++ tailWord_517213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517213).length < 2 ^ (prefixWord ++ tailWord_517213).sum := by decide
  have hdescent : baseEnd_517213 < baseStart_517213 := by decide
  rcases family_descends (prefixWord ++ tailWord_517213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517249 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_517249 : Nat := 118140960795 + 517249 * 2 ^ 59
def prefixEnd_517249 : Nat := 4983230072969 + 3 ^ 40 * 517249 * 2
def baseEnd_517249 : Nat := 265597355057551994608721

theorem tailTrace_517249 : CollatzResearch.WordTrace tailWord_517249 prefixEnd_517249 265597355057551994608721 := by
  unfold tailWord_517249
  simp only [CollatzResearch.WordTrace]
  refine ⟨18865620903102686941274801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12577080602068457960849867 18865620903102686941274801)
  ·
    refine ⟨14149215677327015205956101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18865620903102686941274801 14149215677327015205956101)
    ·
      refine ⟨2652977939498815351116769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14149215677327015205956101 2652977939498815351116769)
      ·
        refine ⟨1989733454624111513337577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2652977939498815351116769 1989733454624111513337577)
        ·
          refine ⟨1492300090968083635003183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1989733454624111513337577 1492300090968083635003183)
          ·
            refine ⟨2238450136452125452504775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492300090968083635003183 2238450136452125452504775)
            ·
              refine ⟨3357675204678188178757163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2238450136452125452504775 3357675204678188178757163)
              ·
                refine ⟨5036512807017282268135745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357675204678188178757163 5036512807017282268135745)
                ·
                  refine ⟨3777384605262961701101809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5036512807017282268135745 3777384605262961701101809)
                  ·
                    refine ⟨2833038453947221275826357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3777384605262961701101809 2833038453947221275826357)
                    ·
                      refine ⟨265597355057551994608721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2833038453947221275826357 265597355057551994608721)
                      ·
                        rfl

theorem cell23_517249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_517249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517249 prefixEnd_517249 := by exact prefixLift 517249
  have htrace : WordTrace (prefixWord ++ tailWord_517249) baseStart_517249 baseEnd_517249 := by
    simpa [prefixWord, tailWord_517249, baseEnd_517249] using wordTrace_append hprefix tailTrace_517249
  have hstable : (prefixWord ++ tailWord_517249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517249).length < 2 ^ (prefixWord ++ tailWord_517249).sum := by decide
  have hdescent : baseEnd_517249 < baseStart_517249 := by decide
  rcases family_descends (prefixWord ++ tailWord_517249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517287 : List Nat := [1, 1, 6, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_517287 : Nat := 118140960795 + 517287 * 2 ^ 59
def prefixEnd_517287 : Nat := 4983230072969 + 3 ^ 40 * 517287 * 2
def baseEnd_517287 : Nat := 265616867322422845933547

theorem tailTrace_517287 : CollatzResearch.WordTrace tailWord_517287 prefixEnd_517287 265616867322422845933547 := by
  unfold tailWord_517287
  simp only [CollatzResearch.WordTrace]
  refine ⟨18867006876965019431158115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12578004584643346287438743 18867006876965019431158115)
  ·
    refine ⟨28300510315447529146737173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18867006876965019431158115 28300510315447529146737173)
    ·
      refine ⟨1326586421036602928753305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28300510315447529146737173 1326586421036602928753305)
      ·
        refine ⟨994939815777452196564979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1326586421036602928753305 994939815777452196564979)
        ·
          refine ⟨1492409723666178294847469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994939815777452196564979 1492409723666178294847469)
          ·
            refine ⟨559653646374816860567801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1492409723666178294847469 559653646374816860567801)
            ·
              refine ⟨419740234781112645425851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 559653646374816860567801 419740234781112645425851)
              ·
                refine ⟨629610352171668968138777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419740234781112645425851 629610352171668968138777)
                ·
                  refine ⟨472207764128751726104083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629610352171668968138777 472207764128751726104083)
                  ·
                    refine ⟨708311646193127589156125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 472207764128751726104083 708311646193127589156125)
                    ·
                      refine ⟨265616867322422845933547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 708311646193127589156125 265616867322422845933547)
                      ·
                        rfl

theorem cell23_517287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_517287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517287 prefixEnd_517287 := by exact prefixLift 517287
  have htrace : WordTrace (prefixWord ++ tailWord_517287) baseStart_517287 baseEnd_517287 := by
    simpa [prefixWord, tailWord_517287, baseEnd_517287] using wordTrace_append hprefix tailTrace_517287
  have hstable : (prefixWord ++ tailWord_517287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517287).length < 2 ^ (prefixWord ++ tailWord_517287).sum := by decide
  have hdescent : baseEnd_517287 < baseStart_517287 := by decide
  rcases family_descends (prefixWord ++ tailWord_517287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517333 : List Nat := [1, 3, 2, 4, 1, 2, 1, 4, 5]
def baseStart_517333 : Nat := 118140960795 + 517333 * 2 ^ 59
def prefixEnd_517333 : Nat := 4983230072969 + 3 ^ 40 * 517333 * 2
def baseEnd_517333 : Nat := 29515609714725518439815

theorem tailTrace_517333 : CollatzResearch.WordTrace tailWord_517333 prefixEnd_517333 29515609714725518439815 := by
  unfold tailWord_517333
  simp only [CollatzResearch.WordTrace]
  refine ⟨18868684634798369287332653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12579123089865579524888435 18868684634798369287332653)
  ·
    refine ⟨7075756738049388482749745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18868684634798369287332653 7075756738049388482749745)
    ·
      refine ⟨5306817553537041362062309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7075756738049388482749745 5306817553537041362062309)
      ·
        refine ⟨995028291288195255386683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5306817553537041362062309 995028291288195255386683)
        ·
          refine ⟨1492542436932292883080025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995028291288195255386683 1492542436932292883080025)
          ·
            refine ⟨1119406827699219662310019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1492542436932292883080025 1119406827699219662310019)
            ·
              refine ⟨1679110241548829493465029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119406827699219662310019 1679110241548829493465029)
              ·
                refine ⟨314833170290405530024693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1679110241548829493465029 314833170290405530024693)
                ·
                  refine ⟨29515609714725518439815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 314833170290405530024693 29515609714725518439815)
                  ·
                    rfl

theorem cell23_517333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 5].length) (baseStart_517333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517333 prefixEnd_517333 := by exact prefixLift 517333
  have htrace : WordTrace (prefixWord ++ tailWord_517333) baseStart_517333 baseEnd_517333 := by
    simpa [prefixWord, tailWord_517333, baseEnd_517333] using wordTrace_append hprefix tailTrace_517333
  have hstable : (prefixWord ++ tailWord_517333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517333).length < 2 ^ (prefixWord ++ tailWord_517333).sum := by decide
  have hdescent : baseEnd_517333 < baseStart_517333 := by decide
  rcases family_descends (prefixWord ++ tailWord_517333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517379 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 6]
def baseStart_517379 : Nat := 118140960795 + 517379 * 2 ^ 59
def prefixEnd_517379 : Nat := 4983230072969 + 3 ^ 40 * 517379 * 2
def baseEnd_517379 : Nat := 265664107542636485983123

theorem tailTrace_517379 : CollatzResearch.WordTrace tailWord_517379 prefixEnd_517379 265664107542636485983123 := by
  unfold tailWord_517379
  simp only [CollatzResearch.WordTrace]
  refine ⟨18870362392631719143507191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12580241595087812762338127 18870362392631719143507191)
  ·
    refine ⟨28305543588947578715260787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18870362392631719143507191 28305543588947578715260787)
    ·
      refine ⟨42458315383421368072891181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28305543588947578715260787 42458315383421368072891181)
      ·
        refine ⟨15921868268783013027334193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42458315383421368072891181 15921868268783013027334193)
        ·
          refine ⟨11941401201587259770500645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15921868268783013027334193 11941401201587259770500645)
          ·
            refine ⟨2239012725297611206968871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11941401201587259770500645 2239012725297611206968871)
            ·
              refine ⟨3358519087946416810453307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239012725297611206968871 3358519087946416810453307)
              ·
                refine ⟨5037778631919625215679961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3358519087946416810453307 5037778631919625215679961)
                ·
                  refine ⟨3778333973939718911759971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5037778631919625215679961 3778333973939718911759971)
                  ·
                    refine ⟨5667500960909578367639957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3778333973939718911759971 5667500960909578367639957)
                    ·
                      refine ⟨265664107542636485983123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5667500960909578367639957 265664107542636485983123)
                      ·
                        rfl

theorem cell23_517379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_517379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517379 prefixEnd_517379 := by exact prefixLift 517379
  have htrace : WordTrace (prefixWord ++ tailWord_517379) baseStart_517379 baseEnd_517379 := by
    simpa [prefixWord, tailWord_517379, baseEnd_517379] using wordTrace_append hprefix tailTrace_517379
  have hstable : (prefixWord ++ tailWord_517379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517379).length < 2 ^ (prefixWord ++ tailWord_517379).sum := by decide
  have hdescent : baseEnd_517379 < baseStart_517379 := by decide
  rcases family_descends (prefixWord ++ tailWord_517379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517386 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3]
def baseStart_517386 : Nat := 118140960795 + 517386 * 2 ^ 59
def prefixEnd_517386 : Nat := 4983230072969 + 3 ^ 40 * 517386 * 2
def baseEnd_517386 : Nat := 265667701907217958595591

theorem tailTrace_517386 : CollatzResearch.WordTrace tailWord_517386 prefixEnd_517386 265667701907217958595591 := by
  unfold tailWord_517386
  simp only [CollatzResearch.WordTrace]
  refine ⟨4717654425901589834753003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12580411802404239559341341 4717654425901589834753003)
  ·
    refine ⟨7076481638852384752129505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4717654425901589834753003 7076481638852384752129505)
    ·
      refine ⟨5307361229139288564097129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7076481638852384752129505 5307361229139288564097129)
      ·
        refine ⟨3980520921854466423072847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5307361229139288564097129 3980520921854466423072847)
        ·
          refine ⟨5970781382781699634609271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3980520921854466423072847 5970781382781699634609271)
          ·
            refine ⟨8956172074172549451913907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5970781382781699634609271 8956172074172549451913907)
            ·
              refine ⟨13434258111258824177870861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8956172074172549451913907 13434258111258824177870861)
              ·
                refine ⟨5037846791722059066701573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13434258111258824177870861 5037846791722059066701573)
                ·
                  refine ⟨944596273447886075006545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5037846791722059066701573 944596273447886075006545)
                  ·
                    refine ⟨708447205085914556254909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 944596273447886075006545 708447205085914556254909)
                    ·
                      refine ⟨265667701907217958595591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 708447205085914556254909 265667701907217958595591)
                      ·
                        rfl

theorem cell23_517386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_517386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517386 prefixEnd_517386 := by exact prefixLift 517386
  have htrace : WordTrace (prefixWord ++ tailWord_517386) baseStart_517386 baseEnd_517386 := by
    simpa [prefixWord, tailWord_517386, baseEnd_517386] using wordTrace_append hprefix tailTrace_517386
  have hstable : (prefixWord ++ tailWord_517386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517386).length < 2 ^ (prefixWord ++ tailWord_517386).sum := by decide
  have hdescent : baseEnd_517386 < baseStart_517386 := by decide
  rcases family_descends (prefixWord ++ tailWord_517386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517393 : List Nat := [1, 2, 2, 1, 1, 4, 1, 6, 1, 4]
def baseStart_517393 : Nat := 118140960795 + 517393 * 2 ^ 59
def prefixEnd_517393 : Nat := 4983230072969 + 3 ^ 40 * 517393 * 2
def baseEnd_517393 : Nat := 88557098757266477069353

theorem tailTrace_517393 : CollatzResearch.WordTrace tailWord_517393 prefixEnd_517393 88557098757266477069353 := by
  unfold tailWord_517393
  simp only [CollatzResearch.WordTrace]
  refine ⟨18870873014580999534516833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12580582009720666356344555 18870873014580999534516833)
  ·
    refine ⟨14153154760935749650887625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18870873014580999534516833 14153154760935749650887625)
    ·
      refine ⟨10614866070701812238165719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14153154760935749650887625 10614866070701812238165719)
      ·
        refine ⟨15922299106052718357248579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10614866070701812238165719 15922299106052718357248579)
        ·
          refine ⟨23883448659079077535872869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15922299106052718357248579 23883448659079077535872869)
          ·
            refine ⟨4478146623577327037976163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23883448659079077535872869 4478146623577327037976163)
            ·
              refine ⟨6717219935365990556964245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4478146623577327037976163 6717219935365990556964245)
              ·
                refine ⟨314869684470280807357699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6717219935365990556964245 314869684470280807357699)
                ·
                  refine ⟨472304526705421211036549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314869684470280807357699 472304526705421211036549)
                  ·
                    refine ⟨88557098757266477069353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 472304526705421211036549 88557098757266477069353)
                    ·
                      rfl

theorem cell23_517393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 1, 4].length) (baseStart_517393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517393 prefixEnd_517393 := by exact prefixLift 517393
  have htrace : WordTrace (prefixWord ++ tailWord_517393) baseStart_517393 baseEnd_517393 := by
    simpa [prefixWord, tailWord_517393, baseEnd_517393] using wordTrace_append hprefix tailTrace_517393
  have hstable : (prefixWord ++ tailWord_517393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517393).length < 2 ^ (prefixWord ++ tailWord_517393).sum := by decide
  have hdescent : baseEnd_517393 < baseStart_517393 := by decide
  rcases family_descends (prefixWord ++ tailWord_517393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517409 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_517409 : Nat := 118140960795 + 517409 * 2 ^ 59
def prefixEnd_517409 : Nat := 4983230072969 + 3 ^ 40 * 517409 * 2
def baseEnd_517409 : Nat := 265679511962271368607985

theorem tailTrace_517409 : CollatzResearch.WordTrace tailWord_517409 prefixEnd_517409 265679511962271368607985 := by
  unfold tailWord_517409
  simp only [CollatzResearch.WordTrace]
  refine ⟨18871456582523034267099281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12580971055015356178066187 18871456582523034267099281)
  ·
    refine ⟨14153592436892275700324461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18871456582523034267099281 14153592436892275700324461)
    ·
      refine ⟨5307597163834603387621673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14153592436892275700324461 5307597163834603387621673)
      ·
        refine ⟨3980697872875952540716255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5307597163834603387621673 3980697872875952540716255)
        ·
          refine ⟨5971046809313928811074383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3980697872875952540716255 5971046809313928811074383)
          ·
            refine ⟨8956570213970893216611575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5971046809313928811074383 8956570213970893216611575)
            ·
              refine ⟨13434855320956339824917363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8956570213970893216611575 13434855320956339824917363)
              ·
                refine ⟨20152282981434509737376045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13434855320956339824917363 20152282981434509737376045)
                ·
                  refine ⟨7557106118037941151516017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20152282981434509737376045 7557106118037941151516017)
                  ·
                    refine ⟨5667829588528455863637013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7557106118037941151516017 5667829588528455863637013)
                    ·
                      refine ⟨265679511962271368607985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5667829588528455863637013 265679511962271368607985)
                      ·
                        rfl

theorem cell23_517409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_517409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517409 prefixEnd_517409 := by exact prefixLift 517409
  have htrace : WordTrace (prefixWord ++ tailWord_517409) baseStart_517409 baseEnd_517409 := by
    simpa [prefixWord, tailWord_517409, baseEnd_517409] using wordTrace_append hprefix tailTrace_517409
  have hstable : (prefixWord ++ tailWord_517409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517409).length < 2 ^ (prefixWord ++ tailWord_517409).sum := by decide
  have hdescent : baseEnd_517409 < baseStart_517409 := by decide
  rcases family_descends (prefixWord ++ tailWord_517409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517444 : List Nat := [2, 3, 4, 1, 1, 2, 3, 2, 1, 4]
def baseStart_517444 : Nat := 118140960795 + 517444 * 2 ^ 59
def prefixEnd_517444 : Nat := 4983230072969 + 3 ^ 40 * 517444 * 2
def baseEnd_517444 : Nat := 88565827928392910556775

theorem tailTrace_517444 : CollatzResearch.WordTrace tailWord_517444 prefixEnd_517444 88565827928392910556775 := by
  unfold tailWord_517444
  simp only [CollatzResearch.WordTrace]
  refine ⟨9436366568698117622311693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12581822091597490163082257 9436366568698117622311693)
  ·
    refine ⟨3538637463261794108366885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9436366568698117622311693 3538637463261794108366885)
    ·
      refine ⟨663494524361586395318791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3538637463261794108366885 663494524361586395318791)
      ·
        refine ⟨995241786542379592978187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663494524361586395318791 995241786542379592978187)
        ·
          refine ⟨1492862679813569389467281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995241786542379592978187 1492862679813569389467281)
          ·
            refine ⟨1119647009860177042100461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1492862679813569389467281 1119647009860177042100461)
            ·
              refine ⟨419867628697566390787673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1119647009860177042100461 419867628697566390787673)
              ·
                refine ⟨314900721523174793090755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419867628697566390787673 314900721523174793090755)
                ·
                  refine ⟨472351082284762189636133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314900721523174793090755 472351082284762189636133)
                  ·
                    refine ⟨88565827928392910556775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 472351082284762189636133 88565827928392910556775)
                    ·
                      rfl

theorem cell23_517444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_517444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517444 prefixEnd_517444 := by exact prefixLift 517444
  have htrace : WordTrace (prefixWord ++ tailWord_517444) baseStart_517444 baseEnd_517444 := by
    simpa [prefixWord, tailWord_517444, baseEnd_517444] using wordTrace_append hprefix tailTrace_517444
  have hstable : (prefixWord ++ tailWord_517444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517444).length < 2 ^ (prefixWord ++ tailWord_517444).sum := by decide
  have hdescent : baseEnd_517444 < baseStart_517444 := by decide
  rcases family_descends (prefixWord ++ tailWord_517444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517450 : List Nat := [3, 1, 2, 1, 1, 1, 1, 8, 1, 1, 3]
def baseStart_517450 : Nat := 118140960795 + 517450 * 2 ^ 59
def prefixEnd_517450 : Nat := 4983230072969 + 3 ^ 40 * 517450 * 2
def baseEnd_517450 : Nat := 265700564669105708195297

theorem tailTrace_517450 : CollatzResearch.WordTrace tailWord_517450 prefixEnd_517450 265700564669105708195297 := by
  unfold tailWord_517450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4718237993843624567335451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12581967983582998846227869 4718237993843624567335451)
  ·
    refine ⟨7077356990765436851003177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4718237993843624567335451 7077356990765436851003177)
    ·
      refine ⟨5308017743074077638252383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7077356990765436851003177 5308017743074077638252383)
      ·
        refine ⟨7962026614611116457378575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5308017743074077638252383 7962026614611116457378575)
        ·
          refine ⟨11943039921916674686067863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7962026614611116457378575 11943039921916674686067863)
          ·
            refine ⟨17914559882875012029101795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11943039921916674686067863 17914559882875012029101795)
            ·
              refine ⟨26871839824312518043652693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17914559882875012029101795 26871839824312518043652693)
              ·
                refine ⟨314904372941162320824055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 26871839824312518043652693 314904372941162320824055)
                ·
                  refine ⟨472356559411743481236083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314904372941162320824055 472356559411743481236083)
                  ·
                    refine ⟨708534839117615221854125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 472356559411743481236083 708534839117615221854125)
                    ·
                      refine ⟨265700564669105708195297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 708534839117615221854125 265700564669105708195297)
                      ·
                        rfl

theorem cell23_517450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 1, 1, 3].length) (baseStart_517450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517450 prefixEnd_517450 := by exact prefixLift 517450
  have htrace : WordTrace (prefixWord ++ tailWord_517450) baseStart_517450 baseEnd_517450 := by
    simpa [prefixWord, tailWord_517450, baseEnd_517450] using wordTrace_append hprefix tailTrace_517450
  have hstable : (prefixWord ++ tailWord_517450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517450).length < 2 ^ (prefixWord ++ tailWord_517450).sum := by decide
  have hdescent : baseEnd_517450 < baseStart_517450 := by decide
  rcases family_descends (prefixWord ++ tailWord_517450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517456 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 4]
def baseStart_517456 : Nat := 118140960795 + 517456 * 2 ^ 59
def prefixEnd_517456 : Nat := 4983230072969 + 3 ^ 40 * 517456 * 2
def baseEnd_517456 : Nat := 265703645553032684720269

theorem tailTrace_517456 : CollatzResearch.WordTrace tailWord_517456 prefixEnd_517456 265703645553032684720269 := by
  unfold tailWord_517456
  simp only [CollatzResearch.WordTrace]
  refine ⟨9436585406676380647030111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12582113875568507529373481 9436585406676380647030111)
  ·
    refine ⟨14154878110014570970545167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9436585406676380647030111 14154878110014570970545167)
    ·
      refine ⟨21232317165021856455817751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14154878110014570970545167 21232317165021856455817751)
      ·
        refine ⟨31848475747532784683726627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21232317165021856455817751 31848475747532784683726627)
        ·
          refine ⟨47772713621299177025589941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31848475747532784683726627 47772713621299177025589941)
          ·
            refine ⟨4478691901996797846149057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47772713621299177025589941 4478691901996797846149057)
            ·
              refine ⟨3359018926497598384611793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4478691901996797846149057 3359018926497598384611793)
              ·
                refine ⟨2519264194873198788458845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3359018926497598384611793 2519264194873198788458845)
                ·
                  refine ⟨944724073077449545672067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2519264194873198788458845 944724073077449545672067)
                  ·
                    refine ⟨1417086109616174318508101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 944724073077449545672067 1417086109616174318508101)
                    ·
                      refine ⟨265703645553032684720269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1417086109616174318508101 265703645553032684720269)
                      ·
                        rfl

theorem cell23_517456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 4].length) (baseStart_517456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517456 prefixEnd_517456 := by exact prefixLift 517456
  have htrace : WordTrace (prefixWord ++ tailWord_517456) baseStart_517456 baseEnd_517456 := by
    simpa [prefixWord, tailWord_517456, baseEnd_517456] using wordTrace_append hprefix tailTrace_517456
  have hstable : (prefixWord ++ tailWord_517456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517456).length < 2 ^ (prefixWord ++ tailWord_517456).sum := by decide
  have hdescent : baseEnd_517456 < baseStart_517456 := by decide
  rcases family_descends (prefixWord ++ tailWord_517456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517490 : List Nat := [3, 2, 1, 2, 1, 2, 5, 1, 1, 1, 4]
def baseStart_517490 : Nat := 118140960795 + 517490 * 2 ^ 59
def prefixEnd_517490 : Nat := 4983230072969 + 3 ^ 40 * 517490 * 2
def baseEnd_517490 : Nat := 265721103895285551695113

theorem tailTrace_517490 : CollatzResearch.WordTrace tailWord_517490 prefixEnd_517490 265721103895285551695113 := by
  unfold tailWord_517490
  simp only [CollatzResearch.WordTrace]
  refine ⟨4718602723807396275199481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12582940596819723400531949 4718602723807396275199481)
  ·
    refine ⟨3538952042855547206399611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4718602723807396275199481 3538952042855547206399611)
    ·
      refine ⟨5308428064283320809599417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3538952042855547206399611 5308428064283320809599417)
      ·
        refine ⟨3981321048212490607199563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5308428064283320809599417 3981321048212490607199563)
        ·
          refine ⟨5971981572318735910799345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3981321048212490607199563 5971981572318735910799345)
          ·
            refine ⟨4478986179239051933099509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5971981572318735910799345 4478986179239051933099509)
            ·
              refine ⟨419904954303661118728079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4478986179239051933099509 419904954303661118728079)
              ·
                refine ⟨629857431455491678092119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419904954303661118728079 629857431455491678092119)
                ·
                  refine ⟨944786147183237517138179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629857431455491678092119 944786147183237517138179)
                  ·
                    refine ⟨1417179220774856275707269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 944786147183237517138179 1417179220774856275707269)
                    ·
                      refine ⟨265721103895285551695113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1417179220774856275707269 265721103895285551695113)
                      ·
                        rfl

theorem cell23_517490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_517490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517490 prefixEnd_517490 := by exact prefixLift 517490
  have htrace : WordTrace (prefixWord ++ tailWord_517490) baseStart_517490 baseEnd_517490 := by
    simpa [prefixWord, tailWord_517490, baseEnd_517490] using wordTrace_append hprefix tailTrace_517490
  have hstable : (prefixWord ++ tailWord_517490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517490).length < 2 ^ (prefixWord ++ tailWord_517490).sum := by decide
  have hdescent : baseEnd_517490 < baseStart_517490 := by decide
  rcases family_descends (prefixWord ++ tailWord_517490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517513 : List Nat := [1, 2, 1, 1, 7, 2, 1, 8]
def baseStart_517513 : Nat := 118140960795 + 517513 * 2 ^ 59
def prefixEnd_517513 : Nat := 4983230072969 + 3 ^ 40 * 517513 * 2
def baseEnd_517513 : Nat := 9841959775938480063241

theorem tailTrace_517513 : CollatzResearch.WordTrace tailWord_517513 prefixEnd_517513 9841959775938480063241 := by
  unfold tailWord_517513
  simp only [CollatzResearch.WordTrace]
  refine ⟨18875249774146260028885193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12583499849430840019256795 18875249774146260028885193)
  ·
    refine ⟨14156437330609695021663895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18875249774146260028885193 14156437330609695021663895)
    ·
      refine ⟨21234655995914542532495843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14156437330609695021663895 21234655995914542532495843)
      ·
        refine ⟨31851983993871813798743765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21234655995914542532495843 31851983993871813798743765)
        ·
          refine ⟨746530874856370635908057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 31851983993871813798743765 746530874856370635908057)
          ·
            refine ⟨559898156142277976931043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 746530874856370635908057 559898156142277976931043)
            ·
              refine ⟨839847234213416965396565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559898156142277976931043 839847234213416965396565)
              ·
                refine ⟨9841959775938480063241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 839847234213416965396565 9841959775938480063241)
                ·
                  rfl

theorem cell23_517513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 8].length) (baseStart_517513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517513 prefixEnd_517513 := by exact prefixLift 517513
  have htrace : WordTrace (prefixWord ++ tailWord_517513) baseStart_517513 baseEnd_517513 := by
    simpa [prefixWord, tailWord_517513, baseEnd_517513] using wordTrace_append hprefix tailTrace_517513
  have hstable : (prefixWord ++ tailWord_517513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517513).length < 2 ^ (prefixWord ++ tailWord_517513).sum := by decide
  have hdescent : baseEnd_517513 < baseStart_517513 := by decide
  rcases family_descends (prefixWord ++ tailWord_517513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517536 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 5]
def baseStart_517536 : Nat := 118140960795 + 517536 * 2 ^ 59
def prefixEnd_517536 : Nat := 4983230072969 + 3 ^ 40 * 517536 * 2
def baseEnd_517536 : Nat := 265744724005392371719901

theorem tailTrace_517536 : CollatzResearch.WordTrace tailWord_517536 prefixEnd_517536 265744724005392371719901 := by
  unfold tailWord_517536
  simp only [CollatzResearch.WordTrace]
  refine ⟨9438044326531467478486231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12584059102041956637981641 9438044326531467478486231)
  ·
    refine ⟨14157066489797201217729347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9438044326531467478486231 14157066489797201217729347)
    ·
      refine ⟨21235599734695801826594021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14157066489797201217729347 21235599734695801826594021)
      ·
        refine ⟨3981674950255462842486379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21235599734695801826594021 3981674950255462842486379)
        ·
          refine ⟨5972512425383194263729569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3981674950255462842486379 5972512425383194263729569)
          ·
            refine ⟨4479384319037395697797177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5972512425383194263729569 4479384319037395697797177)
            ·
              refine ⟨3359538239278046773347883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4479384319037395697797177 3359538239278046773347883)
              ·
                refine ⟨5039307358917070160021825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3359538239278046773347883 5039307358917070160021825)
                ·
                  refine ⟨3779480519187802620016369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5039307358917070160021825 3779480519187802620016369)
                  ·
                    refine ⟨2834610389390851965012277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3779480519187802620016369 2834610389390851965012277)
                    ·
                      refine ⟨265744724005392371719901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2834610389390851965012277 265744724005392371719901)
                      ·
                        rfl

theorem cell23_517536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_517536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517536 prefixEnd_517536 := by exact prefixLift 517536
  have htrace : WordTrace (prefixWord ++ tailWord_517536) baseStart_517536 baseEnd_517536 := by
    simpa [prefixWord, tailWord_517536, baseEnd_517536] using wordTrace_append hprefix tailTrace_517536
  have hstable : (prefixWord ++ tailWord_517536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517536).length < 2 ^ (prefixWord ++ tailWord_517536).sum := by decide
  have hdescent : baseEnd_517536 < baseStart_517536 := by decide
  rcases family_descends (prefixWord ++ tailWord_517536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517557 : List Nat := [1, 3, 3, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_517557 : Nat := 118140960795 + 517557 * 2 ^ 59
def prefixEnd_517557 : Nat := 4983230072969 + 3 ^ 40 * 517557 * 2
def baseEnd_517557 : Nat := 265755507099136789557305

theorem tailTrace_517557 : CollatzResearch.WordTrace tailWord_517557 prefixEnd_517557 265755507099136789557305 := by
  unfold tailWord_517557
  simp only [CollatzResearch.WordTrace]
  refine ⟨18876854585986855543486925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12584569723991237028991283 18876854585986855543486925)
  ·
    refine ⟨7078820469745070828807597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18876854585986855543486925 7078820469745070828807597)
    ·
      refine ⟨2654557676154401560802849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7078820469745070828807597 2654557676154401560802849)
      ·
        refine ⟨1990918257115801170602137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2654557676154401560802849 1990918257115801170602137)
        ·
          refine ⟨1493188692836850877951603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1990918257115801170602137 1493188692836850877951603)
          ·
            refine ⟨2239783039255276316927405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1493188692836850877951603 2239783039255276316927405)
            ·
              refine ⟨839918639720728618847777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2239783039255276316927405 839918639720728618847777)
              ·
                refine ⟨629938979790546464135833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839918639720728618847777 629938979790546464135833)
                ·
                  refine ⟨472454234842909848101875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629938979790546464135833 472454234842909848101875)
                  ·
                    refine ⟨708681352264364772152813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 472454234842909848101875 708681352264364772152813)
                    ·
                      refine ⟨265755507099136789557305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 708681352264364772152813 265755507099136789557305)
                      ·
                        rfl

theorem cell23_517557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_517557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517557 prefixEnd_517557 := by exact prefixLift 517557
  have htrace : WordTrace (prefixWord ++ tailWord_517557) baseStart_517557 baseEnd_517557 := by
    simpa [prefixWord, tailWord_517557, baseEnd_517557] using wordTrace_append hprefix tailTrace_517557
  have hstable : (prefixWord ++ tailWord_517557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517557).length < 2 ^ (prefixWord ++ tailWord_517557).sum := by decide
  have hdescent : baseEnd_517557 < baseStart_517557 := by decide
  rcases family_descends (prefixWord ++ tailWord_517557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517597 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_517597 : Nat := 118140960795 + 517597 * 2 ^ 59
def prefixEnd_517597 : Nat := 4983230072969 + 3 ^ 40 * 517597 * 2
def baseEnd_517597 : Nat := 265776046325316633057121

theorem tailTrace_517597 : CollatzResearch.WordTrace tailWord_517597 prefixEnd_517597 265776046325316633057121 := by
  unfold tailWord_517597
  simp only [CollatzResearch.WordTrace]
  refine ⟨18878313505841942374943045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12585542337227961583295363 18878313505841942374943045)
  ·
    refine ⟨3539683782345364195301821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18878313505841942374943045 3539683782345364195301821)
    ·
      refine ⟨1327381418379511573238183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3539683782345364195301821 1327381418379511573238183)
      ·
        refine ⟨1991072127569267359857275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1327381418379511573238183 1991072127569267359857275)
        ·
          refine ⟨2986608191353901039785913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991072127569267359857275 2986608191353901039785913)
          ·
            refine ⟨2239956143515425779839435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2986608191353901039785913 2239956143515425779839435)
            ·
              refine ⟨3359934215273138669759153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239956143515425779839435 3359934215273138669759153)
              ·
                refine ⟨2519950661454854002319365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3359934215273138669759153 2519950661454854002319365)
                ·
                  refine ⟨472490749022785125434881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2519950661454854002319365 472490749022785125434881)
                  ·
                    refine ⟨354368061767088844076161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 472490749022785125434881 354368061767088844076161)
                    ·
                      refine ⟨265776046325316633057121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 354368061767088844076161 265776046325316633057121)
                      ·
                        rfl

theorem cell23_517597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_517597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517597 prefixEnd_517597 := by exact prefixLift 517597
  have htrace : WordTrace (prefixWord ++ tailWord_517597) baseStart_517597 baseEnd_517597 := by
    simpa [prefixWord, tailWord_517597, baseEnd_517597] using wordTrace_append hprefix tailTrace_517597
  have hstable : (prefixWord ++ tailWord_517597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517597).length < 2 ^ (prefixWord ++ tailWord_517597).sum := by decide
  have hdescent : baseEnd_517597 < baseStart_517597 := by decide
  rcases family_descends (prefixWord ++ tailWord_517597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517714 : List Nat := [3, 2, 2, 1, 2, 3, 2, 3, 1, 4]
def baseStart_517714 : Nat := 118140960795 + 517714 * 2 ^ 59
def prefixEnd_517714 : Nat := 4983230072969 + 3 ^ 40 * 517714 * 2
def baseEnd_517714 : Nat := 88612041187297558431361

theorem tailTrace_517714 : CollatzResearch.WordTrace tailWord_517714 prefixEnd_517714 88612041187297558431361 := by
  unfold tailWord_517714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4720645211604517839238049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12588387230945380904634797 4720645211604517839238049)
  ·
    refine ⟨3540483908703388379428537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4720645211604517839238049 3540483908703388379428537)
    ·
      refine ⟨2655362931527541284571403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3540483908703388379428537 2655362931527541284571403)
      ·
        refine ⟨3983044397291311926857105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2655362931527541284571403 3983044397291311926857105)
        ·
          refine ⟨2987283297968483945142829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3983044397291311926857105 2987283297968483945142829)
          ·
            refine ⟨1120231236738181479428561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2987283297968483945142829 1120231236738181479428561)
            ·
              refine ⟨840173427553636109571421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120231236738181479428561 840173427553636109571421)
              ·
                refine ⟨315065035332613541089283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 840173427553636109571421 315065035332613541089283)
                ·
                  refine ⟨472597552998920311633925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315065035332613541089283 472597552998920311633925)
                  ·
                    refine ⟨88612041187297558431361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 472597552998920311633925 88612041187297558431361)
                    ·
                      rfl

theorem cell23_517714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_517714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517714 prefixEnd_517714 := by exact prefixLift 517714
  have htrace : WordTrace (prefixWord ++ tailWord_517714) baseStart_517714 baseEnd_517714 := by
    simpa [prefixWord, tailWord_517714, baseEnd_517714] using wordTrace_append hprefix tailTrace_517714
  have hstable : (prefixWord ++ tailWord_517714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517714).length < 2 ^ (prefixWord ++ tailWord_517714).sum := by decide
  have hdescent : baseEnd_517714 < baseStart_517714 := by decide
  rcases family_descends (prefixWord ++ tailWord_517714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517720 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 7, 1, 3]
def baseStart_517720 : Nat := 118140960795 + 517720 * 2 ^ 59
def prefixEnd_517720 : Nat := 4983230072969 + 3 ^ 40 * 517720 * 2
def baseEnd_517720 : Nat := 265839204445819651819055

theorem tailTrace_517720 : CollatzResearch.WordTrace tailWord_517720 prefixEnd_517720 265839204445819651819055 := by
  unfold tailWord_517720
  simp only [CollatzResearch.WordTrace]
  refine ⟨9441399842198167190835307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12588533122930889587780409 9441399842198167190835307)
  ·
    refine ⟨14162099763297250786252961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9441399842198167190835307 14162099763297250786252961)
    ·
      refine ⟨10621574822472938089689721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14162099763297250786252961 10621574822472938089689721)
      ·
        refine ⟨7966181116854703567267291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10621574822472938089689721 7966181116854703567267291)
        ·
          refine ⟨11949271675282055350900937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7966181116854703567267291 11949271675282055350900937)
          ·
            refine ⟨8961953756461541513175703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11949271675282055350900937 8961953756461541513175703)
            ·
              refine ⟨13442930634692312269763555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8961953756461541513175703 13442930634692312269763555)
              ·
                refine ⟨20164395952038468404645333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13442930634692312269763555 20164395952038468404645333)
                ·
                  refine ⟨472603030125901603233875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20164395952038468404645333 472603030125901603233875)
                  ·
                    refine ⟨708904545188852404850813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 472603030125901603233875 708904545188852404850813)
                    ·
                      refine ⟨265839204445819651819055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 708904545188852404850813 265839204445819651819055)
                      ·
                        rfl

theorem cell23_517720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_517720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517720 prefixEnd_517720 := by exact prefixLift 517720
  have htrace : WordTrace (prefixWord ++ tailWord_517720) baseStart_517720 baseEnd_517720 := by
    simpa [prefixWord, tailWord_517720, baseEnd_517720] using wordTrace_append hprefix tailTrace_517720
  have hstable : (prefixWord ++ tailWord_517720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517720).length < 2 ^ (prefixWord ++ tailWord_517720).sum := by decide
  have hdescent : baseEnd_517720 < baseStart_517720 := by decide
  rcases family_descends (prefixWord ++ tailWord_517720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517757 : List Nat := [1, 4, 1, 1, 4, 2, 2, 2, 1, 5]
def baseStart_517757 : Nat := 118140960795 + 517757 * 2 ^ 59
def prefixEnd_517757 : Nat := 4983230072969 + 3 ^ 40 * 517757 * 2
def baseEnd_517757 : Nat := 88619401076678669018795

theorem tailTrace_517757 : CollatzResearch.WordTrace tailWord_517757 prefixEnd_517757 88619401076678669018795 := by
  unfold tailWord_517757
  simp only [CollatzResearch.WordTrace]
  refine ⟨18884149185262289700767525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12589432790174859800511683 18884149185262289700767525)
  ·
    refine ⟨3540777972236679318893911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18884149185262289700767525 3540777972236679318893911)
    ·
      refine ⟨5311166958355018978340867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3540777972236679318893911 5311166958355018978340867)
      ·
        refine ⟨7966750437532528467511301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5311166958355018978340867 7966750437532528467511301)
        ·
          refine ⟨1493765707037349087658369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7966750437532528467511301 1493765707037349087658369)
          ·
            refine ⟨1120324280278011815743777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1493765707037349087658369 1120324280278011815743777)
            ·
              refine ⟨840243210208508861807833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120324280278011815743777 840243210208508861807833)
              ·
                refine ⟨630182407656381646355875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840243210208508861807833 630182407656381646355875)
                ·
                  refine ⟨945273611484572469533813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 630182407656381646355875 945273611484572469533813)
                  ·
                    refine ⟨88619401076678669018795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 945273611484572469533813 88619401076678669018795)
                    ·
                      rfl

theorem cell23_517757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_517757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517757 prefixEnd_517757 := by exact prefixLift 517757
  have htrace : WordTrace (prefixWord ++ tailWord_517757) baseStart_517757 baseEnd_517757 := by
    simpa [prefixWord, tailWord_517757, baseEnd_517757] using wordTrace_append hprefix tailTrace_517757
  have hstable : (prefixWord ++ tailWord_517757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517757).length < 2 ^ (prefixWord ++ tailWord_517757).sum := by decide
  have hdescent : baseEnd_517757 < baseStart_517757 := by decide
  rcases family_descends (prefixWord ++ tailWord_517757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517760 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 2, 6, 2]
def baseStart_517760 : Nat := 118140960795 + 517760 * 2 ^ 59
def prefixEnd_517760 : Nat := 4983230072969 + 3 ^ 40 * 517760 * 2
def baseEnd_517760 : Nat := 265859743671999495318871

theorem tailTrace_517760 : CollatzResearch.WordTrace tailWord_517760 prefixEnd_517760 265859743671999495318871 := by
  unfold tailWord_517760
  simp only [CollatzResearch.WordTrace]
  refine ⟨9442129302125710606563367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12589505736167614142084489 9442129302125710606563367)
  ·
    refine ⟨14163193953188565909845051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9442129302125710606563367 14163193953188565909845051)
    ·
      refine ⟨21244790929782848864767577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14163193953188565909845051 21244790929782848864767577)
      ·
        refine ⟨15933593197337136648575683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21244790929782848864767577 15933593197337136648575683)
        ·
          refine ⟨23900389796005704972863525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15933593197337136648575683 23900389796005704972863525)
          ·
            refine ⟨4481323086751069682411911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23900389796005704972863525 4481323086751069682411911)
            ·
              refine ⟨6721984630126604523617867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4481323086751069682411911 6721984630126604523617867)
              ·
                refine ⟨10082976945189906785426801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6721984630126604523617867 10082976945189906785426801)
                ·
                  refine ⟨7562232708892430089070101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10082976945189906785426801 7562232708892430089070101)
                  ·
                    refine ⟨354479658229332660425161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7562232708892430089070101 354479658229332660425161)
                    ·
                      refine ⟨265859743671999495318871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 354479658229332660425161 265859743671999495318871)
                      ·
                        rfl

theorem cell23_517760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 6, 2].length) (baseStart_517760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517760 prefixEnd_517760 := by exact prefixLift 517760
  have htrace : WordTrace (prefixWord ++ tailWord_517760) baseStart_517760 baseEnd_517760 := by
    simpa [prefixWord, tailWord_517760, baseEnd_517760] using wordTrace_append hprefix tailTrace_517760
  have hstable : (prefixWord ++ tailWord_517760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517760).length < 2 ^ (prefixWord ++ tailWord_517760).sum := by decide
  have hdescent : baseEnd_517760 < baseStart_517760 := by decide
  rcases family_descends (prefixWord ++ tailWord_517760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517763 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 5]
def baseStart_517763 : Nat := 118140960795 + 517763 * 2 ^ 59
def prefixEnd_517763 : Nat := 4983230072969 + 3 ^ 40 * 517763 * 2
def baseEnd_517763 : Nat := 265861284113962983581357

theorem tailTrace_517763 : CollatzResearch.WordTrace tailWord_517763 prefixEnd_517763 265861284113962983581357 := by
  unfold tailWord_517763
  simp only [CollatzResearch.WordTrace]
  refine ⟨18884368023240552725485943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12589578682160368483657295 18884368023240552725485943)
  ·
    refine ⟨28326552034860829088228915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18884368023240552725485943 28326552034860829088228915)
    ·
      refine ⟨42489828052291243632343373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28326552034860829088228915 42489828052291243632343373)
      ·
        refine ⟨15933685519609216362128765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42489828052291243632343373 15933685519609216362128765)
        ·
          refine ⟨5975132069853456135798287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15933685519609216362128765 5975132069853456135798287)
          ·
            refine ⟨8962698104780184203697431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5975132069853456135798287 8962698104780184203697431)
            ·
              refine ⟨13444047157170276305546147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8962698104780184203697431 13444047157170276305546147)
              ·
                refine ⟨20166070735755414458319221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13444047157170276305546147 20166070735755414458319221)
                ·
                  refine ⟨1890569131477070105467427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20166070735755414458319221 1890569131477070105467427)
                  ·
                    refine ⟨2835853697215605158201141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1890569131477070105467427 2835853697215605158201141)
                    ·
                      refine ⟨265861284113962983581357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2835853697215605158201141 265861284113962983581357)
                      ·
                        rfl

theorem cell23_517763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_517763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517763 prefixEnd_517763 := by exact prefixLift 517763
  have htrace : WordTrace (prefixWord ++ tailWord_517763) baseStart_517763 baseEnd_517763 := by
    simpa [prefixWord, tailWord_517763, baseEnd_517763] using wordTrace_append hprefix tailTrace_517763
  have hstable : (prefixWord ++ tailWord_517763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517763).length < 2 ^ (prefixWord ++ tailWord_517763).sum := by decide
  have hdescent : baseEnd_517763 < baseStart_517763 := by decide
  rcases family_descends (prefixWord ++ tailWord_517763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517783 : List Nat := [1, 1, 3, 3, 2, 2, 11]
def baseStart_517783 : Nat := 118140960795 + 517783 * 2 ^ 59
def prefixEnd_517783 : Nat := 4983230072969 + 3 ^ 40 * 517783 * 2
def baseEnd_517783 : Nat := 3282364860827813646065

theorem tailTrace_517783 : CollatzResearch.WordTrace tailWord_517783 prefixEnd_517783 3282364860827813646065 := by
  unfold tailWord_517783
  simp only [CollatzResearch.WordTrace]
  refine ⟨18885097483168096141214003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12590064988778730760809335 18885097483168096141214003)
  ·
    refine ⟨28327646224752144211821005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18885097483168096141214003 28327646224752144211821005)
    ·
      refine ⟨10622867334282054079432877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28327646224752144211821005 10622867334282054079432877)
      ·
        refine ⟨3983575250355770279787329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10622867334282054079432877 3983575250355770279787329)
        ·
          refine ⟨2987681437766827709840497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3983575250355770279787329 2987681437766827709840497)
          ·
            refine ⟨2240761078325120782380373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2987681437766827709840497 2240761078325120782380373)
            ·
              refine ⟨3282364860827813646065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2240761078325120782380373 3282364860827813646065)
              ·
                rfl

theorem cell23_517783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 11].length) (baseStart_517783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517783 prefixEnd_517783 := by exact prefixLift 517783
  have htrace : WordTrace (prefixWord ++ tailWord_517783) baseStart_517783 baseEnd_517783 := by
    simpa [prefixWord, tailWord_517783, baseEnd_517783] using wordTrace_append hprefix tailTrace_517783
  have hstable : (prefixWord ++ tailWord_517783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517783).length < 2 ^ (prefixWord ++ tailWord_517783).sum := by decide
  have hdescent : baseEnd_517783 < baseStart_517783 := by decide
  rcases family_descends (prefixWord ++ tailWord_517783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517788 : List Nat := [2, 2, 3, 2, 3, 1, 3, 2, 1, 1, 3]
def baseStart_517788 : Nat := 118140960795 + 517788 * 2 ^ 59
def prefixEnd_517788 : Nat := 4983230072969 + 3 ^ 40 * 517788 * 2
def baseEnd_517788 : Nat := 265874121130325385768743

theorem tailTrace_517788 : CollatzResearch.WordTrace tailWord_517788 prefixEnd_517788 265874121130325385768743 := by
  unfold tailWord_517788
  simp only [CollatzResearch.WordTrace]
  refine ⟨9442639924074990997573009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12590186565433321330097345 9442639924074990997573009)
  ·
    refine ⟨7081979943056243248179757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9442639924074990997573009 7081979943056243248179757)
    ·
      refine ⟨2655742478646091218067409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7081979943056243248179757 2655742478646091218067409)
      ·
        refine ⟨1991806858984568413550557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2655742478646091218067409 1991806858984568413550557)
        ·
          refine ⟨746927572119213155081459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1991806858984568413550557 746927572119213155081459)
          ·
            refine ⟨1120391358178819732622189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746927572119213155081459 1120391358178819732622189)
            ·
              refine ⟨420146759317057399733321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1120391358178819732622189 420146759317057399733321)
              ·
                refine ⟨315110069487793049799991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420146759317057399733321 315110069487793049799991)
                ·
                  refine ⟨472665104231689574699987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315110069487793049799991 472665104231689574699987)
                  ·
                    refine ⟨708997656347534362049981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 472665104231689574699987 708997656347534362049981)
                    ·
                      refine ⟨265874121130325385768743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 708997656347534362049981 265874121130325385768743)
                      ·
                        rfl

theorem cell23_517788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_517788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517788 prefixEnd_517788 := by exact prefixLift 517788
  have htrace : WordTrace (prefixWord ++ tailWord_517788) baseStart_517788 baseEnd_517788 := by
    simpa [prefixWord, tailWord_517788, baseEnd_517788] using wordTrace_append hprefix tailTrace_517788
  have hstable : (prefixWord ++ tailWord_517788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517788).length < 2 ^ (prefixWord ++ tailWord_517788).sum := by decide
  have hdescent : baseEnd_517788 < baseStart_517788 := by decide
  rcases family_descends (prefixWord ++ tailWord_517788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517850 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4]
def baseStart_517850 : Nat := 118140960795 + 517850 * 2 ^ 59
def prefixEnd_517850 : Nat := 4983230072969 + 3 ^ 40 * 517850 * 2
def baseEnd_517850 : Nat := 265905956930904143193457

theorem tailTrace_517850 : CollatzResearch.WordTrace tailWord_517850 prefixEnd_517850 265905956930904143193457 := by
  unfold tailWord_517850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4721885293481341645975751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12591694115950244389268669 4721885293481341645975751)
  ·
    refine ⟨7082827940222012468963627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4721885293481341645975751 7082827940222012468963627)
    ·
      refine ⟨10624241910333018703445441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7082827940222012468963627 10624241910333018703445441)
      ·
        refine ⟨7968181432749764027584081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10624241910333018703445441 7968181432749764027584081)
        ·
          refine ⟨5976136074562323020688061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7968181432749764027584081 5976136074562323020688061)
          ·
            refine ⟨2241051027960871132758023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5976136074562323020688061 2241051027960871132758023)
            ·
              refine ⟨3361576541941306699137035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2241051027960871132758023 3361576541941306699137035)
              ·
                refine ⟨5042364812911960048705553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3361576541941306699137035 5042364812911960048705553)
                ·
                  refine ⟨3781773609683970036529165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5042364812911960048705553 3781773609683970036529165)
                  ·
                    refine ⟨1418165103631488763698437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3781773609683970036529165 1418165103631488763698437)
                    ·
                      refine ⟨265905956930904143193457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1418165103631488763698437 265905956930904143193457)
                      ·
                        rfl

theorem cell23_517850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_517850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517850 prefixEnd_517850 := by exact prefixLift 517850
  have htrace : WordTrace (prefixWord ++ tailWord_517850) baseStart_517850 baseEnd_517850 := by
    simpa [prefixWord, tailWord_517850, baseEnd_517850] using wordTrace_append hprefix tailTrace_517850
  have hstable : (prefixWord ++ tailWord_517850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517850).length < 2 ^ (prefixWord ++ tailWord_517850).sum := by decide
  have hdescent : baseEnd_517850 < baseStart_517850 := by decide
  rcases family_descends (prefixWord ++ tailWord_517850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517860 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 2, 6]
def baseStart_517860 : Nat := 118140960795 + 517860 * 2 ^ 59
def prefixEnd_517860 : Nat := 4983230072969 + 3 ^ 40 * 517860 * 2
def baseEnd_517860 : Nat := 88637030579149701356137

theorem tailTrace_517860 : CollatzResearch.WordTrace tailWord_517860 prefixEnd_517860 88637030579149701356137 := by
  unfold tailWord_517860
  simp only [CollatzResearch.WordTrace]
  refine ⟨9443952951944569145883517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12591937269259425527844689 9443952951944569145883517)
  ·
    refine ⟨3541482356979213429706319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9443952951944569145883517 3541482356979213429706319)
    ·
      refine ⟨5312223535468820144559479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3541482356979213429706319 5312223535468820144559479)
      ·
        refine ⟨7968335303203230216839219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5312223535468820144559479 7968335303203230216839219)
        ·
          refine ⟨11952502954804845325258829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7968335303203230216839219 11952502954804845325258829)
          ·
            refine ⟨4482188608051816996972061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11952502954804845325258829 4482188608051816996972061)
            ·
              refine ⟨1680820728019431373864523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4482188608051816996972061 1680820728019431373864523)
              ·
                refine ⟨2521231092029147060796785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1680820728019431373864523 2521231092029147060796785)
                ·
                  refine ⟨1890923319021860295597589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2521231092029147060796785 1890923319021860295597589)
                  ·
                    refine ⟨88637030579149701356137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1890923319021860295597589 88637030579149701356137)
                    ·
                      rfl

theorem cell23_517860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_517860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517860 prefixEnd_517860 := by exact prefixLift 517860
  have htrace : WordTrace (prefixWord ++ tailWord_517860) baseStart_517860 baseEnd_517860 := by
    simpa [prefixWord, tailWord_517860, baseEnd_517860] using wordTrace_append hprefix tailTrace_517860
  have hstable : (prefixWord ++ tailWord_517860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517860).length < 2 ^ (prefixWord ++ tailWord_517860).sum := by decide
  have hdescent : baseEnd_517860 < baseStart_517860 := by decide
  rcases family_descends (prefixWord ++ tailWord_517860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517867 : List Nat := [1, 1, 1, 1, 2, 4, 3, 3, 1, 4, 2]
def baseStart_517867 : Nat := 118140960795 + 517867 * 2 ^ 59
def prefixEnd_517867 : Nat := 4983230072969 + 3 ^ 40 * 517867 * 2
def baseEnd_517867 : Nat := 265914686102030576680879

theorem tailTrace_517867 : CollatzResearch.WordTrace tailWord_517867 prefixEnd_517867 265914686102030576680879 := by
  unfold tailWord_517867
  simp only [CollatzResearch.WordTrace]
  refine ⟨18888161214863778487271855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12592107476575852324847903 18888161214863778487271855)
  ·
    refine ⟨28332241822295667730907783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18888161214863778487271855 28332241822295667730907783)
    ·
      refine ⟨42498362733443501596361675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28332241822295667730907783 42498362733443501596361675)
      ·
        refine ⟨63747544100165252394542513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42498362733443501596361675 63747544100165252394542513)
        ·
          refine ⟨47810658075123939295906885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63747544100165252394542513 47810658075123939295906885)
          ·
            refine ⟨8964498389085738617982541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47810658075123939295906885 8964498389085738617982541)
            ·
              refine ⟨3361686895907151981743453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8964498389085738617982541 3361686895907151981743453)
              ·
                refine ⟨1260632585965181993153795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3361686895907151981743453 1260632585965181993153795)
                ·
                  refine ⟨1890948878947772989730693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1260632585965181993153795 1890948878947772989730693)
                  ·
                    refine ⟨354552914802707435574505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1890948878947772989730693 354552914802707435574505)
                    ·
                      refine ⟨265914686102030576680879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 354552914802707435574505 265914686102030576680879)
                      ·
                        rfl

theorem cell23_517867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 4, 2].length) (baseStart_517867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517867 prefixEnd_517867 := by exact prefixLift 517867
  have htrace : WordTrace (prefixWord ++ tailWord_517867) baseStart_517867 baseEnd_517867 := by
    simpa [prefixWord, tailWord_517867, baseEnd_517867] using wordTrace_append hprefix tailTrace_517867
  have hstable : (prefixWord ++ tailWord_517867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517867).length < 2 ^ (prefixWord ++ tailWord_517867).sum := by decide
  have hdescent : baseEnd_517867 < baseStart_517867 := by decide
  rcases family_descends (prefixWord ++ tailWord_517867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517884 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 4, 2, 2]
def baseStart_517884 : Nat := 118140960795 + 517884 * 2 ^ 59
def prefixEnd_517884 : Nat := 4983230072969 + 3 ^ 40 * 517884 * 2
def baseEnd_517884 : Nat := 265923415273157010168301

theorem tailTrace_517884 : CollatzResearch.WordTrace tailWord_517884 prefixEnd_517884 265923415273157010168301 := by
  unfold tailWord_517884
  simp only [CollatzResearch.WordTrace]
  refine ⟨9444390627901095195320353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12592520837201460260427137 9444390627901095195320353)
  ·
    refine ⟨7083292970925821396490265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9444390627901095195320353 7083292970925821396490265)
    ·
      refine ⟨5312469728194366047367699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7083292970925821396490265 5312469728194366047367699)
      ·
        refine ⟨7968704592291549071051549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5312469728194366047367699 7968704592291549071051549)
        ·
          refine ⟨2988264222109330901644331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7968704592291549071051549 2988264222109330901644331)
          ·
            refine ⟨4482396333163996352466497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2988264222109330901644331 4482396333163996352466497)
            ·
              refine ⟨3361797249872997264349873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4482396333163996352466497 3361797249872997264349873)
              ·
                refine ⟨2521347937404747948262405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3361797249872997264349873 2521347937404747948262405)
                ·
                  refine ⟨472752738263390240299201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2521347937404747948262405 472752738263390240299201)
                  ·
                    refine ⟨354564553697542680224401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 472752738263390240299201 354564553697542680224401)
                    ·
                      refine ⟨265923415273157010168301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 354564553697542680224401 265923415273157010168301)
                      ·
                        rfl

theorem cell23_517884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_517884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517884 prefixEnd_517884 := by exact prefixLift 517884
  have htrace : WordTrace (prefixWord ++ tailWord_517884) baseStart_517884 baseEnd_517884 := by
    simpa [prefixWord, tailWord_517884, baseEnd_517884] using wordTrace_append hprefix tailTrace_517884
  have hstable : (prefixWord ++ tailWord_517884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517884).length < 2 ^ (prefixWord ++ tailWord_517884).sum := by decide
  have hdescent : baseEnd_517884 < baseStart_517884 := by decide
  rcases family_descends (prefixWord ++ tailWord_517884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517920 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 3, 7]
def baseStart_517920 : Nat := 118140960795 + 517920 * 2 ^ 59
def prefixEnd_517920 : Nat := 4983230072969 + 3 ^ 40 * 517920 * 2
def baseEnd_517920 : Nat := 88647300192239623106045

theorem tailTrace_517920 : CollatzResearch.WordTrace tailWord_517920 prefixEnd_517920 88647300192239623106045 := by
  unfold tailWord_517920
  simp only [CollatzResearch.WordTrace]
  refine ⟨9445047141835884269475607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12593396189114512359300809 9445047141835884269475607)
  ·
    refine ⟨14167570712753826404213411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9445047141835884269475607 14167570712753826404213411)
    ·
      refine ⟨21251356069130739606320117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14167570712753826404213411 21251356069130739606320117)
      ·
        refine ⟨1992314631481006838092511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21251356069130739606320117 1992314631481006838092511)
        ·
          refine ⟨2988471947221510257138767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1992314631481006838092511 2988471947221510257138767)
          ·
            refine ⟨4482707920832265385708151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2988471947221510257138767 4482707920832265385708151)
            ·
              refine ⟨6724061881248398078562227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4482707920832265385708151 6724061881248398078562227)
              ·
                refine ⟨10086092821872597117843341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6724061881248398078562227 10086092821872597117843341)
                ·
                  refine ⟨3782284808202223919191253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10086092821872597117843341 3782284808202223919191253)
                  ·
                    refine ⟨88647300192239623106045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3782284808202223919191253 88647300192239623106045)
                    ·
                      rfl

theorem cell23_517920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 3, 7].length) (baseStart_517920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517920 prefixEnd_517920 := by exact prefixLift 517920
  have htrace : WordTrace (prefixWord ++ tailWord_517920) baseStart_517920 baseEnd_517920 := by
    simpa [prefixWord, tailWord_517920, baseEnd_517920] using wordTrace_append hprefix tailTrace_517920
  have hstable : (prefixWord ++ tailWord_517920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517920).length < 2 ^ (prefixWord ++ tailWord_517920).sum := by decide
  have hdescent : baseEnd_517920 < baseStart_517920 := by decide
  rcases family_descends (prefixWord ++ tailWord_517920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517941 : List Nat := [1, 3, 3, 1, 4, 2, 1, 3, 5]
def baseStart_517941 : Nat := 118140960795 + 517941 * 2 ^ 59
def prefixEnd_517941 : Nat := 4983230072969 + 3 ^ 40 * 517941 * 2
def baseEnd_517941 : Nat := 29550298185607031906171

theorem tailTrace_517941 : CollatzResearch.WordTrace tailWord_517941 prefixEnd_517941 29550298185607031906171 := by
  unfold tailWord_517941
  simp only [CollatzResearch.WordTrace]
  refine ⟨18890860216595689125465677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12593906811063792750310451 18890860216595689125465677)
  ·
    refine ⟨7084072581223383422049629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18890860216595689125465677 7084072581223383422049629)
    ·
      refine ⟨2656527217958768783268611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7084072581223383422049629 2656527217958768783268611)
      ·
        refine ⟨3984790826938153174902917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2656527217958768783268611 3984790826938153174902917)
        ·
          refine ⟨747148280050903720294297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3984790826938153174902917 747148280050903720294297)
          ·
            refine ⟨560361210038177790220723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 747148280050903720294297 560361210038177790220723)
            ·
              refine ⟨840541815057266685331085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560361210038177790220723 840541815057266685331085)
              ·
                refine ⟨315203180646475006999157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 840541815057266685331085 315203180646475006999157)
                ·
                  refine ⟨29550298185607031906171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 315203180646475006999157 29550298185607031906171)
                  ·
                    rfl

theorem cell23_517941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 5].length) (baseStart_517941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517941 prefixEnd_517941 := by exact prefixLift 517941
  have htrace : WordTrace (prefixWord ++ tailWord_517941) baseStart_517941 baseEnd_517941 := by
    simpa [prefixWord, tailWord_517941, baseEnd_517941] using wordTrace_append hprefix tailTrace_517941
  have hstable : (prefixWord ++ tailWord_517941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517941).length < 2 ^ (prefixWord ++ tailWord_517941).sum := by decide
  have hdescent : baseEnd_517941 < baseStart_517941 := by decide
  rcases family_descends (prefixWord ++ tailWord_517941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517957 : List Nat := [1, 3, 1, 1, 1, 2, 5, 2, 2, 1, 4]
def baseStart_517957 : Nat := 118140960795 + 517957 * 2 ^ 59
def prefixEnd_517957 : Nat := 4983230072969 + 3 ^ 40 * 517957 * 2
def baseEnd_517957 : Nat := 265960899360935224555465

theorem tailTrace_517957 : CollatzResearch.WordTrace tailWord_517957 prefixEnd_517957 265960899360935224555465 := by
  unfold tailWord_517957
  simp only [CollatzResearch.WordTrace]
  refine ⟨18891443784537723858048125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12594295856358482572032083 18891443784537723858048125)
  ·
    refine ⟨7084291419201646446768047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18891443784537723858048125 7084291419201646446768047)
    ·
      refine ⟨10626437128802469670152071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7084291419201646446768047 10626437128802469670152071)
      ·
        refine ⟨15939655693203704505228107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10626437128802469670152071 15939655693203704505228107)
        ·
          refine ⟨23909483539805556757842161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15939655693203704505228107 23909483539805556757842161)
          ·
            refine ⟨17932112654854167568381621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23909483539805556757842161 17932112654854167568381621)
            ·
              refine ⟨1681135561392578209535777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17932112654854167568381621 1681135561392578209535777)
              ·
                refine ⟨1260851671044433657151833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1681135561392578209535777 1260851671044433657151833)
                ·
                  refine ⟨945638753283325242863875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1260851671044433657151833 945638753283325242863875)
                  ·
                    refine ⟨1418458129924987864295813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 945638753283325242863875 1418458129924987864295813)
                    ·
                      refine ⟨265960899360935224555465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1418458129924987864295813 265960899360935224555465)
                      ·
                        rfl

theorem cell23_517957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_517957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517957 prefixEnd_517957 := by exact prefixLift 517957
  have htrace : WordTrace (prefixWord ++ tailWord_517957) baseStart_517957 baseEnd_517957 := by
    simpa [prefixWord, tailWord_517957, baseEnd_517957] using wordTrace_append hprefix tailTrace_517957
  have hstable : (prefixWord ++ tailWord_517957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517957).length < 2 ^ (prefixWord ++ tailWord_517957).sum := by decide
  have hdescent : baseEnd_517957 < baseStart_517957 := by decide
  rcases family_descends (prefixWord ++ tailWord_517957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517977 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 4, 2, 3]
def baseStart_517977 : Nat := 118140960795 + 517977 * 2 ^ 59
def prefixEnd_517977 : Nat := 4983230072969 + 3 ^ 40 * 517977 * 2
def baseEnd_517977 : Nat := 265971168974025146305373

theorem tailTrace_517977 : CollatzResearch.WordTrace tailWord_517977 prefixEnd_517977 265971168974025146305373 := by
  unfold tailWord_517977
  simp only [CollatzResearch.WordTrace]
  refine ⟨18892173244465267273776185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12594782162976844849184123 18892173244465267273776185)
  ·
    refine ⟨14169129933348950455332139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18892173244465267273776185 14169129933348950455332139)
    ·
      refine ⟨21253694900023425682998209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14169129933348950455332139 21253694900023425682998209)
      ·
        refine ⟨15940271175017569262248657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21253694900023425682998209 15940271175017569262248657)
        ·
          refine ⟨11955203381263176946686493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15940271175017569262248657 11955203381263176946686493)
          ·
            refine ⟨4483201267973691355007435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11955203381263176946686493 4483201267973691355007435)
            ·
              refine ⟨6724801901960537032511153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4483201267973691355007435 6724801901960537032511153)
              ·
                refine ⟨5043601426470402774383365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6724801901960537032511153 5043601426470402774383365)
                ·
                  refine ⟨945675267463200520196881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5043601426470402774383365 945675267463200520196881)
                  ·
                    refine ⟨709256450597400390147661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 945675267463200520196881 709256450597400390147661)
                    ·
                      refine ⟨265971168974025146305373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 709256450597400390147661 265971168974025146305373)
                      ·
                        rfl

theorem cell23_517977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_517977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_517977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_517977 prefixEnd_517977 := by exact prefixLift 517977
  have htrace : WordTrace (prefixWord ++ tailWord_517977) baseStart_517977 baseEnd_517977 := by
    simpa [prefixWord, tailWord_517977, baseEnd_517977] using wordTrace_append hprefix tailTrace_517977
  have hstable : (prefixWord ++ tailWord_517977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517977).length < 2 ^ (prefixWord ++ tailWord_517977).sum := by decide
  have hdescent : baseEnd_517977 < baseStart_517977 := by decide
  rcases family_descends (prefixWord ++ tailWord_517977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518000 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 8]
def baseStart_518000 : Nat := 118140960795 + 518000 * 2 ^ 59
def prefixEnd_518000 : Nat := 4983230072969 + 3 ^ 40 * 518000 * 2
def baseEnd_518000 : Nat := 265982979029078556317767

theorem tailTrace_518000 : CollatzResearch.WordTrace tailWord_518000 prefixEnd_518000 265982979029078556317767 := by
  unfold tailWord_518000
  simp only [CollatzResearch.WordTrace]
  refine ⟨9446506061690971100931727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12595341415587961467908969 9446506061690971100931727)
  ·
    refine ⟨14169759092536456651397591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9446506061690971100931727 14169759092536456651397591)
    ·
      refine ⟨21254638638804684977096387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14169759092536456651397591 21254638638804684977096387)
      ·
        refine ⟨31881957958207027465644581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21254638638804684977096387 31881957958207027465644581)
        ·
          refine ⟨5977867117163817649808359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31881957958207027465644581 5977867117163817649808359)
          ·
            refine ⟨8966800675745726474712539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5977867117163817649808359 8966800675745726474712539)
            ·
              refine ⟨13450201013618589712068809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8966800675745726474712539 13450201013618589712068809)
              ·
                refine ⟨10087650760213942284051607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13450201013618589712068809 10087650760213942284051607)
                ·
                  refine ⟨15131476140320913426077411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10087650760213942284051607 15131476140320913426077411)
                  ·
                    refine ⟨22697214210481370139116117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15131476140320913426077411 22697214210481370139116117)
                    ·
                      refine ⟨265982979029078556317767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 22697214210481370139116117 265982979029078556317767)
                      ·
                        rfl

theorem cell23_518000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_518000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518000 prefixEnd_518000 := by exact prefixLift 518000
  have htrace : WordTrace (prefixWord ++ tailWord_518000) baseStart_518000 baseEnd_518000 := by
    simpa [prefixWord, tailWord_518000, baseEnd_518000] using wordTrace_append hprefix tailTrace_518000
  have hstable : (prefixWord ++ tailWord_518000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518000).length < 2 ^ (prefixWord ++ tailWord_518000).sum := by decide
  have hdescent : baseEnd_518000 < baseStart_518000 := by decide
  rcases family_descends (prefixWord ++ tailWord_518000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518044 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 3, 5]
def baseStart_518044 : Nat := 118140960795 + 518044 * 2 ^ 59
def prefixEnd_518044 : Nat := 4983230072969 + 3 ^ 40 * 518044 * 2
def baseEnd_518044 : Nat := 88668524059292128055855

theorem tailTrace_518044 : CollatzResearch.WordTrace tailWord_518044 prefixEnd_518044 88668524059292128055855 := by
  unfold tailWord_518044
  simp only [CollatzResearch.WordTrace]
  refine ⟨9447308467611268858232593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12596411290148358477643457 9447308467611268858232593)
  ·
    refine ⟨7085481350708451643674445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9447308467611268858232593 7085481350708451643674445)
    ·
      refine ⟨2657055506515669366377917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7085481350708451643674445 2657055506515669366377917)
      ·
        refine ⟨996395814943376012391719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2657055506515669366377917 996395814943376012391719)
        ·
          refine ⟨1494593722415064018587579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996395814943376012391719 1494593722415064018587579)
          ·
            refine ⟨2241890583622596027881369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494593722415064018587579 2241890583622596027881369)
            ·
              refine ⟨1681417937716947020911027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2241890583622596027881369 1681417937716947020911027)
              ·
                refine ⟨2522126906575420531366541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1681417937716947020911027 2522126906575420531366541)
                ·
                  refine ⟨945797589965782699262453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2522126906575420531366541 945797589965782699262453)
                  ·
                    refine ⟨88668524059292128055855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 945797589965782699262453 88668524059292128055855)
                    ·
                      rfl

theorem cell23_518044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_518044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518044 prefixEnd_518044 := by exact prefixLift 518044
  have htrace : WordTrace (prefixWord ++ tailWord_518044) baseStart_518044 baseEnd_518044 := by
    simpa [prefixWord, tailWord_518044, baseEnd_518044] using wordTrace_append hprefix tailTrace_518044
  have hstable : (prefixWord ++ tailWord_518044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518044).length < 2 ^ (prefixWord ++ tailWord_518044).sum := by decide
  have hdescent : baseEnd_518044 < baseStart_518044 := by decide
  rcases family_descends (prefixWord ++ tailWord_518044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518067 : List Nat := [1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 5]
def baseStart_518067 : Nat := 118140960795 + 518067 * 2 ^ 59
def prefixEnd_518067 : Nat := 4983230072969 + 3 ^ 40 * 518067 * 2
def baseEnd_518067 : Nat := 266017382232929794179959

theorem tailTrace_518067 : CollatzResearch.WordTrace tailWord_518067 prefixEnd_518067 266017382232929794179959 := by
  unfold tailWord_518067
  simp only [CollatzResearch.WordTrace]
  refine ⟨18895455814139212644552455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12596970542759475096368303 18895455814139212644552455)
  ·
    refine ⟨28343183721208818966828683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18895455814139212644552455 28343183721208818966828683)
    ·
      refine ⟨42514775581813228450243025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28343183721208818966828683 42514775581813228450243025)
      ·
        refine ⟨31886081686359921337682269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42514775581813228450243025 31886081686359921337682269)
        ·
          refine ⟨11957280632384970501630851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31886081686359921337682269 11957280632384970501630851)
          ·
            refine ⟨17935920948577455752446277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11957280632384970501630851 17935920948577455752446277)
            ·
              refine ⟨3362985177858272953583677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17935920948577455752446277 3362985177858272953583677)
              ·
                refine ⟨1261119441696852357593879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3362985177858272953583677 1261119441696852357593879)
                ·
                  refine ⟨1891679162545278536390819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1261119441696852357593879 1891679162545278536390819)
                  ·
                    refine ⟨2837518743817917804586229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1891679162545278536390819 2837518743817917804586229)
                    ·
                      refine ⟨266017382232929794179959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2837518743817917804586229 266017382232929794179959)
                      ·
                        rfl

theorem cell23_518067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 5].length) (baseStart_518067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518067 prefixEnd_518067 := by exact prefixLift 518067
  have htrace : WordTrace (prefixWord ++ tailWord_518067) baseStart_518067 baseEnd_518067 := by
    simpa [prefixWord, tailWord_518067, baseEnd_518067] using wordTrace_append hprefix tailTrace_518067
  have hstable : (prefixWord ++ tailWord_518067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518067).length < 2 ^ (prefixWord ++ tailWord_518067).sum := by decide
  have hdescent : baseEnd_518067 < baseStart_518067 := by decide
  rcases family_descends (prefixWord ++ tailWord_518067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518074 : List Nat := [3, 1, 1, 1, 2, 1, 2, 6, 2, 4]
def baseStart_518074 : Nat := 118140960795 + 518074 * 2 ^ 59
def prefixEnd_518074 : Nat := 4983230072969 + 3 ^ 40 * 518074 * 2
def baseEnd_518074 : Nat := 88673658865837088930809

theorem tailTrace_518074 : CollatzResearch.WordTrace tailWord_518074 prefixEnd_518074 88673658865837088930809 := by
  unfold tailWord_518074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4723927781278463210014319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12597140750075901893371517 4723927781278463210014319)
  ·
    refine ⟨7085891671917694815021479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4723927781278463210014319 7085891671917694815021479)
    ·
      refine ⟨10628837507876542222532219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7085891671917694815021479 10628837507876542222532219)
      ·
        refine ⟨15943256261814813333798329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10628837507876542222532219 15943256261814813333798329)
        ·
          refine ⟨11957442196361110000348747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15943256261814813333798329 11957442196361110000348747)
          ·
            refine ⟨17936163294541665000523121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11957442196361110000348747 17936163294541665000523121)
            ·
              refine ⟨13452122470906248750392341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17936163294541665000523121 13452122470906248750392341)
              ·
                refine ⟨630568240823730410174641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13452122470906248750392341 630568240823730410174641)
                ·
                  refine ⟨472926180617797807630981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630568240823730410174641 472926180617797807630981)
                  ·
                    refine ⟨88673658865837088930809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 472926180617797807630981 88673658865837088930809)
                    ·
                      rfl

theorem cell23_518074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_518074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518074 prefixEnd_518074 := by exact prefixLift 518074
  have htrace : WordTrace (prefixWord ++ tailWord_518074) baseStart_518074 baseEnd_518074 := by
    simpa [prefixWord, tailWord_518074, baseEnd_518074] using wordTrace_append hprefix tailTrace_518074
  have hstable : (prefixWord ++ tailWord_518074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518074).length < 2 ^ (prefixWord ++ tailWord_518074).sum := by decide
  have hdescent : baseEnd_518074 < baseStart_518074 := by decide
  rcases family_descends (prefixWord ++ tailWord_518074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518091 : List Nat := [1, 1, 1, 1, 3, 4, 5, 1, 2, 4]
def baseStart_518091 : Nat := 118140960795 + 518091 * 2 ^ 59
def prefixEnd_518091 : Nat := 4983230072969 + 3 ^ 40 * 518091 * 2
def baseEnd_518091 : Nat := 88676568589545900093283

theorem tailTrace_518091 : CollatzResearch.WordTrace tailWord_518091 prefixEnd_518091 88676568589545900093283 := by
  unfold tailWord_518091
  simp only [CollatzResearch.WordTrace]
  refine ⟨18896331166052264743426127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12597554110701509828950751 18896331166052264743426127)
  ·
    refine ⟨28344496749078397115139191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18896331166052264743426127 28344496749078397115139191)
    ·
      refine ⟨42516745123617595672708787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28344496749078397115139191 42516745123617595672708787)
      ·
        refine ⟨63775117685426393509063181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42516745123617595672708787 63775117685426393509063181)
        ·
          refine ⟨23915669132034897565898693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63775117685426393509063181 23915669132034897565898693)
          ·
            refine ⟨4484187962256543293606005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23915669132034897565898693 4484187962256543293606005)
            ·
              refine ⟨420392621461550933775563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4484187962256543293606005 420392621461550933775563)
              ·
                refine ⟨630588932192326400663345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420392621461550933775563 630588932192326400663345)
                ·
                  refine ⟨472941699144244800497509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630588932192326400663345 472941699144244800497509)
                  ·
                    refine ⟨88676568589545900093283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 472941699144244800497509 88676568589545900093283)
                    ·
                      rfl

theorem cell23_518091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 2, 4].length) (baseStart_518091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518091 prefixEnd_518091 := by exact prefixLift 518091
  have htrace : WordTrace (prefixWord ++ tailWord_518091) baseStart_518091 baseEnd_518091 := by
    simpa [prefixWord, tailWord_518091, baseEnd_518091] using wordTrace_append hprefix tailTrace_518091
  have hstable : (prefixWord ++ tailWord_518091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518091).length < 2 ^ (prefixWord ++ tailWord_518091).sum := by decide
  have hdescent : baseEnd_518091 < baseStart_518091 := by decide
  rcases family_descends (prefixWord ++ tailWord_518091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518098 : List Nat := [3, 2, 2, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_518098 : Nat := 118140960795 + 518098 * 2 ^ 59
def prefixEnd_518098 : Nat := 4983230072969 + 3 ^ 40 * 518098 * 2
def baseEnd_518098 : Nat := 266033300133219172892317

theorem tailTrace_518098 : CollatzResearch.WordTrace tailWord_518098 prefixEnd_518098 266033300133219172892317 := by
  unfold tailWord_518098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4724146619256726234732737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12597724318017936625953965 4724146619256726234732737)
  ·
    refine ⟨3543109964442544676049553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4724146619256726234732737 3543109964442544676049553)
    ·
      refine ⟨2657332473331908507037165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3543109964442544676049553 2657332473331908507037165)
      ·
        refine ⟨996499677499465690138937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2657332473331908507037165 996499677499465690138937)
        ·
          refine ⟨747374758124599267604203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 996499677499465690138937 747374758124599267604203)
          ·
            refine ⟨1121062137186898901406305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747374758124599267604203 1121062137186898901406305)
            ·
              refine ⟨840796602890174176054729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1121062137186898901406305 840796602890174176054729)
              ·
                refine ⟨630597452167630632041047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840796602890174176054729 630597452167630632041047)
                ·
                  refine ⟨945896178251445948061571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 630597452167630632041047 945896178251445948061571)
                  ·
                    refine ⟨1418844267377168922092357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 945896178251445948061571 1418844267377168922092357)
                    ·
                      refine ⟨266033300133219172892317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1418844267377168922092357 266033300133219172892317)
                      ·
                        rfl

theorem cell23_518098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_518098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518098 prefixEnd_518098 := by exact prefixLift 518098
  have htrace : WordTrace (prefixWord ++ tailWord_518098) baseStart_518098 baseEnd_518098 := by
    simpa [prefixWord, tailWord_518098, baseEnd_518098] using wordTrace_append hprefix tailTrace_518098
  have hstable : (prefixWord ++ tailWord_518098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518098).length < 2 ^ (prefixWord ++ tailWord_518098).sum := by decide
  have hdescent : baseEnd_518098 < baseStart_518098 := by decide
  rcases family_descends (prefixWord ++ tailWord_518098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518101 : List Nat := [1, 3, 2, 3, 2, 1, 1, 4, 1, 2, 3]
def baseStart_518101 : Nat := 118140960795 + 518101 * 2 ^ 59
def prefixEnd_518101 : Nat := 4983230072969 + 3 ^ 40 * 518101 * 2
def baseEnd_518101 : Nat := 266034840575182661154803

theorem tailTrace_518101 : CollatzResearch.WordTrace tailWord_518101 prefixEnd_518101 266034840575182661154803 := by
  unfold tailWord_518101
  simp only [CollatzResearch.WordTrace]
  refine ⟨18896695896016036451290157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12597797264010690967526771 18896695896016036451290157)
  ·
    refine ⟨7086260961006013669233809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18896695896016036451290157 7086260961006013669233809)
    ·
      refine ⟨5314695720754510251925357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7086260961006013669233809 5314695720754510251925357)
      ·
        refine ⟨1993010895282941344472009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5314695720754510251925357 1993010895282941344472009)
        ·
          refine ⟨1494758171462206008354007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1993010895282941344472009 1494758171462206008354007)
          ·
            refine ⟨2242137257193309012531011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494758171462206008354007 2242137257193309012531011)
            ·
              refine ⟨3363205885789963518796517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2242137257193309012531011 3363205885789963518796517)
              ·
                refine ⟨630601103585618159774347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3363205885789963518796517 630601103585618159774347)
                ·
                  refine ⟨945901655378427239661521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 630601103585618159774347 945901655378427239661521)
                  ·
                    refine ⟨709426241533820429746141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 945901655378427239661521 709426241533820429746141)
                    ·
                      refine ⟨266034840575182661154803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 709426241533820429746141 266034840575182661154803)
                      ·
                        rfl

theorem cell23_518101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_518101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518101 prefixEnd_518101 := by exact prefixLift 518101
  have htrace : WordTrace (prefixWord ++ tailWord_518101) baseStart_518101 baseEnd_518101 := by
    simpa [prefixWord, tailWord_518101, baseEnd_518101] using wordTrace_append hprefix tailTrace_518101
  have hstable : (prefixWord ++ tailWord_518101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518101).length < 2 ^ (prefixWord ++ tailWord_518101).sum := by decide
  have hdescent : baseEnd_518101 < baseStart_518101 := by decide
  rcases family_descends (prefixWord ++ tailWord_518101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518115 : List Nat := [1, 1, 1, 6, 1, 2, 3, 3, 1, 2, 2]
def baseStart_518115 : Nat := 118140960795 + 518115 * 2 ^ 59
def prefixEnd_518115 : Nat := 4983230072969 + 3 ^ 40 * 518115 * 2
def baseEnd_518115 : Nat := 266042029304345606379739

theorem tailTrace_518115 : CollatzResearch.WordTrace tailWord_518115 prefixEnd_518115 266042029304345606379739 := by
  unfold tailWord_518115
  simp only [CollatzResearch.WordTrace]
  refine ⟨18897206517965316842299799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12598137678643544561533199 18897206517965316842299799)
  ·
    refine ⟨28345809776947975263449699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18897206517965316842299799 28345809776947975263449699)
    ·
      refine ⟨42518714665421962895174549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28345809776947975263449699 42518714665421962895174549)
      ·
        refine ⟨1993064749941654510711307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42518714665421962895174549 1993064749941654510711307)
        ·
          refine ⟨2989597124912481766066961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1993064749941654510711307 2989597124912481766066961)
          ·
            refine ⟨2242197843684361324550221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2989597124912481766066961 2242197843684361324550221)
            ·
              refine ⟨840824191381635496706333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2242197843684361324550221 840824191381635496706333)
              ·
                refine ⟨315309071768113311264875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 840824191381635496706333 315309071768113311264875)
                ·
                  refine ⟨472963607652169966897313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315309071768113311264875 472963607652169966897313)
                  ·
                    refine ⟨354722705739127475172985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 472963607652169966897313 354722705739127475172985)
                    ·
                      refine ⟨266042029304345606379739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 354722705739127475172985 266042029304345606379739)
                      ·
                        rfl

theorem cell23_518115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_518115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518115 prefixEnd_518115 := by exact prefixLift 518115
  have htrace : WordTrace (prefixWord ++ tailWord_518115) baseStart_518115 baseEnd_518115 := by
    simpa [prefixWord, tailWord_518115, baseEnd_518115] using wordTrace_append hprefix tailTrace_518115
  have hstable : (prefixWord ++ tailWord_518115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518115).length < 2 ^ (prefixWord ++ tailWord_518115).sum := by decide
  have hdescent : baseEnd_518115 < baseStart_518115 := by decide
  rcases family_descends (prefixWord ++ tailWord_518115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518127 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 5]
def baseStart_518127 : Nat := 118140960795 + 518127 * 2 ^ 59
def prefixEnd_518127 : Nat := 4983230072969 + 3 ^ 40 * 518127 * 2
def baseEnd_518127 : Nat := 266048191072199559429683

theorem tailTrace_518127 : CollatzResearch.WordTrace tailWord_518127 prefixEnd_518127 266048191072199559429683 := by
  unfold tailWord_518127
  simp only [CollatzResearch.WordTrace]
  refine ⟨18897644193921842891736635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12598429462614561927824423 18897644193921842891736635)
  ·
    refine ⟨28346466290882764337604953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18897644193921842891736635 28346466290882764337604953)
    ·
      refine ⟨21259849718162073253203715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28346466290882764337604953 21259849718162073253203715)
      ·
        refine ⟨31889774577243109879805573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21259849718162073253203715 31889774577243109879805573)
        ·
          refine ⟨5979332733233083102463545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31889774577243109879805573 5979332733233083102463545)
          ·
            refine ⟨4484499549924812326847659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5979332733233083102463545 4484499549924812326847659)
            ·
              refine ⟨6726749324887218490271489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4484499549924812326847659 6726749324887218490271489)
              ·
                refine ⟨5045061993665413867703617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6726749324887218490271489 5045061993665413867703617)
                ·
                  refine ⟨3783796495249060400777713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5045061993665413867703617 3783796495249060400777713)
                  ·
                    refine ⟨2837847371436795300583285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3783796495249060400777713 2837847371436795300583285)
                    ·
                      refine ⟨266048191072199559429683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2837847371436795300583285 266048191072199559429683)
                      ·
                        rfl

theorem cell23_518127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_518127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518127 prefixEnd_518127 := by exact prefixLift 518127
  have htrace : WordTrace (prefixWord ++ tailWord_518127) baseStart_518127 baseEnd_518127 := by
    simpa [prefixWord, tailWord_518127, baseEnd_518127] using wordTrace_append hprefix tailTrace_518127
  have hstable : (prefixWord ++ tailWord_518127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518127).length < 2 ^ (prefixWord ++ tailWord_518127).sum := by decide
  have hdescent : baseEnd_518127 < baseStart_518127 := by decide
  rcases family_descends (prefixWord ++ tailWord_518127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518147 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 2, 6]
def baseStart_518147 : Nat := 118140960795 + 518147 * 2 ^ 59
def prefixEnd_518147 : Nat := 4983230072969 + 3 ^ 40 * 518147 * 2
def baseEnd_518147 : Nat := 88686153561763160393197

theorem tailTrace_518147 : CollatzResearch.WordTrace tailWord_518147 prefixEnd_518147 88686153561763160393197 := by
  unfold tailWord_518147
  simp only [CollatzResearch.WordTrace]
  refine ⟨18898373653849386307464695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12598915769232924204976463 18898373653849386307464695)
  ·
    refine ⟨28347560480774079461197043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18898373653849386307464695 28347560480774079461197043)
    ·
      refine ⟨42521340721161119191795565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28347560480774079461197043 42521340721161119191795565)
      ·
        refine ⟨15945502770435419696923337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42521340721161119191795565 15945502770435419696923337)
        ·
          refine ⟨11959127077826564772692503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15945502770435419696923337 11959127077826564772692503)
          ·
            refine ⟨17938690616739847159038755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11959127077826564772692503 17938690616739847159038755)
            ·
              refine ⟨26908035925109770738558133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17938690616739847159038755 26908035925109770738558133)
              ·
                refine ⟨2522628367979041006739825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26908035925109770738558133 2522628367979041006739825)
                ·
                  refine ⟨1891971275984280755054869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2522628367979041006739825 1891971275984280755054869)
                  ·
                    refine ⟨88686153561763160393197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1891971275984280755054869 88686153561763160393197)
                    ·
                      rfl

theorem cell23_518147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 6].length) (baseStart_518147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518147 prefixEnd_518147 := by exact prefixLift 518147
  have htrace : WordTrace (prefixWord ++ tailWord_518147) baseStart_518147 baseEnd_518147 := by
    simpa [prefixWord, tailWord_518147, baseEnd_518147] using wordTrace_append hprefix tailTrace_518147
  have hstable : (prefixWord ++ tailWord_518147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518147).length < 2 ^ (prefixWord ++ tailWord_518147).sum := by decide
  have hdescent : baseEnd_518147 < baseStart_518147 := by decide
  rcases family_descends (prefixWord ++ tailWord_518147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518171 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 4, 2, 2]
def baseStart_518171 : Nat := 118140960795 + 518171 * 2 ^ 59
def prefixEnd_518171 : Nat := 4983230072969 + 3 ^ 40 * 518171 * 2
def baseEnd_518171 : Nat := 266070784220997387279481

theorem tailTrace_518171 : CollatzResearch.WordTrace tailWord_518171 prefixEnd_518171 266070784220997387279481 := by
  unfold tailWord_518171
  simp only [CollatzResearch.WordTrace]
  refine ⟨18899249005762438406338367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12599499337174958937558911 18899249005762438406338367)
  ·
    refine ⟨28348873508643657609507551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18899249005762438406338367 28348873508643657609507551)
    ·
      refine ⟨42523310262965486414261327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28348873508643657609507551 42523310262965486414261327)
      ·
        refine ⟨63784965394448229621391991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42523310262965486414261327 63784965394448229621391991)
        ·
          refine ⟨95677448091672344432087987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63784965394448229621391991 95677448091672344432087987)
          ·
            refine ⟨143516172137508516648131981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95677448091672344432087987 143516172137508516648131981)
            ·
              refine ⟨53818564551565693743049493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143516172137508516648131981 53818564551565693743049493)
              ·
                refine ⟨2522745213354641894205445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53818564551565693743049493 2522745213354641894205445)
                ·
                  refine ⟨473014727503995355163521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2522745213354641894205445 473014727503995355163521)
                  ·
                    refine ⟨354761045627996516372641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 473014727503995355163521 354761045627996516372641)
                    ·
                      refine ⟨266070784220997387279481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 354761045627996516372641 266070784220997387279481)
                      ·
                        rfl

theorem cell23_518171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 2, 2].length) (baseStart_518171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518171 prefixEnd_518171 := by exact prefixLift 518171
  have htrace : WordTrace (prefixWord ++ tailWord_518171) baseStart_518171 baseEnd_518171 := by
    simpa [prefixWord, tailWord_518171, baseEnd_518171] using wordTrace_append hprefix tailTrace_518171
  have hstable : (prefixWord ++ tailWord_518171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518171).length < 2 ^ (prefixWord ++ tailWord_518171).sum := by decide
  have hdescent : baseEnd_518171 < baseStart_518171 := by decide
  rcases family_descends (prefixWord ++ tailWord_518171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518201 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 2, 2, 4]
def baseStart_518201 : Nat := 118140960795 + 518201 * 2 ^ 59
def prefixEnd_518201 : Nat := 4983230072969 + 3 ^ 40 * 518201 * 2
def baseEnd_518201 : Nat := 266086188640632269904343

theorem tailTrace_518201 : CollatzResearch.WordTrace tailWord_518201 prefixEnd_518201 266086188640632269904343 := by
  unfold tailWord_518201
  simp only [CollatzResearch.WordTrace]
  refine ⟨18900343195653753529930457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12600228797102502353286971 18900343195653753529930457)
  ·
    refine ⟨14175257396740315147447843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18900343195653753529930457 14175257396740315147447843)
    ·
      refine ⟨21262886095110472721171765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14175257396740315147447843 21262886095110472721171765)
      ·
        refine ⟨1993395571416606817609853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21262886095110472721171765 1993395571416606817609853)
        ·
          refine ⟨747523339281227556603695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1993395571416606817609853 747523339281227556603695)
          ·
            refine ⟨1121285008921841334905543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747523339281227556603695 1121285008921841334905543)
            ·
              refine ⟨1681927513382762002358315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121285008921841334905543 1681927513382762002358315)
              ·
                refine ⟨2522891270074143003537473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1681927513382762002358315 2522891270074143003537473)
                ·
                  refine ⟨1892168452555607252653105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2522891270074143003537473 1892168452555607252653105)
                  ·
                    refine ⟨1419126339416705439489829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1892168452555607252653105 1419126339416705439489829)
                    ·
                      refine ⟨266086188640632269904343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1419126339416705439489829 266086188640632269904343)
                      ·
                        rfl

theorem cell23_518201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_518201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518201 prefixEnd_518201 := by exact prefixLift 518201
  have htrace : WordTrace (prefixWord ++ tailWord_518201) baseStart_518201 baseEnd_518201 := by
    simpa [prefixWord, tailWord_518201, baseEnd_518201] using wordTrace_append hprefix tailTrace_518201
  have hstable : (prefixWord ++ tailWord_518201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518201).length < 2 ^ (prefixWord ++ tailWord_518201).sum := by decide
  have hdescent : baseEnd_518201 < baseStart_518201 := by decide
  rcases family_descends (prefixWord ++ tailWord_518201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518221 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_518221 : Nat := 118140960795 + 518221 * 2 ^ 59
def prefixEnd_518221 : Nat := 4983230072969 + 3 ^ 40 * 518221 * 2
def baseEnd_518221 : Nat := 266096458253722191654251

theorem tailTrace_518221 : CollatzResearch.WordTrace tailWord_518221 prefixEnd_518221 266096458253722191654251 := by
  unfold tailWord_518221
  simp only [CollatzResearch.WordTrace]
  refine ⟨18901072655581296945658517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12600715103720864630439011 18901072655581296945658517)
  ·
    refine ⟨885987780730373294327743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18901072655581296945658517 885987780730373294327743)
    ·
      refine ⟨1328981671095559941491615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 885987780730373294327743 1328981671095559941491615)
      ·
        refine ⟨1993472506643339912237423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1328981671095559941491615 1993472506643339912237423)
        ·
          refine ⟨2990208759965009868356135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1993472506643339912237423 2990208759965009868356135)
          ·
            refine ⟨4485313139947514802534203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2990208759965009868356135 4485313139947514802534203)
            ·
              refine ⟨6727969709921272203801305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4485313139947514802534203 6727969709921272203801305)
              ·
                refine ⟨5045977282440954152850979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6727969709921272203801305 5045977282440954152850979)
                ·
                  refine ⟨7568965923661431229276469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5045977282440954152850979 7568965923661431229276469)
                  ·
                    refine ⟨709590555343259177744669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7568965923661431229276469 709590555343259177744669)
                    ·
                      refine ⟨266096458253722191654251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 709590555343259177744669 266096458253722191654251)
                      ·
                        rfl

theorem cell23_518221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_518221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518221 prefixEnd_518221 := by exact prefixLift 518221
  have htrace : WordTrace (prefixWord ++ tailWord_518221) baseStart_518221 baseEnd_518221 := by
    simpa [prefixWord, tailWord_518221, baseEnd_518221] using wordTrace_append hprefix tailTrace_518221
  have hstable : (prefixWord ++ tailWord_518221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518221).length < 2 ^ (prefixWord ++ tailWord_518221).sum := by decide
  have hdescent : baseEnd_518221 < baseStart_518221 := by decide
  rcases family_descends (prefixWord ++ tailWord_518221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518227 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 8]
def baseStart_518227 : Nat := 118140960795 + 518227 * 2 ^ 59
def prefixEnd_518227 : Nat := 4983230072969 + 3 ^ 40 * 518227 * 2
def baseEnd_518227 : Nat := 266099539137649168179223

theorem tailTrace_518227 : CollatzResearch.WordTrace tailWord_518227 prefixEnd_518227 266099539137649168179223 := by
  unfold tailWord_518227
  simp only [CollatzResearch.WordTrace]
  refine ⟨18901291493559559970376935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12600860995706373313584623 18901291493559559970376935)
  ·
    refine ⟨28351937240339339955565403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18901291493559559970376935 28351937240339339955565403)
    ·
      refine ⟨42527905860509009933348105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28351937240339339955565403 42527905860509009933348105)
      ·
        refine ⟨31895929395381757450011079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42527905860509009933348105 31895929395381757450011079)
        ·
          refine ⟨47843894093072636175016619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31895929395381757450011079 47843894093072636175016619)
          ·
            refine ⟨71765841139608954262524929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47843894093072636175016619 71765841139608954262524929)
            ·
              refine ⟨53824380854706715696893697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71765841139608954262524929 53824380854706715696893697)
              ·
                refine ⟨40368285641030036772670273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53824380854706715696893697 40368285641030036772670273)
                ·
                  refine ⟨30276214230772527579502705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40368285641030036772670273 30276214230772527579502705)
                  ·
                    refine ⟨22707160673079395684627029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30276214230772527579502705 22707160673079395684627029)
                    ·
                      refine ⟨266099539137649168179223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 22707160673079395684627029 266099539137649168179223)
                      ·
                        rfl

theorem cell23_518227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_518227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518227 prefixEnd_518227 := by exact prefixLift 518227
  have htrace : WordTrace (prefixWord ++ tailWord_518227) baseStart_518227 baseEnd_518227 := by
    simpa [prefixWord, tailWord_518227, baseEnd_518227] using wordTrace_append hprefix tailTrace_518227
  have hstable : (prefixWord ++ tailWord_518227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518227).length < 2 ^ (prefixWord ++ tailWord_518227).sum := by decide
  have hdescent : baseEnd_518227 < baseStart_518227 := by decide
  rcases family_descends (prefixWord ++ tailWord_518227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518281 : List Nat := [1, 2, 1, 1, 4, 2, 2, 3, 2, 2, 3]
def baseStart_518281 : Nat := 118140960795 + 518281 * 2 ^ 59
def prefixEnd_518281 : Nat := 4983230072969 + 3 ^ 40 * 518281 * 2
def baseEnd_518281 : Nat := 266127267092991956903975

theorem tailTrace_518281 : CollatzResearch.WordTrace tailWord_518281 prefixEnd_518281 266127267092991956903975 := by
  unfold tailWord_518281
  simp only [CollatzResearch.WordTrace]
  refine ⟨18903261035363927192842697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12602174023575951461895131 18903261035363927192842697)
  ·
    refine ⟨14177445776522945394632023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18903261035363927192842697 14177445776522945394632023)
    ·
      refine ⟨21266168664784418091948035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14177445776522945394632023 21266168664784418091948035)
      ·
        refine ⟨31899252997176627137922053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21266168664784418091948035 31899252997176627137922053)
        ·
          refine ⟨5981109936970617588360385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31899252997176627137922053 5981109936970617588360385)
          ·
            refine ⟨4485832452727963191270289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5981109936970617588360385 4485832452727963191270289)
            ·
              refine ⟨3364374339545972393452717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4485832452727963191270289 3364374339545972393452717)
              ·
                refine ⟨1261640377329739647544769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3364374339545972393452717 1261640377329739647544769)
                ·
                  refine ⟨946230282997304735658577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1261640377329739647544769 946230282997304735658577)
                  ·
                    refine ⟨709672712247978551743933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 946230282997304735658577 709672712247978551743933)
                    ·
                      refine ⟨266127267092991956903975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 709672712247978551743933 266127267092991956903975)
                      ·
                        rfl

theorem cell23_518281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 2, 3].length) (baseStart_518281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518281 prefixEnd_518281 := by exact prefixLift 518281
  have htrace : WordTrace (prefixWord ++ tailWord_518281) baseStart_518281 baseEnd_518281 := by
    simpa [prefixWord, tailWord_518281, baseEnd_518281] using wordTrace_append hprefix tailTrace_518281
  have hstable : (prefixWord ++ tailWord_518281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518281).length < 2 ^ (prefixWord ++ tailWord_518281).sum := by decide
  have hdescent : baseEnd_518281 < baseStart_518281 := by decide
  rcases family_descends (prefixWord ++ tailWord_518281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518361 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 4, 4]
def baseStart_518361 : Nat := 118140960795 + 518361 * 2 ^ 59
def prefixEnd_518361 : Nat := 4983230072969 + 3 ^ 40 * 518361 * 2
def baseEnd_518361 : Nat := 88722781848450547967869

theorem tailTrace_518361 : CollatzResearch.WordTrace tailWord_518361 prefixEnd_518361 88722781848450547967869 := by
  unfold tailWord_518361
  simp only [CollatzResearch.WordTrace]
  refine ⟨18906178875074100855754937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12604119250049400570503291 18906178875074100855754937)
  ·
    refine ⟨14179634156305575641816203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18906178875074100855754937 14179634156305575641816203)
    ·
      refine ⟨21269451234458363462724305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14179634156305575641816203 21269451234458363462724305)
      ·
        refine ⟨15952088425843772597043229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21269451234458363462724305 15952088425843772597043229)
        ·
          refine ⟨5982033159691414723891211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15952088425843772597043229 5982033159691414723891211)
          ·
            refine ⟨8973049739537122085836817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5982033159691414723891211 8973049739537122085836817)
            ·
              refine ⟨6729787304652841564377613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8973049739537122085836817 6729787304652841564377613)
              ·
                refine ⟨2523670239244815586641605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6729787304652841564377613 2523670239244815586641605)
                ·
                  refine ⟨473188169858402922495301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2523670239244815586641605 473188169858402922495301)
                  ·
                    refine ⟨88722781848450547967869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 473188169858402922495301 88722781848450547967869)
                    ·
                      rfl

theorem cell23_518361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 4].length) (baseStart_518361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518361 prefixEnd_518361 := by exact prefixLift 518361
  have htrace : WordTrace (prefixWord ++ tailWord_518361) baseStart_518361 baseEnd_518361 := by
    simpa [prefixWord, tailWord_518361, baseEnd_518361] using wordTrace_append hprefix tailTrace_518361
  have hstable : (prefixWord ++ tailWord_518361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518361).length < 2 ^ (prefixWord ++ tailWord_518361).sum := by decide
  have hdescent : baseEnd_518361 < baseStart_518361 := by decide
  rcases family_descends (prefixWord ++ tailWord_518361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518362 : List Nat := [3, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3]
def baseStart_518362 : Nat := 118140960795 + 518362 * 2 ^ 59
def prefixEnd_518362 : Nat := 4983230072969 + 3 ^ 40 * 518362 * 2
def baseEnd_518362 : Nat := 266168859026006139991103

theorem tailTrace_518362 : CollatzResearch.WordTrace tailWord_518362 prefixEnd_518362 266168859026006139991103 := by
  unfold tailWord_518362
  simp only [CollatzResearch.WordTrace]
  refine ⟨4726553837017619506635335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12604143565380318684360893 4726553837017619506635335)
  ·
    refine ⟨7089830755526429259953003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4726553837017619506635335 7089830755526429259953003)
    ·
      refine ⟨10634746133289643889929505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7089830755526429259953003 10634746133289643889929505)
      ·
        refine ⟨7976059599967232917447129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10634746133289643889929505 7976059599967232917447129)
        ·
          refine ⟨5982044699975424688085347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7976059599967232917447129 5982044699975424688085347)
          ·
            refine ⟨8973067049963137032128021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5982044699975424688085347 8973067049963137032128021)
            ·
              refine ⟨420612517967022048381001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8973067049963137032128021 420612517967022048381001)
              ·
                refine ⟨315459388475266536285751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420612517967022048381001 315459388475266536285751)
                ·
                  refine ⟨473189082712899804428627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315459388475266536285751 473189082712899804428627)
                  ·
                    refine ⟨709783624069349706642941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 473189082712899804428627 709783624069349706642941)
                    ·
                      refine ⟨266168859026006139991103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 709783624069349706642941 266168859026006139991103)
                      ·
                        rfl

theorem cell23_518362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3].length) (baseStart_518362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518362 prefixEnd_518362 := by exact prefixLift 518362
  have htrace : WordTrace (prefixWord ++ tailWord_518362) baseStart_518362 baseEnd_518362 := by
    simpa [prefixWord, tailWord_518362, baseEnd_518362] using wordTrace_append hprefix tailTrace_518362
  have hstable : (prefixWord ++ tailWord_518362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518362).length < 2 ^ (prefixWord ++ tailWord_518362).sum := by decide
  have hdescent : baseEnd_518362 < baseStart_518362 := by decide
  rcases family_descends (prefixWord ++ tailWord_518362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518378 : List Nat := [3, 1, 3, 1, 1, 2, 1, 5, 2, 4]
def baseStart_518378 : Nat := 118140960795 + 518378 * 2 ^ 59
def prefixEnd_518378 : Nat := 4983230072969 + 3 ^ 40 * 518378 * 2
def baseEnd_518378 : Nat := 88725691572159359130343

theorem tailTrace_518378 : CollatzResearch.WordTrace tailWord_518378 prefixEnd_518378 88725691572159359130343 := by
  unfold tailWord_518378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4726699729003128189780947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12604532610675008506082525 4726699729003128189780947)
  ·
    refine ⟨7090049593504692284671421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4726699729003128189780947 7090049593504692284671421)
    ·
      refine ⟨2658768597564259606751783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7090049593504692284671421 2658768597564259606751783)
      ·
        refine ⟨3988152896346389410127675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2658768597564259606751783 3988152896346389410127675)
        ·
          refine ⟨5982229344519584115191513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3988152896346389410127675 5982229344519584115191513)
          ·
            refine ⟨4486672008389688086393635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5982229344519584115191513 4486672008389688086393635)
            ·
              refine ⟨6730008012584532129590453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4486672008389688086393635 6730008012584532129590453)
              ·
                refine ⟨630938251179799887149105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6730008012584532129590453 630938251179799887149105)
                ·
                  refine ⟨473203688384849915361829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630938251179799887149105 473203688384849915361829)
                  ·
                    refine ⟨88725691572159359130343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 473203688384849915361829 88725691572159359130343)
                    ·
                      rfl

theorem cell23_518378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_518378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518378 prefixEnd_518378 := by exact prefixLift 518378
  have htrace : WordTrace (prefixWord ++ tailWord_518378) baseStart_518378 baseEnd_518378 := by
    simpa [prefixWord, tailWord_518378, baseEnd_518378] using wordTrace_append hprefix tailTrace_518378
  have hstable : (prefixWord ++ tailWord_518378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518378).length < 2 ^ (prefixWord ++ tailWord_518378).sum := by decide
  have hdescent : baseEnd_518378 < baseStart_518378 := by decide
  rcases family_descends (prefixWord ++ tailWord_518378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518384 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 7]
def baseStart_518384 : Nat := 118140960795 + 518384 * 2 ^ 59
def prefixEnd_518384 : Nat := 4983230072969 + 3 ^ 40 * 518384 * 2
def baseEnd_518384 : Nat := 266180155600405053916001

theorem tailTrace_518384 : CollatzResearch.WordTrace tailWord_518384 prefixEnd_518384 266180155600405053916001 := by
  unfold tailWord_518384
  simp only [CollatzResearch.WordTrace]
  refine ⟨9453508876995387891921103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12604678502660517189228137 9453508876995387891921103)
  ·
    refine ⟨14180263315493081837881655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9453508876995387891921103 14180263315493081837881655)
    ·
      refine ⟨21270394973239622756822483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14180263315493081837881655 21270394973239622756822483)
      ·
        refine ⟨31905592459859434135233725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21270394973239622756822483 31905592459859434135233725)
        ·
          refine ⟨11964597172447287800712647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31905592459859434135233725 11964597172447287800712647)
          ·
            refine ⟨17946895758670931701068971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11964597172447287800712647 17946895758670931701068971)
            ·
              refine ⟨26920343638006397551603457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17946895758670931701068971 26920343638006397551603457)
              ·
                refine ⟨20190257728504798163702593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26920343638006397551603457 20190257728504798163702593)
                ·
                  refine ⟨15142693296378598622776945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20190257728504798163702593 15142693296378598622776945)
                  ·
                    refine ⟨11357019972283948967082709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15142693296378598622776945 11357019972283948967082709)
                    ·
                      refine ⟨266180155600405053916001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11357019972283948967082709 266180155600405053916001)
                      ·
                        rfl

theorem cell23_518384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_518384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518384 prefixEnd_518384 := by exact prefixLift 518384
  have htrace : WordTrace (prefixWord ++ tailWord_518384) baseStart_518384 baseEnd_518384 := by
    simpa [prefixWord, tailWord_518384, baseEnd_518384] using wordTrace_append hprefix tailTrace_518384
  have hstable : (prefixWord ++ tailWord_518384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518384).length < 2 ^ (prefixWord ++ tailWord_518384).sum := by decide
  have hdescent : baseEnd_518384 < baseStart_518384 := by decide
  rcases family_descends (prefixWord ++ tailWord_518384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518398 : List Nat := [4, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_518398 : Nat := 118140960795 + 518398 * 2 ^ 59
def prefixEnd_518398 : Nat := 4983230072969 + 3 ^ 40 * 518398 * 2
def baseEnd_518398 : Nat := 266187344329567999140937

theorem tailTrace_518398 : CollatzResearch.WordTrace tailWord_518398 prefixEnd_518398 266187344329567999140937 := by
  unfold tailWord_518398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2363441046992507021856481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12605018917293370783234565 2363441046992507021856481)
  ·
    refine ⟨1772580785244380266392361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2363441046992507021856481 1772580785244380266392361)
    ·
      refine ⟨1329435588933285199794271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1772580785244380266392361 1329435588933285199794271)
      ·
        refine ⟨1994153383399927799691407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1329435588933285199794271 1994153383399927799691407)
        ·
          refine ⟨2991230075099891699537111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1994153383399927799691407 2991230075099891699537111)
          ·
            refine ⟨4486845112649837549305667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2991230075099891699537111 4486845112649837549305667)
            ·
              refine ⟨6730267668974756323958501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4486845112649837549305667 6730267668974756323958501)
              ·
                refine ⟨1261925187932766810742219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6730267668974756323958501 1261925187932766810742219)
                ·
                  refine ⟨1892887781899150216113329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1261925187932766810742219 1892887781899150216113329)
                  ·
                    refine ⟨1419665836424362662084997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1892887781899150216113329 1419665836424362662084997)
                    ·
                      refine ⟨266187344329567999140937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1419665836424362662084997 266187344329567999140937)
                      ·
                        rfl

theorem cell23_518398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_518398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518398 prefixEnd_518398 := by exact prefixLift 518398
  have htrace : WordTrace (prefixWord ++ tailWord_518398) baseStart_518398 baseEnd_518398 := by
    simpa [prefixWord, tailWord_518398, baseEnd_518398] using wordTrace_append hprefix tailTrace_518398
  have hstable : (prefixWord ++ tailWord_518398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518398).length < 2 ^ (prefixWord ++ tailWord_518398).sum := by decide
  have hdescent : baseEnd_518398 < baseStart_518398 := by decide
  rcases family_descends (prefixWord ++ tailWord_518398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518402 : List Nat := [3, 4, 1, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_518402 : Nat := 118140960795 + 518402 * 2 ^ 59
def prefixEnd_518402 : Nat := 4983230072969 + 3 ^ 40 * 518402 * 2
def baseEnd_518402 : Nat := 266189398252185983490919

theorem tailTrace_518402 : CollatzResearch.WordTrace tailWord_518402 prefixEnd_518402 266189398252185983490919 := by
  unfold tailWord_518402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4726918566981391214499365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12605116178617043238664973 4726918566981391214499365)
  ·
    refine ⟨886297231309010852718631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4726918566981391214499365 886297231309010852718631)
    ·
      refine ⟨1329445846963516279077947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 886297231309010852718631 1329445846963516279077947)
      ·
        refine ⟨1994168770445274418616921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1329445846963516279077947 1994168770445274418616921)
        ·
          refine ⟨1495626577833955813962691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1994168770445274418616921 1495626577833955813962691)
          ·
            refine ⟨2243439866750933720944037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1495626577833955813962691 2243439866750933720944037)
            ·
              refine ⟨420644975015800072677007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2243439866750933720944037 420644975015800072677007)
              ·
                refine ⟨630967462523700109015511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420644975015800072677007 630967462523700109015511)
                ·
                  refine ⟨946451193785550163523267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 630967462523700109015511 946451193785550163523267)
                  ·
                    refine ⟨1419676790678325245284901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 946451193785550163523267 1419676790678325245284901)
                    ·
                      refine ⟨266189398252185983490919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1419676790678325245284901 266189398252185983490919)
                      ·
                        rfl

theorem cell23_518402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_518402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518402 prefixEnd_518402 := by exact prefixLift 518402
  have htrace : WordTrace (prefixWord ++ tailWord_518402) baseStart_518402 baseEnd_518402 := by
    simpa [prefixWord, tailWord_518402, baseEnd_518402] using wordTrace_append hprefix tailTrace_518402
  have hstable : (prefixWord ++ tailWord_518402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518402).length < 2 ^ (prefixWord ++ tailWord_518402).sum := by decide
  have hdescent : baseEnd_518402 < baseStart_518402 := by decide
  rcases family_descends (prefixWord ++ tailWord_518402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518442 : List Nat := [3, 1, 4, 2, 3, 1, 2, 7]
def baseStart_518442 : Nat := 118140960795 + 518442 * 2 ^ 59
def prefixEnd_518442 : Nat := 4983230072969 + 3 ^ 40 * 518442 * 2
def baseEnd_518442 : Nat := 9859627314013549147805

theorem tailTrace_518442 : CollatzResearch.WordTrace tailWord_518442 prefixEnd_518442 9859627314013549147805 := by
  unfold tailWord_518442
  simp only [CollatzResearch.WordTrace]
  refine ⟨4727283296945162922363395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12606088791853767792969053 4727283296945162922363395)
  ·
    refine ⟨7090924945417744383545093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4727283296945162922363395 7090924945417744383545093)
    ·
      refine ⟨1329548427265827071914705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7090924945417744383545093 1329548427265827071914705)
      ·
        refine ⟨997161320449370303936029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1329548427265827071914705 997161320449370303936029)
        ·
          refine ⟨373935495168513863976011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 997161320449370303936029 373935495168513863976011)
          ·
            refine ⟨560903242752770795964017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373935495168513863976011 560903242752770795964017)
            ·
              refine ⟨420677432064578096973013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560903242752770795964017 420677432064578096973013)
              ·
                refine ⟨9859627314013549147805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 420677432064578096973013 9859627314013549147805)
                ·
                  rfl

theorem cell23_518442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 7].length) (baseStart_518442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518442 prefixEnd_518442 := by exact prefixLift 518442
  have htrace : WordTrace (prefixWord ++ tailWord_518442) baseStart_518442 baseEnd_518442 := by
    simpa [prefixWord, tailWord_518442, baseEnd_518442] using wordTrace_append hprefix tailTrace_518442
  have hstable : (prefixWord ++ tailWord_518442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518442).length < 2 ^ (prefixWord ++ tailWord_518442).sum := by decide
  have hdescent : baseEnd_518442 < baseStart_518442 := by decide
  rcases family_descends (prefixWord ++ tailWord_518442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518462 : List Nat := [4, 2, 1, 2, 1, 2, 2, 3, 1, 3, 2]
def baseStart_518462 : Nat := 118140960795 + 518462 * 2 ^ 59
def prefixEnd_518462 : Nat := 4983230072969 + 3 ^ 40 * 518462 * 2
def baseEnd_518462 : Nat := 266220207091455748740643

theorem tailTrace_518462 : CollatzResearch.WordTrace tailWord_518462 prefixEnd_518462 266220207091455748740643 := by
  unfold tailWord_518462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2363732830963524388147705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12606575098472130070121093 2363732830963524388147705)
  ·
    refine ⟨1772799623222643291110779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2363732830963524388147705 1772799623222643291110779)
    ·
      refine ⟨2659199434833964936666169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1772799623222643291110779 2659199434833964936666169)
      ·
        refine ⟨1994399576125473702499627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2659199434833964936666169 1994399576125473702499627)
        ·
          refine ⟨2991599364188210553749441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1994399576125473702499627 2991599364188210553749441)
          ·
            refine ⟨2243699523141157915312081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2991599364188210553749441 2243699523141157915312081)
            ·
              refine ⟨1682774642355868436484061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2243699523141157915312081 1682774642355868436484061)
              ·
                refine ⟨631040490883450663681523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1682774642355868436484061 631040490883450663681523)
                ·
                  refine ⟨946560736325175995522285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631040490883450663681523 946560736325175995522285)
                  ·
                    refine ⟨354960276121940998320857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 946560736325175995522285 354960276121940998320857)
                    ·
                      refine ⟨266220207091455748740643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 354960276121940998320857 266220207091455748740643)
                      ·
                        rfl

theorem cell23_518462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_518462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518462 prefixEnd_518462 := by exact prefixLift 518462
  have htrace : WordTrace (prefixWord ++ tailWord_518462) baseStart_518462 baseEnd_518462 := by
    simpa [prefixWord, tailWord_518462, baseEnd_518462] using wordTrace_append hprefix tailTrace_518462
  have hstable : (prefixWord ++ tailWord_518462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518462).length < 2 ^ (prefixWord ++ tailWord_518462).sum := by decide
  have hdescent : baseEnd_518462 < baseStart_518462 := by decide
  rcases family_descends (prefixWord ++ tailWord_518462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518625 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 1, 5, 2]
def baseStart_518625 : Nat := 118140960795 + 518625 * 2 ^ 59
def prefixEnd_518625 : Nat := 4983230072969 + 3 ^ 40 * 518625 * 2
def baseEnd_518625 : Nat := 266303904438138611002393

theorem tailTrace_518625 : CollatzResearch.WordTrace tailWord_518625 prefixEnd_518625 266303904438138611002393 := by
  unfold tailWord_518625
  simp only [CollatzResearch.WordTrace]
  refine ⟨18915807746117673943365329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12610538497411782628910219 18915807746117673943365329)
  ·
    refine ⟨14186855809588255457523997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18915807746117673943365329 14186855809588255457523997)
    ·
      refine ⟨5320070928595595796571499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14186855809588255457523997 5320070928595595796571499)
      ·
        refine ⟨7980106392893393694857249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5320070928595595796571499 7980106392893393694857249)
        ·
          refine ⟨5985079794670045271142937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7980106392893393694857249 5985079794670045271142937)
          ·
            refine ⟨4488809846002533953357203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5985079794670045271142937 4488809846002533953357203)
            ·
              refine ⟨6733214769003800930035805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4488809846002533953357203 6733214769003800930035805)
              ·
                refine ⟨2524955538376425348763427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6733214769003800930035805 2524955538376425348763427)
                ·
                  refine ⟨3787433307564638023145141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2524955538376425348763427 3787433307564638023145141)
                  ·
                    refine ⟨355071872584184814669857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3787433307564638023145141 355071872584184814669857)
                    ·
                      refine ⟨266303904438138611002393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 355071872584184814669857 266303904438138611002393)
                      ·
                        rfl

theorem cell23_518625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_518625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518625 prefixEnd_518625 := by exact prefixLift 518625
  have htrace : WordTrace (prefixWord ++ tailWord_518625) baseStart_518625 baseEnd_518625 := by
    simpa [prefixWord, tailWord_518625, baseEnd_518625] using wordTrace_append hprefix tailTrace_518625
  have hstable : (prefixWord ++ tailWord_518625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518625).length < 2 ^ (prefixWord ++ tailWord_518625).sum := by decide
  have hdescent : baseEnd_518625 < baseStart_518625 := by decide
  rcases family_descends (prefixWord ++ tailWord_518625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518669 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_518669 : Nat := 118140960795 + 518669 * 2 ^ 59
def prefixEnd_518669 : Nat := 4983230072969 + 3 ^ 40 * 518669 * 2
def baseEnd_518669 : Nat := 88775499195645479617397

theorem tailTrace_518669 : CollatzResearch.WordTrace tailWord_518669 prefixEnd_518669 88775499195645479617397 := by
  unfold tailWord_518669
  simp only [CollatzResearch.WordTrace]
  refine ⟨18917412557958269457967061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12611608371972179638644707 18917412557958269457967061)
  ·
    refine ⟨443376856827146940421103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 18917412557958269457967061 443376856827146940421103)
    ·
      refine ⟨665065285240720410631655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443376856827146940421103 665065285240720410631655)
      ·
        refine ⟨997597927861080615947483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665065285240720410631655 997597927861080615947483)
        ·
          refine ⟨1496396891791620923921225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997597927861080615947483 1496396891791620923921225)
          ·
            refine ⟨1122297668843715692940919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1496396891791620923921225 1122297668843715692940919)
            ·
              refine ⟨1683446503265573539411379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122297668843715692940919 1683446503265573539411379)
              ·
                refine ⟨2525169754898360309117069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1683446503265573539411379 2525169754898360309117069)
                ·
                  refine ⟨946938658086885115918901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2525169754898360309117069 946938658086885115918901)
                  ·
                    refine ⟨88775499195645479617397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 946938658086885115918901 88775499195645479617397)
                    ·
                      rfl

theorem cell23_518669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_518669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518669 prefixEnd_518669 := by exact prefixLift 518669
  have htrace : WordTrace (prefixWord ++ tailWord_518669) baseStart_518669 baseEnd_518669 := by
    simpa [prefixWord, tailWord_518669, baseEnd_518669] using wordTrace_append hprefix tailTrace_518669
  have hstable : (prefixWord ++ tailWord_518669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518669).length < 2 ^ (prefixWord ++ tailWord_518669).sum := by decide
  have hdescent : baseEnd_518669 < baseStart_518669 := by decide
  rcases family_descends (prefixWord ++ tailWord_518669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518675 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 3]
def baseStart_518675 : Nat := 118140960795 + 518675 * 2 ^ 59
def prefixEnd_518675 : Nat := 4983230072969 + 3 ^ 40 * 518675 * 2
def baseEnd_518675 : Nat := 266329578470863415377163

theorem tailTrace_518675 : CollatzResearch.WordTrace tailWord_518675 prefixEnd_518675 266329578470863415377163 := by
  unfold tailWord_518675
  simp only [CollatzResearch.WordTrace]
  refine ⟨18917631395936532482685479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12611754263957688321790319 18917631395936532482685479)
  ·
    refine ⟨28376447093904798724028219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18917631395936532482685479 28376447093904798724028219)
    ·
      refine ⟨42564670640857198086042329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28376447093904798724028219 42564670640857198086042329)
      ·
        refine ⟨31923502980642898564531747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42564670640857198086042329 31923502980642898564531747)
        ·
          refine ⟨47885254470964347846797621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31923502980642898564531747 47885254470964347846797621)
          ·
            refine ⟨4489242606652907610637277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47885254470964347846797621 4489242606652907610637277)
            ·
              refine ⟨1683465977494840353988979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4489242606652907610637277 1683465977494840353988979)
              ·
                refine ⟨2525198966242260530983469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1683465977494840353988979 2525198966242260530983469)
                ·
                  refine ⟨946949612340847699118801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2525198966242260530983469 946949612340847699118801)
                  ·
                    refine ⟨710212209255635774339101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 946949612340847699118801 710212209255635774339101)
                    ·
                      refine ⟨266329578470863415377163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 710212209255635774339101 266329578470863415377163)
                      ·
                        rfl

theorem cell23_518675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 3].length) (baseStart_518675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518675 prefixEnd_518675 := by exact prefixLift 518675
  have htrace : WordTrace (prefixWord ++ tailWord_518675) baseStart_518675 baseEnd_518675 := by
    simpa [prefixWord, tailWord_518675, baseEnd_518675] using wordTrace_append hprefix tailTrace_518675
  have hstable : (prefixWord ++ tailWord_518675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518675).length < 2 ^ (prefixWord ++ tailWord_518675).sum := by decide
  have hdescent : baseEnd_518675 < baseStart_518675 := by decide
  rcases family_descends (prefixWord ++ tailWord_518675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518676 : List Nat := [2, 4, 3, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_518676 : Nat := 118140960795 + 518676 * 2 ^ 59
def prefixEnd_518676 : Nat := 4983230072969 + 3 ^ 40 * 518676 * 2
def baseEnd_518676 : Nat := 266330091951517911464659

theorem tailTrace_518676 : CollatzResearch.WordTrace tailWord_518676 prefixEnd_518676 266330091951517911464659 := by
  unfold tailWord_518676
  simp only [CollatzResearch.WordTrace]
  refine ⟨9458833934466454826735941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12611778579288606435647921 9458833934466454826735941)
  ·
    refine ⟨1773531362712460280012989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9458833934466454826735941 1773531362712460280012989)
    ·
      refine ⟨665074261017172605004871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1773531362712460280012989 665074261017172605004871)
      ·
        refine ⟨997611391525758907507307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665074261017172605004871 997611391525758907507307)
        ·
          refine ⟨1496417087288638361260961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997611391525758907507307 1496417087288638361260961)
          ·
            refine ⟨1122312815466478770945721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1496417087288638361260961 1122312815466478770945721)
            ·
              refine ⟨841734611599859078209291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1122312815466478770945721 841734611599859078209291)
              ·
                refine ⟨1262601917399788617313937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841734611599859078209291 1262601917399788617313937)
                ·
                  refine ⟨946951438049841462985453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1262601917399788617313937 946951438049841462985453)
                  ·
                    refine ⟨355106789268690548619545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 946951438049841462985453 355106789268690548619545)
                    ·
                      refine ⟨266330091951517911464659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 355106789268690548619545 266330091951517911464659)
                      ·
                        rfl

theorem cell23_518676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_518676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518676 prefixEnd_518676 := by exact prefixLift 518676
  have htrace : WordTrace (prefixWord ++ tailWord_518676) baseStart_518676 baseEnd_518676 := by
    simpa [prefixWord, tailWord_518676, baseEnd_518676] using wordTrace_append hprefix tailTrace_518676
  have hstable : (prefixWord ++ tailWord_518676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518676).length < 2 ^ (prefixWord ++ tailWord_518676).sum := by decide
  have hdescent : baseEnd_518676 < baseStart_518676 := by decide
  rcases family_descends (prefixWord ++ tailWord_518676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518685 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_518685 : Nat := 118140960795 + 518685 * 2 ^ 59
def prefixEnd_518685 : Nat := 4983230072969 + 3 ^ 40 * 518685 * 2
def baseEnd_518685 : Nat := 266334713277408376252117

theorem tailTrace_518685 : CollatzResearch.WordTrace tailWord_518685 prefixEnd_518685 266334713277408376252117 := by
  unfold tailWord_518685
  simp only [CollatzResearch.WordTrace]
  refine ⟨18917996125900304190549509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12611997417266869460366339 18917996125900304190549509)
  ·
    refine ⟨3547124273606307035728033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18917996125900304190549509 3547124273606307035728033)
    ·
      refine ⟨2660343205204730276796025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3547124273606307035728033 2660343205204730276796025)
      ·
        refine ⟨1995257403903547707597019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2660343205204730276796025 1995257403903547707597019)
        ·
          refine ⟨2992886105855321561395529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1995257403903547707597019 2992886105855321561395529)
          ·
            refine ⟨2244664579391491171046647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2992886105855321561395529 2244664579391491171046647)
            ·
              refine ⟨3366996869087236756569971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2244664579391491171046647 3366996869087236756569971)
              ·
                refine ⟨5050495303630855134854957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3366996869087236756569971 5050495303630855134854957)
                ·
                  refine ⟨1893935738861570675570609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5050495303630855134854957 1893935738861570675570609)
                  ·
                    refine ⟨1420451804146178006677957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1893935738861570675570609 1420451804146178006677957)
                    ·
                      refine ⟨266334713277408376252117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1420451804146178006677957 266334713277408376252117)
                      ·
                        rfl

theorem cell23_518685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_518685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518685 prefixEnd_518685 := by exact prefixLift 518685
  have htrace : WordTrace (prefixWord ++ tailWord_518685) baseStart_518685 baseEnd_518685 := by
    simpa [prefixWord, tailWord_518685, baseEnd_518685] using wordTrace_append hprefix tailTrace_518685
  have hstable : (prefixWord ++ tailWord_518685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518685).length < 2 ^ (prefixWord ++ tailWord_518685).sum := by decide
  have hdescent : baseEnd_518685 < baseStart_518685 := by decide
  rcases family_descends (prefixWord ++ tailWord_518685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518695 : List Nat := [1, 1, 7, 2, 12]
def baseStart_518695 : Nat := 118140960795 + 518695 * 2 ^ 59
def prefixEnd_518695 : Nat := 4983230072969 + 3 ^ 40 * 518695 * 2
def baseEnd_518695 : Nat := 365349585849044358199

theorem tailTrace_518695 : CollatzResearch.WordTrace tailWord_518695 prefixEnd_518695 365349585849044358199 := by
  unfold tailWord_518695
  simp only [CollatzResearch.WordTrace]
  refine ⟨18918360855864075898413539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12612240570576050598942359 18918360855864075898413539)
  ·
    refine ⟨28377541283796113847620309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18918360855864075898413539 28377541283796113847620309)
    ·
      refine ⟨665098623838971418303601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 28377541283796113847620309 665098623838971418303601)
      ·
        refine ⟨498823967879228563727701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 665098623838971418303601 498823967879228563727701)
        ·
          refine ⟨365349585849044358199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 498823967879228563727701 365349585849044358199)
          ·
            rfl

theorem cell23_518695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 12].length) (baseStart_518695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518695 prefixEnd_518695 := by exact prefixLift 518695
  have htrace : WordTrace (prefixWord ++ tailWord_518695) baseStart_518695 baseEnd_518695 := by
    simpa [prefixWord, tailWord_518695, baseEnd_518695] using wordTrace_append hprefix tailTrace_518695
  have hstable : (prefixWord ++ tailWord_518695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518695).length < 2 ^ (prefixWord ++ tailWord_518695).sum := by decide
  have hdescent : baseEnd_518695 < baseStart_518695 := by decide
  rcases family_descends (prefixWord ++ tailWord_518695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518732 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 3, 3, 2]
def baseStart_518732 : Nat := 118140960795 + 518732 * 2 ^ 59
def prefixEnd_518732 : Nat := 4983230072969 + 3 ^ 40 * 518732 * 2
def baseEnd_518732 : Nat := 266358846868169692364401

theorem tailTrace_518732 : CollatzResearch.WordTrace tailWord_518732 prefixEnd_518732 266358846868169692364401 := by
  unfold tailWord_518732
  simp only [CollatzResearch.WordTrace]
  refine ⟨9459855178365015608755225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12613140237820020811673633 9459855178365015608755225)
  ·
    refine ⟨7094891383773761706566419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9459855178365015608755225 7094891383773761706566419)
    ·
      refine ⟨10642337075660642559849629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7094891383773761706566419 10642337075660642559849629)
      ·
        refine ⟨3990876403372740959943611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10642337075660642559849629 3990876403372740959943611)
        ·
          refine ⟨5986314605059111439915417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3990876403372740959943611 5986314605059111439915417)
          ·
            refine ⟨4489735953794333579936563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5986314605059111439915417 4489735953794333579936563)
            ·
              refine ⟨6734603930691500369904845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4489735953794333579936563 6734603930691500369904845)
              ·
                refine ⟨2525476474009312638714317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6734603930691500369904845 2525476474009312638714317)
                ·
                  refine ⟨947053677753492239517869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2525476474009312638714317 947053677753492239517869)
                  ·
                    refine ⟨355145129157559589819201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 947053677753492239517869 355145129157559589819201)
                    ·
                      refine ⟨266358846868169692364401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 355145129157559589819201 266358846868169692364401)
                      ·
                        rfl

theorem cell23_518732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_518732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518732 prefixEnd_518732 := by exact prefixLift 518732
  have htrace : WordTrace (prefixWord ++ tailWord_518732) baseStart_518732 baseEnd_518732 := by
    simpa [prefixWord, tailWord_518732, baseEnd_518732] using wordTrace_append hprefix tailTrace_518732
  have hstable : (prefixWord ++ tailWord_518732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518732).length < 2 ^ (prefixWord ++ tailWord_518732).sum := by decide
  have hdescent : baseEnd_518732 < baseStart_518732 := by decide
  rcases family_descends (prefixWord ++ tailWord_518732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518750 : List Nat := [4, 4, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_518750 : Nat := 118140960795 + 518750 * 2 ^ 59
def prefixEnd_518750 : Nat := 4983230072969 + 3 ^ 40 * 518750 * 2
def baseEnd_518750 : Nat := 88789363173316873979773

theorem tailTrace_518750 : CollatzResearch.WordTrace tailWord_518750 prefixEnd_518750 88789363173316873979773 := by
  unfold tailWord_518750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2365045858833102536458213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12613577913776546861110469 2365045858833102536458213)
  ·
    refine ⟨443446098531206725585915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2365045858833102536458213 443446098531206725585915)
    ·
      refine ⟨665169147796810088378873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443446098531206725585915 665169147796810088378873)
      ·
        refine ⟨498876860847607566284155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 665169147796810088378873 498876860847607566284155)
        ·
          refine ⟨748315291271411349426233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498876860847607566284155 748315291271411349426233)
          ·
            refine ⟨561236468453558512069675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 748315291271411349426233 561236468453558512069675)
            ·
              refine ⟨841854702680337768104513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561236468453558512069675 841854702680337768104513)
              ·
                refine ⟨631391027010253326078385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 841854702680337768104513 631391027010253326078385)
                ·
                  refine ⟨473543270257689994558789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631391027010253326078385 473543270257689994558789)
                  ·
                    refine ⟨88789363173316873979773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 473543270257689994558789 88789363173316873979773)
                    ·
                      rfl

theorem cell23_518750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_518750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518750 prefixEnd_518750 := by exact prefixLift 518750
  have htrace : WordTrace (prefixWord ++ tailWord_518750) baseStart_518750 baseEnd_518750 := by
    simpa [prefixWord, tailWord_518750, baseEnd_518750] using wordTrace_append hprefix tailTrace_518750
  have hstable : (prefixWord ++ tailWord_518750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518750).length < 2 ^ (prefixWord ++ tailWord_518750).sum := by decide
  have hdescent : baseEnd_518750 < baseStart_518750 := by decide
  rcases family_descends (prefixWord ++ tailWord_518750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518773 : List Nat := [1, 3, 4, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_518773 : Nat := 118140960795 + 518773 * 2 ^ 59
def prefixEnd_518773 : Nat := 4983230072969 + 3 ^ 40 * 518773 * 2
def baseEnd_518773 : Nat := 266379899575004031951713

theorem tailTrace_518773 : CollatzResearch.WordTrace tailWord_518773 prefixEnd_518773 266379899575004031951713 := by
  unfold tailWord_518773
  simp only [CollatzResearch.WordTrace]
  refine ⟨18921205749581495219752973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12614137166387663479835315 18921205749581495219752973)
  ·
    refine ⟨7095452156093060707407365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18921205749581495219752973 7095452156093060707407365)
    ·
      refine ⟨1330397279267448882638881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7095452156093060707407365 1330397279267448882638881)
      ·
        refine ⟨997797959450586661979161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1330397279267448882638881 997797959450586661979161)
        ·
          refine ⟨748348469587939996484371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 997797959450586661979161 748348469587939996484371)
          ·
            refine ⟨1122522704381909994726557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748348469587939996484371 1122522704381909994726557)
            ·
              refine ⟨420946014143216248022459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1122522704381909994726557 420946014143216248022459)
              ·
                refine ⟨631419021214824372033689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420946014143216248022459 631419021214824372033689)
                ·
                  refine ⟨473564265911118279025267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631419021214824372033689 473564265911118279025267)
                  ·
                    refine ⟨710346398866677418537901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 473564265911118279025267 710346398866677418537901)
                    ·
                      refine ⟨266379899575004031951713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 710346398866677418537901 266379899575004031951713)
                      ·
                        rfl

theorem cell23_518773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_518773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518773 prefixEnd_518773 := by exact prefixLift 518773
  have htrace : WordTrace (prefixWord ++ tailWord_518773) baseStart_518773 baseEnd_518773 := by
    simpa [prefixWord, tailWord_518773, baseEnd_518773] using wordTrace_append hprefix tailTrace_518773
  have hstable : (prefixWord ++ tailWord_518773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518773).length < 2 ^ (prefixWord ++ tailWord_518773).sum := by decide
  have hdescent : baseEnd_518773 < baseStart_518773 := by decide
  rcases family_descends (prefixWord ++ tailWord_518773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518775 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 4]
def baseStart_518775 : Nat := 118140960795 + 518775 * 2 ^ 59
def prefixEnd_518775 : Nat := 4983230072969 + 3 ^ 40 * 518775 * 2
def baseEnd_518775 : Nat := 266380926536313024126703

theorem tailTrace_518775 : CollatzResearch.WordTrace tailWord_518775 prefixEnd_518775 266380926536313024126703 := by
  unfold tailWord_518775
  simp only [CollatzResearch.WordTrace]
  refine ⟨18921278695574249561325779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12614185797049499707550519 18921278695574249561325779)
  ·
    refine ⟨28381918043361374341988669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18921278695574249561325779 28381918043361374341988669)
    ·
      refine ⟨10643219266260515378245751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28381918043361374341988669 10643219266260515378245751)
      ·
        refine ⟨15964828899390773067368627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10643219266260515378245751 15964828899390773067368627)
        ·
          refine ⟨23947243349086159601052941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15964828899390773067368627 23947243349086159601052941)
          ·
            refine ⟨8980216255907309850394853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23947243349086159601052941 8980216255907309850394853)
            ·
              refine ⟨1683790547982620596949035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8980216255907309850394853 1683790547982620596949035)
              ·
                refine ⟨2525685821973930895423553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1683790547982620596949035 2525685821973930895423553)
                ·
                  refine ⟨1894264366480448171567665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2525685821973930895423553 1894264366480448171567665)
                  ·
                    refine ⟨1420698274860336128675749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1894264366480448171567665 1420698274860336128675749)
                    ·
                      refine ⟨266380926536313024126703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1420698274860336128675749 266380926536313024126703)
                      ·
                        rfl

theorem cell23_518775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_518775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518775 prefixEnd_518775 := by exact prefixLift 518775
  have htrace : WordTrace (prefixWord ++ tailWord_518775) baseStart_518775 baseEnd_518775 := by
    simpa [prefixWord, tailWord_518775, baseEnd_518775] using wordTrace_append hprefix tailTrace_518775
  have hstable : (prefixWord ++ tailWord_518775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518775).length < 2 ^ (prefixWord ++ tailWord_518775).sum := by decide
  have hdescent : baseEnd_518775 < baseStart_518775 := by decide
  rcases family_descends (prefixWord ++ tailWord_518775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518785 : List Nat := [1, 2, 4, 2, 1, 1, 1, 4, 7]
def baseStart_518785 : Nat := 118140960795 + 518785 * 2 ^ 59
def prefixEnd_518785 : Nat := 4983230072969 + 3 ^ 40 * 518785 * 2
def baseEnd_518785 : Nat := 29598451260317553889073

theorem tailTrace_518785 : CollatzResearch.WordTrace tailWord_518785 prefixEnd_518785 29598451260317553889073 := by
  unfold tailWord_518785
  simp only [CollatzResearch.WordTrace]
  refine ⟨18921643425538021269189809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12614428950358680846126539 18921643425538021269189809)
  ·
    refine ⟨14191232569153515951892357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18921643425538021269189809 14191232569153515951892357)
    ·
      refine ⟨2660856106716284240979817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14191232569153515951892357 2660856106716284240979817)
      ·
        refine ⟨1995642080037213180734863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2660856106716284240979817 1995642080037213180734863)
        ·
          refine ⟨2993463120055819771102295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1995642080037213180734863 2993463120055819771102295)
          ·
            refine ⟨4490194680083729656653443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2993463120055819771102295 4490194680083729656653443)
            ·
              refine ⟨6735292020125594484980165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4490194680083729656653443 6735292020125594484980165)
              ·
                refine ⟨1262867253773548965933781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6735292020125594484980165 1262867253773548965933781)
                ·
                  refine ⟨29598451260317553889073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1262867253773548965933781 29598451260317553889073)
                  ·
                    rfl

theorem cell23_518785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 7].length) (baseStart_518785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518785 prefixEnd_518785 := by exact prefixLift 518785
  have htrace : WordTrace (prefixWord ++ tailWord_518785) baseStart_518785 baseEnd_518785 := by
    simpa [prefixWord, tailWord_518785, baseEnd_518785] using wordTrace_append hprefix tailTrace_518785
  have hstable : (prefixWord ++ tailWord_518785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518785).length < 2 ^ (prefixWord ++ tailWord_518785).sum := by decide
  have hdescent : baseEnd_518785 < baseStart_518785 := by decide
  rcases family_descends (prefixWord ++ tailWord_518785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518795 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 3]
def baseStart_518795 : Nat := 118140960795 + 518795 * 2 ^ 59
def prefixEnd_518795 : Nat := 4983230072969 + 3 ^ 40 * 518795 * 2
def baseEnd_518795 : Nat := 266391196149402945876611

theorem tailTrace_518795 : CollatzResearch.WordTrace tailWord_518795 prefixEnd_518795 266391196149402945876611 := by
  unfold tailWord_518795
  simp only [CollatzResearch.WordTrace]
  refine ⟨18922008155501792977053839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12614672103667861984702559 18922008155501792977053839)
  ·
    refine ⟨28383012233252689465580759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18922008155501792977053839 28383012233252689465580759)
    ·
      refine ⟨42574518349879034198371139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28383012233252689465580759 42574518349879034198371139)
      ·
        refine ⟨63861777524818551297556709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42574518349879034198371139 63861777524818551297556709)
        ·
          refine ⟨11974083285903478368291883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63861777524818551297556709 11974083285903478368291883)
          ·
            refine ⟨17961124928855217552437825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11974083285903478368291883 17961124928855217552437825)
            ·
              refine ⟨13470843696641413164328369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17961124928855217552437825 13470843696641413164328369)
              ·
                refine ⟨10103132772481059873246277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13470843696641413164328369 10103132772481059873246277)
                ·
                  refine ⟨1894337394840198726233677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10103132772481059873246277 1894337394840198726233677)
                  ·
                    refine ⟨710376523065074522337629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1894337394840198726233677 710376523065074522337629)
                    ·
                      refine ⟨266391196149402945876611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 710376523065074522337629 266391196149402945876611)
                      ·
                        rfl

theorem cell23_518795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 3].length) (baseStart_518795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518795 prefixEnd_518795 := by exact prefixLift 518795
  have htrace : WordTrace (prefixWord ++ tailWord_518795) baseStart_518795 baseEnd_518795 := by
    simpa [prefixWord, tailWord_518795, baseEnd_518795] using wordTrace_append hprefix tailTrace_518795
  have hstable : (prefixWord ++ tailWord_518795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518795).length < 2 ^ (prefixWord ++ tailWord_518795).sum := by decide
  have hdescent : baseEnd_518795 < baseStart_518795 := by decide
  rcases family_descends (prefixWord ++ tailWord_518795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518830 : List Nat := [4, 1, 4, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_518830 : Nat := 118140960795 + 518830 * 2 ^ 59
def prefixEnd_518830 : Nat := 4983230072969 + 3 ^ 40 * 518830 * 2
def baseEnd_518830 : Nat := 266409167972310308938951

theorem tailTrace_518830 : CollatzResearch.WordTrace tailWord_518830 prefixEnd_518830 266409167972310308938951 := by
  unfold tailWord_518830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2365410588796874244322243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12615523140249995969718629 2365410588796874244322243)
  ·
    refine ⟨3548115883195311366483365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2365410588796874244322243 3548115883195311366483365)
    ·
      refine ⟨665271728099120881215631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3548115883195311366483365 665271728099120881215631)
      ·
        refine ⟨997907592148681321823447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665271728099120881215631 997907592148681321823447)
        ·
          refine ⟨1496861388223021982735171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997907592148681321823447 1496861388223021982735171)
          ·
            refine ⟨2245292082334532974102757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496861388223021982735171 2245292082334532974102757)
            ·
              refine ⟨420992265437724932644267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2245292082334532974102757 420992265437724932644267)
              ·
                refine ⟨631488398156587398966401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420992265437724932644267 631488398156587398966401)
                ·
                  refine ⟨473616298617440549224801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631488398156587398966401 473616298617440549224801)
                  ·
                    refine ⟨355212223963080411918601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 473616298617440549224801 355212223963080411918601)
                    ·
                      refine ⟨266409167972310308938951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 355212223963080411918601 266409167972310308938951)
                      ·
                        rfl

theorem cell23_518830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_518830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518830 prefixEnd_518830 := by exact prefixLift 518830
  have htrace : WordTrace (prefixWord ++ tailWord_518830) baseStart_518830 baseEnd_518830 := by
    simpa [prefixWord, tailWord_518830, baseEnd_518830] using wordTrace_append hprefix tailTrace_518830
  have hstable : (prefixWord ++ tailWord_518830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518830).length < 2 ^ (prefixWord ++ tailWord_518830).sum := by decide
  have hdescent : baseEnd_518830 < baseStart_518830 := by decide
  rcases family_descends (prefixWord ++ tailWord_518830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518865 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 2, 1, 6]
def baseStart_518865 : Nat := 118140960795 + 518865 * 2 ^ 59
def prefixEnd_518865 : Nat := 4983230072969 + 3 ^ 40 * 518865 * 2
def baseEnd_518865 : Nat := 266427139795217672001289

theorem tailTrace_518865 : CollatzResearch.WordTrace tailWord_518865 prefixEnd_518865 266427139795217672001289 := by
  unfold tailWord_518865
  simp only [CollatzResearch.WordTrace]
  refine ⟨18924561265248194932102049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12616374176832129954734699 18924561265248194932102049)
  ·
    refine ⟨14193420948936146199076537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18924561265248194932102049 14193420948936146199076537)
    ·
      refine ⟨10645065711702109649307403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14193420948936146199076537 10645065711702109649307403)
      ·
        refine ⟨15967598567553164473961105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10645065711702109649307403 15967598567553164473961105)
        ·
          refine ⟨11975698925664873355470829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15967598567553164473961105 11975698925664873355470829)
          ·
            refine ⟨4490887097124327508301561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11975698925664873355470829 4490887097124327508301561)
            ·
              refine ⟨3368165322843245631226171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4490887097124327508301561 3368165322843245631226171)
              ·
                refine ⟨5052247984264868446839257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368165322843245631226171 5052247984264868446839257)
                ·
                  refine ⟨3789185988198651335129443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5052247984264868446839257 3789185988198651335129443)
                  ·
                    refine ⟨5683778982297977002694165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3789185988198651335129443 5683778982297977002694165)
                    ·
                      refine ⟨266427139795217672001289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5683778982297977002694165 266427139795217672001289)
                      ·
                        rfl

theorem cell23_518865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_518865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518865 prefixEnd_518865 := by exact prefixLift 518865
  have htrace : WordTrace (prefixWord ++ tailWord_518865) baseStart_518865 baseEnd_518865 := by
    simpa [prefixWord, tailWord_518865, baseEnd_518865] using wordTrace_append hprefix tailTrace_518865
  have hstable : (prefixWord ++ tailWord_518865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518865).length < 2 ^ (prefixWord ++ tailWord_518865).sum := by decide
  have hdescent : baseEnd_518865 < baseStart_518865 := by decide
  rcases family_descends (prefixWord ++ tailWord_518865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518900 : List Nat := [2, 6, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_518900 : Nat := 118140960795 + 518900 * 2 ^ 59
def prefixEnd_518900 : Nat := 4983230072969 + 3 ^ 40 * 518900 * 2
def baseEnd_518900 : Nat := 88815037206041678354543

theorem tailTrace_518900 : CollatzResearch.WordTrace tailWord_518900 prefixEnd_518900 88815037206041678354543 := by
  unfold tailWord_518900
  simp only [CollatzResearch.WordTrace]
  refine ⟨9462918910060697954813077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12617225213414263939750769 9462918910060697954813077)
  ·
    refine ⟨443574323909095216631863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9462918910060697954813077 443574323909095216631863)
    ·
      refine ⟨665361485863642824947795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443574323909095216631863 665361485863642824947795)
      ·
        refine ⟨998042228795464237421693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665361485863642824947795 998042228795464237421693)
        ·
          refine ⟨374265835798299089033135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 998042228795464237421693 374265835798299089033135)
          ·
            refine ⟨561398753697448633549703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374265835798299089033135 561398753697448633549703)
            ·
              refine ⟨842098130546172950324555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561398753697448633549703 842098130546172950324555)
              ·
                refine ⟨1263147195819259425486833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842098130546172950324555 1263147195819259425486833)
                ·
                  refine ⟨947360396864444569115125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1263147195819259425486833 947360396864444569115125)
                  ·
                    refine ⟨88815037206041678354543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 947360396864444569115125 88815037206041678354543)
                    ·
                      rfl

theorem cell23_518900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_518900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518900 prefixEnd_518900 := by exact prefixLift 518900
  have htrace : WordTrace (prefixWord ++ tailWord_518900) baseStart_518900 baseEnd_518900 := by
    simpa [prefixWord, tailWord_518900, baseEnd_518900] using wordTrace_append hprefix tailTrace_518900
  have hstable : (prefixWord ++ tailWord_518900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518900).length < 2 ^ (prefixWord ++ tailWord_518900).sum := by decide
  have hdescent : baseEnd_518900 < baseStart_518900 := by decide
  rcases family_descends (prefixWord ++ tailWord_518900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518915 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 5]
def baseStart_518915 : Nat := 118140960795 + 518915 * 2 ^ 59
def prefixEnd_518915 : Nat := 4983230072969 + 3 ^ 40 * 518915 * 2
def baseEnd_518915 : Nat := 266452813827942476376059

theorem tailTrace_518915 : CollatzResearch.WordTrace tailWord_518915 prefixEnd_518915 266452813827942476376059 := by
  unfold tailWord_518915
  simp only [CollatzResearch.WordTrace]
  refine ⟨18926384915067053471422199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12617589943378035647614799 18926384915067053471422199)
  ·
    refine ⟨28389577372600580207133299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18926384915067053471422199 28389577372600580207133299)
    ·
      refine ⟨42584366058900870310699949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28389577372600580207133299 42584366058900870310699949)
      ·
        refine ⟨15969137272087826366512481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42584366058900870310699949 15969137272087826366512481)
        ·
          refine ⟨11976852954065869774884361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15969137272087826366512481 11976852954065869774884361)
          ·
            refine ⟨8982639715549402331163271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11976852954065869774884361 8982639715549402331163271)
            ·
              refine ⟨13473959573324103496744907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8982639715549402331163271 13473959573324103496744907)
              ·
                refine ⟨20210939359986155245117361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13473959573324103496744907 20210939359986155245117361)
                ·
                  refine ⟨15158204519989616433838021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20210939359986155245117361 15158204519989616433838021)
                  ·
                    refine ⟨2842163347498053081344629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15158204519989616433838021 2842163347498053081344629)
                    ·
                      refine ⟨266452813827942476376059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2842163347498053081344629 266452813827942476376059)
                      ·
                        rfl

theorem cell23_518915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_518915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518915 prefixEnd_518915 := by exact prefixLift 518915
  have htrace : WordTrace (prefixWord ++ tailWord_518915) baseStart_518915 baseEnd_518915 := by
    simpa [prefixWord, tailWord_518915, baseEnd_518915] using wordTrace_append hprefix tailTrace_518915
  have hstable : (prefixWord ++ tailWord_518915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518915).length < 2 ^ (prefixWord ++ tailWord_518915).sum := by decide
  have hdescent : baseEnd_518915 < baseStart_518915 := by decide
  rcases family_descends (prefixWord ++ tailWord_518915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518929 : List Nat := [1, 2, 2, 1, 1, 3, 2, 4, 2, 3, 2]
def baseStart_518929 : Nat := 118140960795 + 518929 * 2 ^ 59
def prefixEnd_518929 : Nat := 4983230072969 + 3 ^ 40 * 518929 * 2
def baseEnd_518929 : Nat := 266460002557105421600995

theorem tailTrace_518929 : CollatzResearch.WordTrace tailWord_518929 prefixEnd_518929 266460002557105421600995 := by
  unfold tailWord_518929
  simp only [CollatzResearch.WordTrace]
  refine ⟨18926895537016333862431841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12617930358010889241621227 18926895537016333862431841)
  ·
    refine ⟨14195171652762250396823881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18926895537016333862431841 14195171652762250396823881)
    ·
      refine ⟨10646378739571687797617911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14195171652762250396823881 10646378739571687797617911)
      ·
        refine ⟨15969568109357531696426867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10646378739571687797617911 15969568109357531696426867)
        ·
          refine ⟨23954352164036297544640301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15969568109357531696426867 23954352164036297544640301)
          ·
            refine ⟨8982882061513611579240113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23954352164036297544640301 8982882061513611579240113)
            ·
              refine ⟨6737161546135208684430085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8982882061513611579240113 6737161546135208684430085)
              ·
                refine ⟨1263217789900351628330641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6737161546135208684430085 1263217789900351628330641)
                ·
                  refine ⟨947413342425263721247981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1263217789900351628330641 947413342425263721247981)
                  ·
                    refine ⟨355280003409473895467993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 947413342425263721247981 355280003409473895467993)
                    ·
                      refine ⟨266460002557105421600995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 355280003409473895467993 266460002557105421600995)
                      ·
                        rfl

theorem cell23_518929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 3, 2].length) (baseStart_518929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518929 prefixEnd_518929 := by exact prefixLift 518929
  have htrace : WordTrace (prefixWord ++ tailWord_518929) baseStart_518929 baseEnd_518929 := by
    simpa [prefixWord, tailWord_518929, baseEnd_518929] using wordTrace_append hprefix tailTrace_518929
  have hstable : (prefixWord ++ tailWord_518929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518929).length < 2 ^ (prefixWord ++ tailWord_518929).sum := by decide
  have hdescent : baseEnd_518929 < baseStart_518929 := by decide
  rcases family_descends (prefixWord ++ tailWord_518929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518962 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_518962 : Nat := 118140960795 + 518962 * 2 ^ 59
def prefixEnd_518962 : Nat := 4983230072969 + 3 ^ 40 * 518962 * 2
def baseEnd_518962 : Nat := 266476947418703792488343

theorem tailTrace_518962 : CollatzResearch.WordTrace tailWord_518962 prefixEnd_518962 266476947418703792488343 := by
  unfold tailWord_518962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4732024786474195124595785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12618732763931186998922093 4732024786474195124595785)
  ·
    refine ⟨3549018589855646343446839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4732024786474195124595785 3549018589855646343446839)
    ·
      refine ⟨5323527884783469515170259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3549018589855646343446839 5323527884783469515170259)
      ·
        refine ⟨7985291827175204272755389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5323527884783469515170259 7985291827175204272755389)
        ·
          refine ⟨2994484435190701602283271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7985291827175204272755389 2994484435190701602283271)
          ·
            refine ⟨4491726652786052403424907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994484435190701602283271 4491726652786052403424907)
            ·
              refine ⟨6737589979179078605137361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4491726652786052403424907 6737589979179078605137361)
              ·
                refine ⟨5053192484384308953853021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6737589979179078605137361 5053192484384308953853021)
                ·
                  refine ⟨1894947181644115857694883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5053192484384308953853021 1894947181644115857694883)
                  ·
                    refine ⟨2842420772466173786542325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1894947181644115857694883 2842420772466173786542325)
                    ·
                      refine ⟨266476947418703792488343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2842420772466173786542325 266476947418703792488343)
                      ·
                        rfl

theorem cell23_518962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_518962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518962 prefixEnd_518962 := by exact prefixLift 518962
  have htrace : WordTrace (prefixWord ++ tailWord_518962) baseStart_518962 baseEnd_518962 := by
    simpa [prefixWord, tailWord_518962, baseEnd_518962] using wordTrace_append hprefix tailTrace_518962
  have hstable : (prefixWord ++ tailWord_518962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518962).length < 2 ^ (prefixWord ++ tailWord_518962).sum := by decide
  have hdescent : baseEnd_518962 < baseStart_518962 := by decide
  rcases family_descends (prefixWord ++ tailWord_518962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518970 : List Nat := [3, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3]
def baseStart_518970 : Nat := 118140960795 + 518970 * 2 ^ 59
def prefixEnd_518970 : Nat := 4983230072969 + 3 ^ 40 * 518970 * 2
def baseEnd_518970 : Nat := 266481055263939761188307

theorem tailTrace_518970 : CollatzResearch.WordTrace tailWord_518970 prefixEnd_518970 266481055263939761188307 := by
  unfold tailWord_518970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4732097732466949466168591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12618927286578531909782909 4732097732466949466168591)
  ·
    refine ⟨7098146598700424199252887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4732097732466949466168591 7098146598700424199252887)
    ·
      refine ⟨10647219898050636298879331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7098146598700424199252887 10647219898050636298879331)
      ·
        refine ⟨15970829847075954448318997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10647219898050636298879331 15970829847075954448318997)
        ·
          refine ⟨748632649081685364764953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15970829847075954448318997 748632649081685364764953)
          ·
            refine ⟨561474486811264023573715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 748632649081685364764953 561474486811264023573715)
            ·
              refine ⟨842211730216896035360573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561474486811264023573715 842211730216896035360573)
              ·
                refine ⟨315829398831336013260215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 842211730216896035360573 315829398831336013260215)
                ·
                  refine ⟨473744098247004019890323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315829398831336013260215 473744098247004019890323)
                  ·
                    refine ⟨710616147370506029835485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 473744098247004019890323 710616147370506029835485)
                    ·
                      refine ⟨266481055263939761188307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 710616147370506029835485 266481055263939761188307)
                      ·
                        rfl

theorem cell23_518970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3].length) (baseStart_518970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518970 prefixEnd_518970 := by exact prefixLift 518970
  have htrace : WordTrace (prefixWord ++ tailWord_518970) baseStart_518970 baseEnd_518970 := by
    simpa [prefixWord, tailWord_518970, baseEnd_518970] using wordTrace_append hprefix tailTrace_518970
  have hstable : (prefixWord ++ tailWord_518970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518970).length < 2 ^ (prefixWord ++ tailWord_518970).sum := by decide
  have hdescent : baseEnd_518970 < baseStart_518970 := by decide
  rcases family_descends (prefixWord ++ tailWord_518970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518972 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_518972 : Nat := 118140960795 + 518972 * 2 ^ 59
def prefixEnd_518972 : Nat := 4983230072969 + 3 ^ 40 * 518972 * 2
def baseEnd_518972 : Nat := 266482082225248753363297

theorem tailTrace_518972 : CollatzResearch.WordTrace tailWord_518972 prefixEnd_518972 266482082225248753363297 := by
  unfold tailWord_518972
  simp only [CollatzResearch.WordTrace]
  refine ⟨9464231937930276103123585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12618975917240368137498113 9464231937930276103123585)
  ·
    refine ⟨7098173953447707077342689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9464231937930276103123585 7098173953447707077342689)
    ·
      refine ⟨5323630465085780308007017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7098173953447707077342689 5323630465085780308007017)
      ·
        refine ⟨3992722848814335231005263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5323630465085780308007017 3992722848814335231005263)
        ·
          refine ⟨5989084273221502846507895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3992722848814335231005263 5989084273221502846507895)
          ·
            refine ⟨8983626409832254269761843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5989084273221502846507895 8983626409832254269761843)
            ·
              refine ⟨13475439614748381404642765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8983626409832254269761843 13475439614748381404642765)
              ·
                refine ⟨5053289855530643026741037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13475439614748381404642765 5053289855530643026741037)
                ·
                  refine ⟨1894983695823991135027889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5053289855530643026741037 1894983695823991135027889)
                  ·
                    refine ⟨1421237771867993351270917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1894983695823991135027889 1421237771867993351270917)
                    ·
                      refine ⟨266482082225248753363297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1421237771867993351270917 266482082225248753363297)
                      ·
                        rfl

theorem cell23_518972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_518972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518972 prefixEnd_518972 := by exact prefixLift 518972
  have htrace : WordTrace (prefixWord ++ tailWord_518972) baseStart_518972 baseEnd_518972 := by
    simpa [prefixWord, tailWord_518972, baseEnd_518972] using wordTrace_append hprefix tailTrace_518972
  have hstable : (prefixWord ++ tailWord_518972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518972).length < 2 ^ (prefixWord ++ tailWord_518972).sum := by decide
  have hdescent : baseEnd_518972 < baseStart_518972 := by decide
  rcases family_descends (prefixWord ++ tailWord_518972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518979 : List Nat := [1, 1, 1, 3, 1, 4, 1, 5, 1, 2, 3]
def baseStart_518979 : Nat := 118140960795 + 518979 * 2 ^ 59
def prefixEnd_518979 : Nat := 4983230072969 + 3 ^ 40 * 518979 * 2
def baseEnd_518979 : Nat := 266485676589830225975765

theorem tailTrace_518979 : CollatzResearch.WordTrace tailWord_518979 prefixEnd_518979 266485676589830225975765 := by
  unfold tailWord_518979
  simp only [CollatzResearch.WordTrace]
  refine ⟨18928719186835192401751991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12619146124556794934501327 18928719186835192401751991)
  ·
    refine ⟨28393078780252788602627987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18928719186835192401751991 28393078780252788602627987)
    ·
      refine ⟨42589618170379182903941981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28393078780252788602627987 42589618170379182903941981)
      ·
        refine ⟨15971106813892193588978243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42589618170379182903941981 15971106813892193588978243)
        ·
          refine ⟨23956660220838290383467365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15971106813892193588978243 23956660220838290383467365)
          ·
            refine ⟨4491873791407179446900131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23956660220838290383467365 4491873791407179446900131)
            ·
              refine ⟨6737810687110769170350197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4491873791407179446900131 6737810687110769170350197)
              ·
                refine ⟨631669751916634609720331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6737810687110769170350197 631669751916634609720331)
                ·
                  refine ⟨947504627874951914580497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631669751916634609720331 947504627874951914580497)
                  ·
                    refine ⟨710628470906213935935373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 947504627874951914580497 710628470906213935935373)
                    ·
                      refine ⟨266485676589830225975765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 710628470906213935935373 266485676589830225975765)
                      ·
                        rfl

theorem cell23_518979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 2, 3].length) (baseStart_518979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518979 prefixEnd_518979 := by exact prefixLift 518979
  have htrace : WordTrace (prefixWord ++ tailWord_518979) baseStart_518979 baseEnd_518979 := by
    simpa [prefixWord, tailWord_518979, baseEnd_518979] using wordTrace_append hprefix tailTrace_518979
  have hstable : (prefixWord ++ tailWord_518979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518979).length < 2 ^ (prefixWord ++ tailWord_518979).sum := by decide
  have hdescent : baseEnd_518979 < baseStart_518979 := by decide
  rcases family_descends (prefixWord ++ tailWord_518979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518980 : List Nat := [2, 3, 4, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_518980 : Nat := 118140960795 + 518980 * 2 ^ 59
def prefixEnd_518980 : Nat := 4983230072969 + 3 ^ 40 * 518980 * 2
def baseEnd_518980 : Nat := 266486190070484722063261

theorem tailTrace_518980 : CollatzResearch.WordTrace tailWord_518980 prefixEnd_518980 266486190070484722063261 := by
  unfold tailWord_518980
  simp only [CollatzResearch.WordTrace]
  refine ⟨9464377829915784786269197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12619170439887713048358929 9464377829915784786269197)
  ·
    refine ⟨3549141686218419294850949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9464377829915784786269197 3549141686218419294850949)
    ·
      refine ⟨665464066165953617784553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3549141686218419294850949 665464066165953617784553)
      ·
        refine ⟨499098049624465213338415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 665464066165953617784553 499098049624465213338415)
        ·
          refine ⟨748647074436697820007623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499098049624465213338415 748647074436697820007623)
          ·
            refine ⟨1122970611655046730011435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748647074436697820007623 1122970611655046730011435)
            ·
              refine ⟨1684455917482570095017153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122970611655046730011435 1684455917482570095017153)
              ·
                refine ⟨1263341938111927571262865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1684455917482570095017153 1263341938111927571262865)
                ·
                  refine ⟨947506453583945678447149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1263341938111927571262865 947506453583945678447149)
                  ·
                    refine ⟨355314920093979629417681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 947506453583945678447149 355314920093979629417681)
                    ·
                      refine ⟨266486190070484722063261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 355314920093979629417681 266486190070484722063261)
                      ·
                        rfl

theorem cell23_518980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_518980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_518980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_518980 prefixEnd_518980 := by exact prefixLift 518980
  have htrace : WordTrace (prefixWord ++ tailWord_518980) baseStart_518980 baseEnd_518980 := by
    simpa [prefixWord, tailWord_518980, baseEnd_518980] using wordTrace_append hprefix tailTrace_518980
  have hstable : (prefixWord ++ tailWord_518980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518980).length < 2 ^ (prefixWord ++ tailWord_518980).sum := by decide
  have hdescent : baseEnd_518980 < baseStart_518980 := by decide
  rcases family_descends (prefixWord ++ tailWord_518980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519009 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 6, 1, 3]
def baseStart_519009 : Nat := 118140960795 + 519009 * 2 ^ 59
def prefixEnd_519009 : Nat := 4983230072969 + 3 ^ 40 * 519009 * 2
def baseEnd_519009 : Nat := 266501081009465108600627

theorem tailTrace_519009 : CollatzResearch.WordTrace tailWord_519009 prefixEnd_519009 266501081009465108600627 := by
  unfold tailWord_519009
  simp only [CollatzResearch.WordTrace]
  refine ⟨18929813376726507525344081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12619875584484338350229387 18929813376726507525344081)
  ·
    refine ⟨14197360032544880644008061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18929813376726507525344081 14197360032544880644008061)
    ·
      refine ⟨5324010012204330241503023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14197360032544880644008061 5324010012204330241503023)
      ·
        refine ⟨7986015018306495362254535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5324010012204330241503023 7986015018306495362254535)
        ·
          refine ⟨11979022527459743043381803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7986015018306495362254535 11979022527459743043381803)
          ·
            refine ⟨17968533791189614565072705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11979022527459743043381803 17968533791189614565072705)
            ·
              refine ⟨13476400343392210923804529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17968533791189614565072705 13476400343392210923804529)
              ·
                refine ⟨10107300257544158192853397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13476400343392210923804529 10107300257544158192853397)
                ·
                  refine ⟨473779699572382415290003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10107300257544158192853397 473779699572382415290003)
                  ·
                    refine ⟨710669549358573622935005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 473779699572382415290003 710669549358573622935005)
                    ·
                      refine ⟨266501081009465108600627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 710669549358573622935005 266501081009465108600627)
                      ·
                        rfl

theorem cell23_519009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_519009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519009 prefixEnd_519009 := by exact prefixLift 519009
  have htrace : WordTrace (prefixWord ++ tailWord_519009) baseStart_519009 baseEnd_519009 := by
    simpa [prefixWord, tailWord_519009, baseEnd_519009] using wordTrace_append hprefix tailTrace_519009
  have hstable : (prefixWord ++ tailWord_519009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519009).length < 2 ^ (prefixWord ++ tailWord_519009).sum := by decide
  have hdescent : baseEnd_519009 < baseStart_519009 := by decide
  rcases family_descends (prefixWord ++ tailWord_519009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519010 : List Nat := [3, 3, 2, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_519010 : Nat := 118140960795 + 519010 * 2 ^ 59
def prefixEnd_519010 : Nat := 4983230072969 + 3 ^ 40 * 519010 * 2
def baseEnd_519010 : Nat := 266501594490119604688123

theorem tailTrace_519010 : CollatzResearch.WordTrace tailWord_519010 prefixEnd_519010 266501594490119604688123 := by
  unfold tailWord_519010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4732462462430721174032621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12619899899815256464086989 4732462462430721174032621)
  ·
    refine ⟨1774673423411520440262233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4732462462430721174032621 1774673423411520440262233)
    ·
      refine ⟨1331005067558640330196675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1774673423411520440262233 1331005067558640330196675)
      ·
        refine ⟨1996507601337960495295013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1331005067558640330196675 1996507601337960495295013)
        ·
          refine ⟨374345175250867592867815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1996507601337960495295013 374345175250867592867815)
          ·
            refine ⟨561517762876301389301723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374345175250867592867815 561517762876301389301723)
            ·
              refine ⟨842276644314452083952585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561517762876301389301723 842276644314452083952585)
              ·
                refine ⟨631707483235839062964439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842276644314452083952585 631707483235839062964439)
                ·
                  refine ⟨947561224853758594446659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631707483235839062964439 947561224853758594446659)
                  ·
                    refine ⟨1421341837280637891669989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 947561224853758594446659 1421341837280637891669989)
                    ·
                      refine ⟨266501594490119604688123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1421341837280637891669989 266501594490119604688123)
                      ·
                        rfl

theorem cell23_519010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_519010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519010 prefixEnd_519010 := by exact prefixLift 519010
  have htrace : WordTrace (prefixWord ++ tailWord_519010) baseStart_519010 baseEnd_519010 := by
    simpa [prefixWord, tailWord_519010, baseEnd_519010] using wordTrace_append hprefix tailTrace_519010
  have hstable : (prefixWord ++ tailWord_519010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519010).length < 2 ^ (prefixWord ++ tailWord_519010).sum := by decide
  have hdescent : baseEnd_519010 < baseStart_519010 := by decide
  rcases family_descends (prefixWord ++ tailWord_519010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519030 : List Nat := [5, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3]
def baseStart_519030 : Nat := 118140960795 + 519030 * 2 ^ 59
def prefixEnd_519030 : Nat := 4983230072969 + 3 ^ 40 * 519030 * 2
def baseEnd_519030 : Nat := 266511864103209526438031

theorem tailTrace_519030 : CollatzResearch.WordTrace tailWord_519030 prefixEnd_519030 266511864103209526438031 := by
  unfold tailWord_519030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1183161206853151756991159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12620386206433618741239029 1183161206853151756991159)
  ·
    refine ⟨1774741810279727635486739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1183161206853151756991159 1774741810279727635486739)
    ·
      refine ⟨2662112715419591453230109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1774741810279727635486739 2662112715419591453230109)
      ·
        refine ⟨998292268282346794961291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2662112715419591453230109 998292268282346794961291)
        ·
          refine ⟨1497438402423520192441937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998292268282346794961291 1497438402423520192441937)
          ·
            refine ⟨1123078801817640144331453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1497438402423520192441937 1123078801817640144331453)
            ·
              refine ⟨421154550681615054124295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1123078801817640144331453 421154550681615054124295)
              ·
                refine ⟨631731826022422581186443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421154550681615054124295 631731826022422581186443)
                ·
                  refine ⟨947597739033633871779665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631731826022422581186443 947597739033633871779665)
                  ·
                    refine ⟨710698304275225403834749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 947597739033633871779665 710698304275225403834749)
                    ·
                      refine ⟨266511864103209526438031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 710698304275225403834749 266511864103209526438031)
                      ·
                        rfl

theorem cell23_519030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_519030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519030 prefixEnd_519030 := by exact prefixLift 519030
  have htrace : WordTrace (prefixWord ++ tailWord_519030) baseStart_519030 baseEnd_519030 := by
    simpa [prefixWord, tailWord_519030, baseEnd_519030] using wordTrace_append hprefix tailTrace_519030
  have hstable : (prefixWord ++ tailWord_519030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519030).length < 2 ^ (prefixWord ++ tailWord_519030).sum := by decide
  have hdescent : baseEnd_519030 < baseStart_519030 := by decide
  rcases family_descends (prefixWord ++ tailWord_519030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519036 : List Nat := [2, 2, 2, 1, 1, 1, 1, 7, 1, 3, 2]
def baseStart_519036 : Nat := 118140960795 + 519036 * 2 ^ 59
def prefixEnd_519036 : Nat := 4983230072969 + 3 ^ 40 * 519036 * 2
def baseEnd_519036 : Nat := 266514944987136502963003

theorem tailTrace_519036 : CollatzResearch.WordTrace tailWord_519036 prefixEnd_519036 266514944987136502963003 := by
  unfold tailWord_519036
  simp only [CollatzResearch.WordTrace]
  refine ⟨9465399073814345568288481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12620532098419127424384641 9465399073814345568288481)
  ·
    refine ⟨7099049305360759176216361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9465399073814345568288481 7099049305360759176216361)
    ·
      refine ⟨5324286979020569382162271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7099049305360759176216361 5324286979020569382162271)
      ·
        refine ⟨7986430468530854073243407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5324286979020569382162271 7986430468530854073243407)
        ·
          refine ⟨11979645702796281109865111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7986430468530854073243407 11979645702796281109865111)
          ·
            refine ⟨17969468554194421664797667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11979645702796281109865111 17969468554194421664797667)
            ·
              refine ⟨26954202831291632497196501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17969468554194421664797667 26954202831291632497196501)
              ·
                refine ⟨631739128858397636653043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26954202831291632497196501 631739128858397636653043)
                ·
                  refine ⟨947608693287596454979565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631739128858397636653043 947608693287596454979565)
                  ·
                    refine ⟨355353259982848670617337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 947608693287596454979565 355353259982848670617337)
                    ·
                      refine ⟨266514944987136502963003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 355353259982848670617337 266514944987136502963003)
                      ·
                        rfl

theorem cell23_519036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_519036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519036 prefixEnd_519036 := by exact prefixLift 519036
  have htrace : WordTrace (prefixWord ++ tailWord_519036) baseStart_519036 baseEnd_519036 := by
    simpa [prefixWord, tailWord_519036, baseEnd_519036] using wordTrace_append hprefix tailTrace_519036
  have hstable : (prefixWord ++ tailWord_519036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519036).length < 2 ^ (prefixWord ++ tailWord_519036).sum := by decide
  have hdescent : baseEnd_519036 < baseStart_519036 := by decide
  rcases family_descends (prefixWord ++ tailWord_519036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519052 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 1, 3, 5]
def baseStart_519052 : Nat := 118140960795 + 519052 * 2 ^ 59
def prefixEnd_519052 : Nat := 4983230072969 + 3 ^ 40 * 519052 * 2
def baseEnd_519052 : Nat := 266523160677608440362929

theorem tailTrace_519052 : CollatzResearch.WordTrace tailWord_519052 prefixEnd_519052 266523160677608440362929 := by
  unfold tailWord_519052
  simp only [CollatzResearch.WordTrace]
  refine ⟨9465690857785362934579705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12620921143713817246106273 9465690857785362934579705)
  ·
    refine ⟨7099268143339022200934779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9465690857785362934579705 7099268143339022200934779)
    ·
      refine ⟨10648902215008533301402169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7099268143339022200934779 10648902215008533301402169)
      ·
        refine ⟨7986676661256399976051627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10648902215008533301402169 7986676661256399976051627)
        ·
          refine ⟨11980014991884599964077441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7986676661256399976051627 11980014991884599964077441)
          ·
            refine ⟨8985011243913449973058081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11980014991884599964077441 8985011243913449973058081)
            ·
              refine ⟨6738758432935087479793561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8985011243913449973058081 6738758432935087479793561)
              ·
                refine ⟨5054068824701315609845171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6738758432935087479793561 5054068824701315609845171)
                ·
                  refine ⟨7581103237051973414767757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5054068824701315609845171 7581103237051973414767757)
                  ·
                    refine ⟨2842913713894490030537909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7581103237051973414767757 2842913713894490030537909)
                    ·
                      refine ⟨266523160677608440362929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2842913713894490030537909 266523160677608440362929)
                      ·
                        rfl

theorem cell23_519052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_519052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519052 prefixEnd_519052 := by exact prefixLift 519052
  have htrace : WordTrace (prefixWord ++ tailWord_519052) baseStart_519052 baseEnd_519052 := by
    simpa [prefixWord, tailWord_519052, baseEnd_519052] using wordTrace_append hprefix tailTrace_519052
  have hstable : (prefixWord ++ tailWord_519052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519052).length < 2 ^ (prefixWord ++ tailWord_519052).sum := by decide
  have hdescent : baseEnd_519052 < baseStart_519052 := by decide
  rcases family_descends (prefixWord ++ tailWord_519052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519069 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_519069 : Nat := 118140960795 + 519069 * 2 ^ 59
def prefixEnd_519069 : Nat := 4983230072969 + 3 ^ 40 * 519069 * 2
def baseEnd_519069 : Nat := 266531889848734873850351

theorem tailTrace_519069 : CollatzResearch.WordTrace tailWord_519069 prefixEnd_519069 266531889848734873850351 := by
  unfold tailWord_519069
  simp only [CollatzResearch.WordTrace]
  refine ⟨18932001756509137772528261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12621334504339425181685507 18932001756509137772528261)
  ·
    refine ⟨3549750329345463332349049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18932001756509137772528261 3549750329345463332349049)
    ·
      refine ⟨2662312747009097499261787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3549750329345463332349049 2662312747009097499261787)
      ·
        refine ⟨3993469120513646248892681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662312747009097499261787 3993469120513646248892681)
        ·
          refine ⟨2995101840385234686669511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3993469120513646248892681 2995101840385234686669511)
          ·
            refine ⟨4492652760577852030004267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2995101840385234686669511 4492652760577852030004267)
            ·
              refine ⟨6738979140866778045006401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4492652760577852030004267 6738979140866778045006401)
              ·
                refine ⟨5054234355650083533754801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6738979140866778045006401 5054234355650083533754801)
                ·
                  refine ⟨3790675766737562650316101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5054234355650083533754801 3790675766737562650316101)
                  ·
                    refine ⟨710751706263292996934269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3790675766737562650316101 710751706263292996934269)
                    ·
                      refine ⟨266531889848734873850351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 710751706263292996934269 266531889848734873850351)
                      ·
                        rfl

theorem cell23_519069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_519069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519069 prefixEnd_519069 := by exact prefixLift 519069
  have htrace : WordTrace (prefixWord ++ tailWord_519069) baseStart_519069 baseEnd_519069 := by
    simpa [prefixWord, tailWord_519069, baseEnd_519069] using wordTrace_append hprefix tailTrace_519069
  have hstable : (prefixWord ++ tailWord_519069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519069).length < 2 ^ (prefixWord ++ tailWord_519069).sum := by decide
  have hdescent : baseEnd_519069 < baseStart_519069 := by decide
  rcases family_descends (prefixWord ++ tailWord_519069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519072 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 9]
def baseStart_519072 : Nat := 118140960795 + 519072 * 2 ^ 59
def prefixEnd_519072 : Nat := 4983230072969 + 3 ^ 40 * 519072 * 2
def baseEnd_519072 : Nat := 29614825587855373568093

theorem tailTrace_519072 : CollatzResearch.WordTrace tailWord_519072 prefixEnd_519072 29614825587855373568093 := by
  unfold tailWord_519072
  simp only [CollatzResearch.WordTrace]
  refine ⟨9466055587749134642443735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12621407450332179523258313 9466055587749134642443735)
  ·
    refine ⟨14199083381623701963665603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9466055587749134642443735 14199083381623701963665603)
    ·
      refine ⟨21298625072435552945498405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14199083381623701963665603 21298625072435552945498405)
      ·
        refine ⟨3993492201081666177280951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21298625072435552945498405 3993492201081666177280951)
        ·
          refine ⟨5990238301622499265921427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3993492201081666177280951 5990238301622499265921427)
          ·
            refine ⟨8985357452433748898882141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5990238301622499265921427 8985357452433748898882141)
            ·
              refine ⟨3369509044662655837080803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8985357452433748898882141 3369509044662655837080803)
              ·
                refine ⟨5054263566993983755621205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3369509044662655837080803 5054263566993983755621205)
                ·
                  refine ⟨29614825587855373568093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5054263566993983755621205 29614825587855373568093)
                  ·
                    rfl

theorem cell23_519072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 9].length) (baseStart_519072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519072 prefixEnd_519072 := by exact prefixLift 519072
  have htrace : WordTrace (prefixWord ++ tailWord_519072) baseStart_519072 baseEnd_519072 := by
    simpa [prefixWord, tailWord_519072, baseEnd_519072] using wordTrace_append hprefix tailTrace_519072
  have hstable : (prefixWord ++ tailWord_519072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519072).length < 2 ^ (prefixWord ++ tailWord_519072).sum := by decide
  have hdescent : baseEnd_519072 < baseStart_519072 := by decide
  rcases family_descends (prefixWord ++ tailWord_519072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519139 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 4]
def baseStart_519139 : Nat := 118140960795 + 519139 * 2 ^ 59
def prefixEnd_519139 : Nat := 4983230072969 + 3 ^ 40 * 519139 * 2
def baseEnd_519139 : Nat := 266567833494549599975029

theorem tailTrace_519139 : CollatzResearch.WordTrace tailWord_519139 prefixEnd_519139 266567833494549599975029 := by
  unfold tailWord_519139
  simp only [CollatzResearch.WordTrace]
  refine ⟨18934554866255539727576471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12623036577503693151717647 18934554866255539727576471)
  ·
    refine ⟨28401832299383309591364707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18934554866255539727576471 28401832299383309591364707)
    ·
      refine ⟨42602748449074964387047061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28401832299383309591364707 42602748449074964387047061)
      ·
        refine ⟨1997003833550388955642831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42602748449074964387047061 1997003833550388955642831)
        ·
          refine ⟨2995505750325583433464247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1997003833550388955642831 2995505750325583433464247)
          ·
            refine ⟨4493258625488375150196371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2995505750325583433464247 4493258625488375150196371)
            ·
              refine ⟨6739887938232562725294557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4493258625488375150196371 6739887938232562725294557)
              ·
                refine ⟨2527457976837211021985459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6739887938232562725294557 2527457976837211021985459)
                ·
                  refine ⟨3791186965255816532978189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2527457976837211021985459 3791186965255816532978189)
                  ·
                    refine ⟨1421695111970931199866821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3791186965255816532978189 1421695111970931199866821)
                    ·
                      refine ⟨266567833494549599975029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1421695111970931199866821 266567833494549599975029)
                      ·
                        rfl

theorem cell23_519139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_519139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519139 prefixEnd_519139 := by exact prefixLift 519139
  have htrace : WordTrace (prefixWord ++ tailWord_519139) baseStart_519139 baseEnd_519139 := by
    simpa [prefixWord, tailWord_519139, baseEnd_519139] using wordTrace_append hprefix tailTrace_519139
  have hstable : (prefixWord ++ tailWord_519139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519139).length < 2 ^ (prefixWord ++ tailWord_519139).sum := by decide
  have hdescent : baseEnd_519139 < baseStart_519139 := by decide
  rcases family_descends (prefixWord ++ tailWord_519139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519157 : List Nat := [1, 3, 5, 2, 1, 1, 3, 2, 5]
def baseStart_519157 : Nat := 118140960795 + 519157 * 2 ^ 59
def prefixEnd_519157 : Nat := 4983230072969 + 3 ^ 40 * 519157 * 2
def baseEnd_519157 : Nat := 29619675127370058838883

theorem tailTrace_519157 : CollatzResearch.WordTrace tailWord_519157 prefixEnd_519157 29619675127370058838883 := by
  unfold tailWord_519157
  simp only [CollatzResearch.WordTrace]
  refine ⟨18935211380190328801731725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12623474253460219201154483 18935211380190328801731725)
  ·
    refine ⟨7100704267571373300649397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18935211380190328801731725 7100704267571373300649397)
    ·
      refine ⟨665691025084816246935881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7100704267571373300649397 665691025084816246935881)
      ·
        refine ⟨499268268813612185201911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 665691025084816246935881 499268268813612185201911)
        ·
          refine ⟨748902403220418277802867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499268268813612185201911 748902403220418277802867)
          ·
            refine ⟨1123353604830627416704301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748902403220418277802867 1123353604830627416704301)
            ·
              refine ⟨421257601811485281264113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1123353604830627416704301 421257601811485281264113)
              ·
                refine ⟨315943201358613960948085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421257601811485281264113 315943201358613960948085)
                ·
                  refine ⟨29619675127370058838883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 315943201358613960948085 29619675127370058838883)
                  ·
                    rfl

theorem cell23_519157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 5].length) (baseStart_519157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519157 prefixEnd_519157 := by exact prefixLift 519157
  have htrace : WordTrace (prefixWord ++ tailWord_519157) baseStart_519157 baseEnd_519157 := by
    simpa [prefixWord, tailWord_519157, baseEnd_519157] using wordTrace_append hprefix tailTrace_519157
  have hstable : (prefixWord ++ tailWord_519157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519157).length < 2 ^ (prefixWord ++ tailWord_519157).sum := by decide
  have hdescent : baseEnd_519157 < baseStart_519157 := by decide
  rcases family_descends (prefixWord ++ tailWord_519157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519246 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_519246 : Nat := 118140960795 + 519246 * 2 ^ 59
def prefixEnd_519246 : Nat := 4983230072969 + 3 ^ 40 * 519246 * 2
def baseEnd_519246 : Nat := 266622775924580681337037

theorem tailTrace_519246 : CollatzResearch.WordTrace tailWord_519246 prefixEnd_519246 266622775924580681337037 := by
  unfold tailWord_519246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2367307184608487125215199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12625638317911931334481061 2367307184608487125215199)
  ·
    refine ⟨3550960776912730687822799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2367307184608487125215199 3550960776912730687822799)
    ·
      refine ⟨5326441165369096031734199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3550960776912730687822799 5326441165369096031734199)
      ·
        refine ⟨7989661748053644047601299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5326441165369096031734199 7989661748053644047601299)
        ·
          refine ⟨11984492622080466071401949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7989661748053644047601299 11984492622080466071401949)
          ·
            refine ⟨4494184733280174776775731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11984492622080466071401949 4494184733280174776775731)
            ·
              refine ⟨6741277099920262165163597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4494184733280174776775731 6741277099920262165163597)
              ·
                refine ⟨2527978912470098311936349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6741277099920262165163597 2527978912470098311936349)
                ·
                  refine ⟨947992092176286866976131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2527978912470098311936349 947992092176286866976131)
                  ·
                    refine ⟨1421988138264430300464197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 947992092176286866976131 1421988138264430300464197)
                    ·
                      refine ⟨266622775924580681337037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1421988138264430300464197 266622775924580681337037)
                      ·
                        rfl

theorem cell23_519246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_519246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519246 prefixEnd_519246 := by exact prefixLift 519246
  have htrace : WordTrace (prefixWord ++ tailWord_519246) baseStart_519246 baseEnd_519246 := by
    simpa [prefixWord, tailWord_519246, baseEnd_519246] using wordTrace_append hprefix tailTrace_519246
  have hstable : (prefixWord ++ tailWord_519246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519246).length < 2 ^ (prefixWord ++ tailWord_519246).sum := by decide
  have hdescent : baseEnd_519246 < baseStart_519246 := by decide
  rcases family_descends (prefixWord ++ tailWord_519246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519250 : List Nat := [3, 2, 2, 1, 3, 1, 3, 1, 2, 3, 2]
def baseStart_519250 : Nat := 118140960795 + 519250 * 2 ^ 59
def prefixEnd_519250 : Nat := 4983230072969 + 3 ^ 40 * 519250 * 2
def baseEnd_519250 : Nat := 266624829847198665687019

theorem tailTrace_519250 : CollatzResearch.WordTrace tailWord_519250 prefixEnd_519250 266624829847198665687019 := by
  unfold tailWord_519250
  simp only [CollatzResearch.WordTrace]
  refine ⟨4734650842213351421216801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12625735579235603789911469 4734650842213351421216801)
  ·
    refine ⟨3550988131660013565912601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4734650842213351421216801 3550988131660013565912601)
    ·
      refine ⟨2663241098745010174434451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3550988131660013565912601 2663241098745010174434451)
      ·
        refine ⟨3994861648117515261651677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2663241098745010174434451 3994861648117515261651677)
        ·
          refine ⟨1498073118044068223119379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3994861648117515261651677 1498073118044068223119379)
          ·
            refine ⟨2247109677066102334679069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1498073118044068223119379 2247109677066102334679069)
            ·
              refine ⟨842666128899788375504651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2247109677066102334679069 842666128899788375504651)
              ·
                refine ⟨1263999193349682563256977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842666128899788375504651 1263999193349682563256977)
                ·
                  refine ⟨947999395012261922442733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1263999193349682563256977 947999395012261922442733)
                  ·
                    refine ⟨355499773129598220916025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 947999395012261922442733 355499773129598220916025)
                    ·
                      refine ⟨266624829847198665687019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 355499773129598220916025 266624829847198665687019)
                      ·
                        rfl

theorem cell23_519250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_519250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519250 prefixEnd_519250 := by exact prefixLift 519250
  have htrace : WordTrace (prefixWord ++ tailWord_519250) baseStart_519250 baseEnd_519250 := by
    simpa [prefixWord, tailWord_519250, baseEnd_519250] using wordTrace_append hprefix tailTrace_519250
  have hstable : (prefixWord ++ tailWord_519250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519250).length < 2 ^ (prefixWord ++ tailWord_519250).sum := by decide
  have hdescent : baseEnd_519250 < baseStart_519250 := by decide
  rcases family_descends (prefixWord ++ tailWord_519250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519256 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 4, 4]
def baseStart_519256 : Nat := 118140960795 + 519256 * 2 ^ 59
def prefixEnd_519256 : Nat := 4983230072969 + 3 ^ 40 * 519256 * 2
def baseEnd_519256 : Nat := 88875970243708547403997

theorem tailTrace_519256 : CollatzResearch.WordTrace tailWord_519256 prefixEnd_519256 88875970243708547403997 := by
  unfold tailWord_519256
  simp only [CollatzResearch.WordTrace]
  refine ⟨9469411103415834354792811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12625881471221112473057081 9469411103415834354792811)
  ·
    refine ⟨14204116655123751532189217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9469411103415834354792811 14204116655123751532189217)
    ·
      refine ⟨10653087491342813649141913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14204116655123751532189217 10653087491342813649141913)
      ·
        refine ⟨7989815618507110236856435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10653087491342813649141913 7989815618507110236856435)
        ·
          refine ⟨11984723427760665355284653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7989815618507110236856435 11984723427760665355284653)
          ·
            refine ⟨4494271285410249508231745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11984723427760665355284653 4494271285410249508231745)
            ·
              refine ⟨3370703464057687131173809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4494271285410249508231745 3370703464057687131173809)
              ·
                refine ⟨2528027598043265348380357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3370703464057687131173809 2528027598043265348380357)
                ·
                  refine ⟨474005174633112252821317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2528027598043265348380357 474005174633112252821317)
                  ·
                    refine ⟨88875970243708547403997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 474005174633112252821317 88875970243708547403997)
                    ·
                      rfl

theorem cell23_519256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_519256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519256 prefixEnd_519256 := by exact prefixLift 519256
  have htrace : WordTrace (prefixWord ++ tailWord_519256) baseStart_519256 baseEnd_519256 := by
    simpa [prefixWord, tailWord_519256, baseEnd_519256] using wordTrace_append hprefix tailTrace_519256
  have hstable : (prefixWord ++ tailWord_519256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519256).length < 2 ^ (prefixWord ++ tailWord_519256).sum := by decide
  have hdescent : baseEnd_519256 < baseStart_519256 := by decide
  rcases family_descends (prefixWord ++ tailWord_519256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519263 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 5, 2, 2]
def baseStart_519263 : Nat := 118140960795 + 519263 * 2 ^ 59
def prefixEnd_519263 : Nat := 4983230072969 + 3 ^ 40 * 519263 * 2
def baseEnd_519263 : Nat := 266631505095707114824459

theorem tailTrace_519263 : CollatzResearch.WordTrace tailWord_519263 prefixEnd_519263 266631505095707114824459 := by
  unfold tailWord_519263
  simp only [CollatzResearch.WordTrace]
  refine ⟨18939077517806308905090443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12626051678537539270060295 18939077517806308905090443)
  ·
    refine ⟨28408616276709463357635665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18939077517806308905090443 28408616276709463357635665)
    ·
      refine ⟨21306462207532097518226749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28408616276709463357635665 21306462207532097518226749)
      ·
        refine ⟨7989923327824536569335031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21306462207532097518226749 7989923327824536569335031)
        ·
          refine ⟨11984884991736804854002547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7989923327824536569335031 11984884991736804854002547)
          ·
            refine ⟨17977327487605207281003821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11984884991736804854002547 17977327487605207281003821)
            ·
              refine ⟨6741497807851952730376433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17977327487605207281003821 6741497807851952730376433)
              ·
                refine ⟨5056123355888964547782325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6741497807851952730376433 5056123355888964547782325)
                ·
                  refine ⟨474011564614590426354593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5056123355888964547782325 474011564614590426354593)
                  ·
                    refine ⟨355508673460942819765945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 474011564614590426354593 355508673460942819765945)
                    ·
                      refine ⟨266631505095707114824459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 355508673460942819765945 266631505095707114824459)
                      ·
                        rfl

theorem cell23_519263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_519263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519263 prefixEnd_519263 := by exact prefixLift 519263
  have htrace : WordTrace (prefixWord ++ tailWord_519263) baseStart_519263 baseEnd_519263 := by
    simpa [prefixWord, tailWord_519263, baseEnd_519263] using wordTrace_append hprefix tailTrace_519263
  have hstable : (prefixWord ++ tailWord_519263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519263).length < 2 ^ (prefixWord ++ tailWord_519263).sum := by decide
  have hdescent : baseEnd_519263 < baseStart_519263 := by decide
  rcases family_descends (prefixWord ++ tailWord_519263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519269 : List Nat := [1, 3, 1, 3, 2, 1, 12]
def baseStart_519269 : Nat := 118140960795 + 519269 * 2 ^ 59
def prefixEnd_519269 : Nat := 4983230072969 + 3 ^ 40 * 519269 * 2
def baseEnd_519269 : Nat := 3291785012094248041351

theorem tailTrace_519269 : CollatzResearch.WordTrace tailWord_519269 prefixEnd_519269 3291785012094248041351 := by
  unfold tailWord_519269
  simp only [CollatzResearch.WordTrace]
  refine ⟨18939296355784571929808861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12626197570523047953205907 18939296355784571929808861)
  ·
    refine ⟨7102236133419214473678323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18939296355784571929808861 7102236133419214473678323)
    ·
      refine ⟨10653354200128821710517485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7102236133419214473678323 10653354200128821710517485)
      ·
        refine ⟨3995007825048308141444057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10653354200128821710517485 3995007825048308141444057)
        ·
          refine ⟨2996255868786231106083043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3995007825048308141444057 2996255868786231106083043)
          ·
            refine ⟨4494383803179346659124565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2996255868786231106083043 4494383803179346659124565)
            ·
              refine ⟨3291785012094248041351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 4494383803179346659124565 3291785012094248041351)
              ·
                rfl

theorem cell23_519269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 12].length) (baseStart_519269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519269 prefixEnd_519269 := by exact prefixLift 519269
  have htrace : WordTrace (prefixWord ++ tailWord_519269) baseStart_519269 baseEnd_519269 := by
    simpa [prefixWord, tailWord_519269, baseEnd_519269] using wordTrace_append hprefix tailTrace_519269
  have hstable : (prefixWord ++ tailWord_519269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519269).length < 2 ^ (prefixWord ++ tailWord_519269).sum := by decide
  have hdescent : baseEnd_519269 < baseStart_519269 := by decide
  rcases family_descends (prefixWord ++ tailWord_519269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519273 : List Nat := [1, 2, 1, 1, 1, 6, 3, 2, 2, 4]
def baseStart_519273 : Nat := 118140960795 + 519273 * 2 ^ 59
def prefixEnd_519273 : Nat := 4983230072969 + 3 ^ 40 * 519273 * 2
def baseEnd_519273 : Nat := 88878879967417358566471

theorem tailTrace_519273 : CollatzResearch.WordTrace tailWord_519273 prefixEnd_519273 88878879967417358566471 := by
  unfold tailWord_519273
  simp only [CollatzResearch.WordTrace]
  refine ⟨18939442247770080612954473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12626294831846720408636315 18939442247770080612954473)
  ·
    refine ⟨14204581685827560459715855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18939442247770080612954473 14204581685827560459715855)
    ·
      refine ⟨21306872528741340689573783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14204581685827560459715855 21306872528741340689573783)
      ·
        refine ⟨31960308793112011034360675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21306872528741340689573783 31960308793112011034360675)
        ·
          refine ⟨47940463189668016551541013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31960308793112011034360675 47940463189668016551541013)
          ·
            refine ⟨2247209212015688275853485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47940463189668016551541013 2247209212015688275853485)
            ·
              refine ⟨842703454505883103445057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2247209212015688275853485 842703454505883103445057)
              ·
                refine ⟨632027590879412327583793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842703454505883103445057 632027590879412327583793)
                ·
                  refine ⟨474020693159559245687845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632027590879412327583793 474020693159559245687845)
                  ·
                    refine ⟨88878879967417358566471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 474020693159559245687845 88878879967417358566471)
                    ·
                      rfl

theorem cell23_519273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 4].length) (baseStart_519273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519273 prefixEnd_519273 := by exact prefixLift 519273
  have htrace : WordTrace (prefixWord ++ tailWord_519273) baseStart_519273 baseEnd_519273 := by
    simpa [prefixWord, tailWord_519273, baseEnd_519273] using wordTrace_append hprefix tailTrace_519273
  have hstable : (prefixWord ++ tailWord_519273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519273).length < 2 ^ (prefixWord ++ tailWord_519273).sum := by decide
  have hdescent : baseEnd_519273 < baseStart_519273 := by decide
  rcases family_descends (prefixWord ++ tailWord_519273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519280 : List Nat := [2, 1, 1, 1, 5, 1, 4, 1, 3, 2, 2]
def baseStart_519280 : Nat := 118140960795 + 519280 * 2 ^ 59
def prefixEnd_519280 : Nat := 4983230072969 + 3 ^ 40 * 519280 * 2
def baseEnd_519280 : Nat := 266640234266833548311881

theorem tailTrace_519280 : CollatzResearch.WordTrace tailWord_519280 prefixEnd_519280 266640234266833548311881 := by
  unfold tailWord_519280
  simp only [CollatzResearch.WordTrace]
  refine ⟨9469848779372360404229647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12626465039163147205639529 9469848779372360404229647)
  ·
    refine ⟨14204773169058540606344471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9469848779372360404229647 14204773169058540606344471)
    ·
      refine ⟨21307159753587810909516707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14204773169058540606344471 21307159753587810909516707)
      ·
        refine ⟨31960739630381716364275061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21307159753587810909516707 31960739630381716364275061)
        ·
          refine ⟨2996319340348285909150787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31960739630381716364275061 2996319340348285909150787)
          ·
            refine ⟨4494479010522428863726181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2996319340348285909150787 4494479010522428863726181)
            ·
              refine ⟨842714814472955411948659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4494479010522428863726181 842714814472955411948659)
              ·
                refine ⟨1264072221709433117922989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842714814472955411948659 1264072221709433117922989)
                ·
                  refine ⟨474027083141037419221121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1264072221709433117922989 474027083141037419221121)
                  ·
                    refine ⟨355520312355778064415841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 474027083141037419221121 355520312355778064415841)
                    ·
                      refine ⟨266640234266833548311881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 355520312355778064415841 266640234266833548311881)
                      ·
                        rfl

theorem cell23_519280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 3, 2, 2].length) (baseStart_519280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519280 prefixEnd_519280 := by exact prefixLift 519280
  have htrace : WordTrace (prefixWord ++ tailWord_519280) baseStart_519280 baseEnd_519280 := by
    simpa [prefixWord, tailWord_519280, baseEnd_519280] using wordTrace_append hprefix tailTrace_519280
  have hstable : (prefixWord ++ tailWord_519280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519280).length < 2 ^ (prefixWord ++ tailWord_519280).sum := by decide
  have hdescent : baseEnd_519280 < baseStart_519280 := by decide
  rcases family_descends (prefixWord ++ tailWord_519280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519286 : List Nat := [5, 1, 1, 2, 1, 1, 2, 10]
def baseStart_519286 : Nat := 118140960795 + 519286 * 2 ^ 59
def prefixEnd_519286 : Nat := 4983230072969 + 3 ^ 40 * 519286 * 2
def baseEnd_519286 : Nat := 9875678338917056475439

theorem tailTrace_519286 : CollatzResearch.WordTrace tailWord_519286 prefixEnd_519286 9875678338917056475439 := by
  unfold tailWord_519286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1183744774795186489573607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12626610931148655888785141 1183744774795186489573607)
  ·
    refine ⟨1775617162192779734360411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1183744774795186489573607 1775617162192779734360411)
    ·
      refine ⟨2663425743289169601540617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1775617162192779734360411 2663425743289169601540617)
      ·
        refine ⟨1997569307466877201155463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2663425743289169601540617 1997569307466877201155463)
        ·
          refine ⟨2996353961200315801733195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1997569307466877201155463 2996353961200315801733195)
          ·
            refine ⟨4494530941800473702599793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2996353961200315801733195 4494530941800473702599793)
            ·
              refine ⟨3370898206350355276949845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4494530941800473702599793 3370898206350355276949845)
              ·
                refine ⟨9875678338917056475439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3370898206350355276949845 9875678338917056475439)
                ·
                  rfl

theorem cell23_519286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_519286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519286 prefixEnd_519286 := by exact prefixLift 519286
  have htrace : WordTrace (prefixWord ++ tailWord_519286) baseStart_519286 baseEnd_519286 := by
    simpa [prefixWord, tailWord_519286, baseEnd_519286] using wordTrace_append hprefix tailTrace_519286
  have hstable : (prefixWord ++ tailWord_519286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519286).length < 2 ^ (prefixWord ++ tailWord_519286).sum := by decide
  have hdescent : baseEnd_519286 < baseStart_519286 := by decide
  rcases family_descends (prefixWord ++ tailWord_519286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519294 : List Nat := [4, 2, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_519294 : Nat := 118140960795 + 519294 * 2 ^ 59
def prefixEnd_519294 : Nat := 4983230072969 + 3 ^ 40 * 519294 * 2
def baseEnd_519294 : Nat := 88882474331998831178939

theorem tailTrace_519294 : CollatzResearch.WordTrace tailWord_519294 prefixEnd_519294 88882474331998831178939 := by
  unfold tailWord_519294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2367526022586750149933617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12626805453796000799645957 2367526022586750149933617)
  ·
    refine ⟨1775644516940062612450213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2367526022586750149933617 1775644516940062612450213)
    ·
      refine ⟨332933346926261739834415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1775644516940062612450213 332933346926261739834415)
      ·
        refine ⟨499400020389392609751623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332933346926261739834415 499400020389392609751623)
        ·
          refine ⟨749100030584088914627435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499400020389392609751623 749100030584088914627435)
          ·
            refine ⟨1123650045876133371941153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749100030584088914627435 1123650045876133371941153)
            ·
              refine ⟨842737534407100028955865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123650045876133371941153 842737534407100028955865)
              ·
                refine ⟨632053150805325021716899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842737534407100028955865 632053150805325021716899)
                ·
                  refine ⟨948079726207987532575349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632053150805325021716899 948079726207987532575349)
                  ·
                    refine ⟨88882474331998831178939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 948079726207987532575349 88882474331998831178939)
                    ·
                      rfl

theorem cell23_519294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_519294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519294 prefixEnd_519294 := by exact prefixLift 519294
  have htrace : WordTrace (prefixWord ++ tailWord_519294) baseStart_519294 baseEnd_519294 := by
    simpa [prefixWord, tailWord_519294, baseEnd_519294] using wordTrace_append hprefix tailTrace_519294
  have hstable : (prefixWord ++ tailWord_519294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519294).length < 2 ^ (prefixWord ++ tailWord_519294).sum := by decide
  have hdescent : baseEnd_519294 < baseStart_519294 := by decide
  rcases family_descends (prefixWord ++ tailWord_519294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519300 : List Nat := [2, 3, 2, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_519300 : Nat := 118140960795 + 519300 * 2 ^ 59
def prefixEnd_519300 : Nat := 4983230072969 + 3 ^ 40 * 519300 * 2
def baseEnd_519300 : Nat := 266650503879923470061789

theorem tailTrace_519300 : CollatzResearch.WordTrace tailWord_519300 prefixEnd_519300 266650503879923470061789 := by
  unfold tailWord_519300
  simp only [CollatzResearch.WordTrace]
  refine ⟨9470213509336132112093677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12626951345781509482791569 9470213509336132112093677)
  ·
    refine ⟨3551330066001049542035129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9470213509336132112093677 3551330066001049542035129)
    ·
      refine ⟨2663497549500787156526347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3551330066001049542035129 2663497549500787156526347)
      ·
        refine ⟨3995246324251180734789521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2663497549500787156526347 3995246324251180734789521)
        ·
          refine ⟨2996434743188385551092141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3995246324251180734789521 2996434743188385551092141)
          ·
            refine ⟨1123663028695644581659553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2996434743188385551092141 1123663028695644581659553)
            ·
              refine ⟨842747271521733436244665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123663028695644581659553 842747271521733436244665)
              ·
                refine ⟨632060453641300077183499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842747271521733436244665 632060453641300077183499)
                ·
                  refine ⟨948090680461950115775249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632060453641300077183499 948090680461950115775249)
                  ·
                    refine ⟨711068010346462586831437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 948090680461950115775249 711068010346462586831437)
                    ·
                      refine ⟨266650503879923470061789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 711068010346462586831437 266650503879923470061789)
                      ·
                        rfl

theorem cell23_519300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_519300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519300 prefixEnd_519300 := by exact prefixLift 519300
  have htrace : WordTrace (prefixWord ++ tailWord_519300) baseStart_519300 baseEnd_519300 := by
    simpa [prefixWord, tailWord_519300, baseEnd_519300] using wordTrace_append hprefix tailTrace_519300
  have hstable : (prefixWord ++ tailWord_519300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519300).length < 2 ^ (prefixWord ++ tailWord_519300).sum := by decide
  have hdescent : baseEnd_519300 < baseStart_519300 := by decide
  rcases family_descends (prefixWord ++ tailWord_519300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519314 : List Nat := [3, 2, 3, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_519314 : Nat := 118140960795 + 519314 * 2 ^ 59
def prefixEnd_519314 : Nat := 4983230072969 + 3 ^ 40 * 519314 * 2
def baseEnd_519314 : Nat := 266657692609086415286725

theorem tailTrace_519314 : CollatzResearch.WordTrace tailWord_519314 prefixEnd_519314 266657692609086415286725 := by
  unfold tailWord_519314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4735234410155386153799249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12627291760414363076797997 4735234410155386153799249)
  ·
    refine ⟨3551425807616539615349437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4735234410155386153799249 3551425807616539615349437)
    ·
      refine ⟨1331784677856202355756039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3551425807616539615349437 1331784677856202355756039)
      ·
        refine ⟨1997677016784303533634059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1331784677856202355756039 1997677016784303533634059)
        ·
          refine ⟨2996515525176455300451089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1997677016784303533634059 2996515525176455300451089)
          ·
            refine ⟨2247386643882341475338317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2996515525176455300451089 2247386643882341475338317)
            ·
              refine ⟨842769991455878053251869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2247386643882341475338317 842769991455878053251869)
              ·
                refine ⟨316038746795954269969451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 842769991455878053251869 316038746795954269969451)
                ·
                  refine ⟨474058120193931404954177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316038746795954269969451 474058120193931404954177)
                  ·
                    refine ⟨355543590145448553715633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 474058120193931404954177 355543590145448553715633)
                    ·
                      refine ⟨266657692609086415286725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 355543590145448553715633 266657692609086415286725)
                      ·
                        rfl

theorem cell23_519314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_519314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519314 prefixEnd_519314 := by exact prefixLift 519314
  have htrace : WordTrace (prefixWord ++ tailWord_519314) baseStart_519314 baseEnd_519314 := by
    simpa [prefixWord, tailWord_519314, baseEnd_519314] using wordTrace_append hprefix tailTrace_519314
  have hstable : (prefixWord ++ tailWord_519314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519314).length < 2 ^ (prefixWord ++ tailWord_519314).sum := by decide
  have hdescent : baseEnd_519314 < baseStart_519314 := by decide
  rcases family_descends (prefixWord ++ tailWord_519314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519370 : List Nat := [3, 1, 2, 1, 3, 3, 1, 2, 1, 4, 2]
def baseStart_519370 : Nat := 118140960795 + 519370 * 2 ^ 59
def prefixEnd_519370 : Nat := 4983230072969 + 3 ^ 40 * 519370 * 2
def baseEnd_519370 : Nat := 266686447525738196186467

theorem tailTrace_519370 : CollatzResearch.WordTrace tailWord_519370 prefixEnd_519370 266686447525738196186467 := by
  unfold tailWord_519370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4735745032104666544808891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12628653418945777452823709 4735745032104666544808891)
  ·
    refine ⟨7103617548156999817213337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4735745032104666544808891 7103617548156999817213337)
    ·
      refine ⟨5327713161117749862910003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7103617548156999817213337 5327713161117749862910003)
      ·
        refine ⟨7991569741676624794365005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5327713161117749862910003 7991569741676624794365005)
        ·
          refine ⟨2996838653128734297886877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7991569741676624794365005 2996838653128734297886877)
          ·
            refine ⟨1123814494923275361707579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2996838653128734297886877 1123814494923275361707579)
            ·
              refine ⟨1685721742384913042561369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123814494923275361707579 1685721742384913042561369)
              ·
                refine ⟨1264291306788684781921027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1685721742384913042561369 1264291306788684781921027)
                ·
                  refine ⟨1896436960183027172881541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1264291306788684781921027 1896436960183027172881541)
                  ·
                    refine ⟨355581930034317594915289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1896436960183027172881541 355581930034317594915289)
                    ·
                      refine ⟨266686447525738196186467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 355581930034317594915289 266686447525738196186467)
                      ·
                        rfl

theorem cell23_519370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_519370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519370 prefixEnd_519370 := by exact prefixLift 519370
  have htrace : WordTrace (prefixWord ++ tailWord_519370) baseStart_519370 baseEnd_519370 := by
    simpa [prefixWord, tailWord_519370, baseEnd_519370] using wordTrace_append hprefix tailTrace_519370
  have hstable : (prefixWord ++ tailWord_519370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519370).length < 2 ^ (prefixWord ++ tailWord_519370).sum := by decide
  have hdescent : baseEnd_519370 < baseStart_519370 := by decide
  rcases family_descends (prefixWord ++ tailWord_519370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519374 : List Nat := [4, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2]
def baseStart_519374 : Nat := 118140960795 + 519374 * 2 ^ 59
def prefixEnd_519374 : Nat := 4983230072969 + 3 ^ 40 * 519374 * 2
def baseEnd_519374 : Nat := 266688501448356180536449

theorem tailTrace_519374 : CollatzResearch.WordTrace tailWord_519374 prefixEnd_519374 266688501448356180536449 := by
  unfold tailWord_519374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2367890752550521857797647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12628750680269449908254117 2367890752550521857797647)
  ·
    refine ⟨3551836128825782786696471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2367890752550521857797647 3551836128825782786696471)
    ·
      refine ⟨5327754193238674180044707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3551836128825782786696471 5327754193238674180044707)
      ·
        refine ⟨7991631289858011270067061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5327754193238674180044707 7991631289858011270067061)
        ·
          refine ⟨749215433424188556568787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7991631289858011270067061 749215433424188556568787)
          ·
            refine ⟨1123823150136282834853181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749215433424188556568787 1123823150136282834853181)
            ·
              refine ⟨421433681301106063069943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1123823150136282834853181 421433681301106063069943)
              ·
                refine ⟨632150521951659094604915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421433681301106063069943 632150521951659094604915)
                ·
                  refine ⟨948225782927488641907373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632150521951659094604915 948225782927488641907373)
                  ·
                    refine ⟨355584668597808240715265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 948225782927488641907373 355584668597808240715265)
                    ·
                      refine ⟨266688501448356180536449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 355584668597808240715265 266688501448356180536449)
                      ·
                        rfl

theorem cell23_519374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_519374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519374 prefixEnd_519374 := by exact prefixLift 519374
  have htrace : WordTrace (prefixWord ++ tailWord_519374) baseStart_519374 baseEnd_519374 := by
    simpa [prefixWord, tailWord_519374, baseEnd_519374] using wordTrace_append hprefix tailTrace_519374
  have hstable : (prefixWord ++ tailWord_519374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519374).length < 2 ^ (prefixWord ++ tailWord_519374).sum := by decide
  have hdescent : baseEnd_519374 < baseStart_519374 := by decide
  rcases family_descends (prefixWord ++ tailWord_519374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519403 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 3]
def baseStart_519403 : Nat := 118140960795 + 519403 * 2 ^ 59
def prefixEnd_519403 : Nat := 4983230072969 + 3 ^ 40 * 519403 * 2
def baseEnd_519403 : Nat := 266703392387336567073815

theorem tailTrace_519403 : CollatzResearch.WordTrace tailWord_519403 prefixEnd_519403 266703392387336567073815 := by
  unfold tailWord_519403
  simp only [CollatzResearch.WordTrace]
  refine ⟨18944183737299112815186863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12629455824866075210124575 18944183737299112815186863)
  ·
    refine ⟨28416275605948669222780295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18944183737299112815186863 28416275605948669222780295)
    ·
      refine ⟨42624413408923003834170443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28416275605948669222780295 42624413408923003834170443)
      ·
        refine ⟨63936620113384505751255665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42624413408923003834170443 63936620113384505751255665)
        ·
          refine ⟨47952465085038379313441749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63936620113384505751255665 47952465085038379313441749)
          ·
            refine ⟨1123885900430587015158791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 47952465085038379313441749 1123885900430587015158791)
            ·
              refine ⟨1685828850645880522738187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123885900430587015158791 1685828850645880522738187)
              ·
                refine ⟨2528743275968820784107281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1685828850645880522738187 2528743275968820784107281)
                ·
                  refine ⟨1896557456976615588080461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2528743275968820784107281 1896557456976615588080461)
                  ·
                    refine ⟨711209046366230845530173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1896557456976615588080461 711209046366230845530173)
                    ·
                      refine ⟨266703392387336567073815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 711209046366230845530173 266703392387336567073815)
                      ·
                        rfl

theorem cell23_519403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 3].length) (baseStart_519403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519403 prefixEnd_519403 := by exact prefixLift 519403
  have htrace : WordTrace (prefixWord ++ tailWord_519403) baseStart_519403 baseEnd_519403 := by
    simpa [prefixWord, tailWord_519403, baseEnd_519403] using wordTrace_append hprefix tailTrace_519403
  have hstable : (prefixWord ++ tailWord_519403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519403).length < 2 ^ (prefixWord ++ tailWord_519403).sum := by decide
  have hdescent : baseEnd_519403 < baseStart_519403 := by decide
  rcases family_descends (prefixWord ++ tailWord_519403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519423 : List Nat := [1, 1, 2, 2, 1, 5, 3, 1, 2, 5]
def baseStart_519423 : Nat := 118140960795 + 519423 * 2 ^ 59
def prefixEnd_519423 : Nat := 4983230072969 + 3 ^ 40 * 519423 * 2
def baseEnd_519423 : Nat := 88904554000142162941241

theorem tailTrace_519423 : CollatzResearch.WordTrace tailWord_519423 prefixEnd_519423 88904554000142162941241 := by
  unfold tailWord_519423
  simp only [CollatzResearch.WordTrace]
  refine ⟨18944913197226656230914923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12629942131484437487276615 18944913197226656230914923)
  ·
    refine ⟨28417369795839984346372385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18944913197226656230914923 28417369795839984346372385)
    ·
      refine ⟨21313027346879988259779289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28417369795839984346372385 21313027346879988259779289)
      ·
        refine ⟨15984770510159991194834467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21313027346879988259779289 15984770510159991194834467)
        ·
          refine ⟨23977155765239986792251701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15984770510159991194834467 23977155765239986792251701)
          ·
            refine ⟨2247858352991248761773597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23977155765239986792251701 2247858352991248761773597)
            ·
              refine ⟨842946882371718285665099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2247858352991248761773597 842946882371718285665099)
              ·
                refine ⟨1264420323557577428497649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842946882371718285665099 1264420323557577428497649)
                ·
                  refine ⟨948315242668183071373237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1264420323557577428497649 948315242668183071373237)
                  ·
                    refine ⟨88904554000142162941241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 948315242668183071373237 88904554000142162941241)
                    ·
                      rfl

theorem cell23_519423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 5].length) (baseStart_519423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519423 prefixEnd_519423 := by exact prefixLift 519423
  have htrace : WordTrace (prefixWord ++ tailWord_519423) baseStart_519423 baseEnd_519423 := by
    simpa [prefixWord, tailWord_519423, baseEnd_519423] using wordTrace_append hprefix tailTrace_519423
  have hstable : (prefixWord ++ tailWord_519423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519423).length < 2 ^ (prefixWord ++ tailWord_519423).sum := by decide
  have hdescent : baseEnd_519423 < baseStart_519423 := by decide
  rcases family_descends (prefixWord ++ tailWord_519423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519460 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 2, 4, 2]
def baseStart_519460 : Nat := 118140960795 + 519460 * 2 ^ 59
def prefixEnd_519460 : Nat := 4983230072969 + 3 ^ 40 * 519460 * 2
def baseEnd_519460 : Nat := 266732660784642844061053

theorem tailTrace_519460 : CollatzResearch.WordTrace tailWord_519460 prefixEnd_519460 266732660784642844061053 := by
  unfold tailWord_519460
  simp only [CollatzResearch.WordTrace]
  refine ⟨9473131349046305775005917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12630841798728407700007889 9473131349046305775005917)
  ·
    refine ⟨3552424255892364665627219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9473131349046305775005917 3552424255892364665627219)
    ·
      refine ⟨5328636383838546998440829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3552424255892364665627219 5328636383838546998440829)
      ·
        refine ⟨1998238643939455124415311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5328636383838546998440829 1998238643939455124415311)
        ·
          refine ⟨2997357965909182686622967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1998238643939455124415311 2997357965909182686622967)
          ·
            refine ⟨4496036948863774029934451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2997357965909182686622967 4496036948863774029934451)
            ·
              refine ⟨6744055423295661044901677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4496036948863774029934451 6744055423295661044901677)
              ·
                refine ⟨2529020783735872891838129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6744055423295661044901677 2529020783735872891838129)
                ·
                  refine ⟨1896765587801904668878597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2529020783735872891838129 1896765587801904668878597)
                  ·
                    refine ⟨355643547712857125414737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1896765587801904668878597 355643547712857125414737)
                    ·
                      refine ⟨266732660784642844061053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 355643547712857125414737 266732660784642844061053)
                      ·
                        rfl

theorem cell23_519460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_519460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519460 prefixEnd_519460 := by exact prefixLift 519460
  have htrace : WordTrace (prefixWord ++ tailWord_519460) baseStart_519460 baseEnd_519460 := by
    simpa [prefixWord, tailWord_519460, baseEnd_519460] using wordTrace_append hprefix tailTrace_519460
  have hstable : (prefixWord ++ tailWord_519460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519460).length < 2 ^ (prefixWord ++ tailWord_519460).sum := by decide
  have hdescent : baseEnd_519460 < baseStart_519460 := by decide
  rcases family_descends (prefixWord ++ tailWord_519460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519487 : List Nat := [1, 1, 2, 2, 4, 2, 3, 3, 1, 4]
def baseStart_519487 : Nat := 118140960795 + 519487 * 2 ^ 59
def prefixEnd_519487 : Nat := 4983230072969 + 3 ^ 40 * 519487 * 2
def baseEnd_519487 : Nat := 88915508254104746141143

theorem tailTrace_519487 : CollatzResearch.WordTrace tailWord_519487 prefixEnd_519487 88915508254104746141143 := by
  unfold tailWord_519487
  simp only [CollatzResearch.WordTrace]
  refine ⟨18947247468994795161244715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12631498312663196774163143 18947247468994795161244715)
  ·
    refine ⟨28420871203492192741867073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18947247468994795161244715 28420871203492192741867073)
    ·
      refine ⟨21315653402619144556400305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28420871203492192741867073 21315653402619144556400305)
      ·
        refine ⟨15986740051964358417300229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21315653402619144556400305 15986740051964358417300229)
        ·
          refine ⟨2997513759743317203243793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15986740051964358417300229 2997513759743317203243793)
          ·
            refine ⟨2248135319807487902432845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2997513759743317203243793 2248135319807487902432845)
            ·
              refine ⟨843050744927807963412317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2248135319807487902432845 843050744927807963412317)
              ·
                refine ⟨316144029347927986279619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 843050744927807963412317 316144029347927986279619)
                ·
                  refine ⟨474216044021891979419429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316144029347927986279619 474216044021891979419429)
                  ·
                    refine ⟨88915508254104746141143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 474216044021891979419429 88915508254104746141143)
                    ·
                      rfl

theorem cell23_519487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 1, 4].length) (baseStart_519487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519487 prefixEnd_519487 := by exact prefixLift 519487
  have htrace : WordTrace (prefixWord ++ tailWord_519487) baseStart_519487 baseEnd_519487 := by
    simpa [prefixWord, tailWord_519487, baseEnd_519487] using wordTrace_append hprefix tailTrace_519487
  have hstable : (prefixWord ++ tailWord_519487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519487).length < 2 ^ (prefixWord ++ tailWord_519487).sum := by decide
  have hdescent : baseEnd_519487 < baseStart_519487 := by decide
  rcases family_descends (prefixWord ++ tailWord_519487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519543 : List Nat := [1, 1, 3, 1, 1, 2, 5, 2, 1, 6]
def baseStart_519543 : Nat := 118140960795 + 519543 * 2 ^ 59
def prefixEnd_519543 : Nat := 4983230072969 + 3 ^ 40 * 519543 * 2
def baseEnd_519543 : Nat := 88925093226322006441057

theorem tailTrace_519543 : CollatzResearch.WordTrace tailWord_519543 prefixEnd_519543 88925093226322006441057 := by
  unfold tailWord_519543
  simp only [CollatzResearch.WordTrace]
  refine ⟨18949289956791916725283283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12632859971194611150188855 18949289956791916725283283)
  ·
    refine ⟨28423934935187875087924925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18949289956791916725283283 28423934935187875087924925)
    ·
      refine ⟨10658975600695453157971847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28423934935187875087924925 10658975600695453157971847)
      ·
        refine ⟨15988463401043179736957771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10658975600695453157971847 15988463401043179736957771)
        ·
          refine ⟨23982695101564769605436657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15988463401043179736957771 23982695101564769605436657)
          ·
            refine ⟨17987021326173577204077493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23982695101564769605436657 17987021326173577204077493)
            ·
              refine ⟨1686283249328772862882265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17987021326173577204077493 1686283249328772862882265)
              ·
                refine ⟨1264712436996579647161699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1686283249328772862882265 1264712436996579647161699)
                ·
                  refine ⟨1897068655494869470742549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1264712436996579647161699 1897068655494869470742549)
                  ·
                    refine ⟨88925093226322006441057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1897068655494869470742549 88925093226322006441057)
                    ·
                      rfl

theorem cell23_519543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_519543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519543 prefixEnd_519543 := by exact prefixLift 519543
  have htrace : WordTrace (prefixWord ++ tailWord_519543) baseStart_519543 baseEnd_519543 := by
    simpa [prefixWord, tailWord_519543, baseEnd_519543] using wordTrace_append hprefix tailTrace_519543
  have hstable : (prefixWord ++ tailWord_519543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519543).length < 2 ^ (prefixWord ++ tailWord_519543).sum := by decide
  have hdescent : baseEnd_519543 < baseStart_519543 := by decide
  rcases family_descends (prefixWord ++ tailWord_519543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519563 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 4]
def baseStart_519563 : Nat := 118140960795 + 519563 * 2 ^ 59
def prefixEnd_519563 : Nat := 4983230072969 + 3 ^ 40 * 519563 * 2
def baseEnd_519563 : Nat := 266785549292055941073079

theorem tailTrace_519563 : CollatzResearch.WordTrace tailWord_519563 prefixEnd_519563 266785549292055941073079 := by
  unfold tailWord_519563
  simp only [CollatzResearch.WordTrace]
  refine ⟨18950019416719460141011343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12633346277812973427340895 18950019416719460141011343)
  ·
    refine ⟨28425029125079190211517015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18950019416719460141011343 28425029125079190211517015)
    ·
      refine ⟨42637543687618785317275523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28425029125079190211517015 42637543687618785317275523)
      ·
        refine ⟨63956315531428177975913285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42637543687618785317275523 63956315531428177975913285)
        ·
          refine ⟨11991809162142783370483741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63956315531428177975913285 11991809162142783370483741)
          ·
            refine ⟨4496928435803543763931403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11991809162142783370483741 4496928435803543763931403)
            ·
              refine ⟨6745392653705315645897105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4496928435803543763931403 6745392653705315645897105)
              ·
                refine ⟨5059044490278986734422829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6745392653705315645897105 5059044490278986734422829)
                ·
                  refine ⟨1897141683854620025408561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5059044490278986734422829 1897141683854620025408561)
                  ·
                    refine ⟨1422856262890965019056421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1897141683854620025408561 1422856262890965019056421)
                    ·
                      refine ⟨266785549292055941073079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1422856262890965019056421 266785549292055941073079)
                      ·
                        rfl

theorem cell23_519563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 4].length) (baseStart_519563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519563 prefixEnd_519563 := by exact prefixLift 519563
  have htrace : WordTrace (prefixWord ++ tailWord_519563) baseStart_519563 baseEnd_519563 := by
    simpa [prefixWord, tailWord_519563, baseEnd_519563] using wordTrace_append hprefix tailTrace_519563
  have hstable : (prefixWord ++ tailWord_519563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519563).length < 2 ^ (prefixWord ++ tailWord_519563).sum := by decide
  have hdescent : baseEnd_519563 < baseStart_519563 := by decide
  rcases family_descends (prefixWord ++ tailWord_519563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519573 : List Nat := [1, 3, 2, 1, 1, 2, 5, 8]
def baseStart_519573 : Nat := 118140960795 + 519573 * 2 ^ 59
def prefixEnd_519573 : Nat := 4983230072969 + 3 ^ 40 * 519573 * 2
def baseEnd_519573 : Nat := 9881136448096329701779

theorem tailTrace_519573 : CollatzResearch.WordTrace tailWord_519573 prefixEnd_519573 9881136448096329701779 := by
  unfold tailWord_519573
  simp only [CollatzResearch.WordTrace]
  refine ⟨18950384146683231848875373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12633589431122154565916915 18950384146683231848875373)
  ·
    refine ⟨7106394055006211943328265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18950384146683231848875373 7106394055006211943328265)
    ·
      refine ⟨5329795541254658957496199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7106394055006211943328265 5329795541254658957496199)
      ·
        refine ⟨7994693311881988436244299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5329795541254658957496199 7994693311881988436244299)
        ·
          refine ⟨11992039967822982654366449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7994693311881988436244299 11992039967822982654366449)
          ·
            refine ⟨8994029975867236990774837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11992039967822982654366449 8994029975867236990774837)
            ·
              refine ⟨843190310237553467885141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8994029975867236990774837 843190310237553467885141)
              ·
                refine ⟨9881136448096329701779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 843190310237553467885141 9881136448096329701779)
                ·
                  rfl

theorem cell23_519573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 8].length) (baseStart_519573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519573 prefixEnd_519573 := by exact prefixLift 519573
  have htrace : WordTrace (prefixWord ++ tailWord_519573) baseStart_519573 baseEnd_519573 := by
    simpa [prefixWord, tailWord_519573, baseEnd_519573] using wordTrace_append hprefix tailTrace_519573
  have hstable : (prefixWord ++ tailWord_519573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519573).length < 2 ^ (prefixWord ++ tailWord_519573).sum := by decide
  have hdescent : baseEnd_519573 < baseStart_519573 := by decide
  rcases family_descends (prefixWord ++ tailWord_519573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519597 : List Nat := [1, 5, 2, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_519597 : Nat := 118140960795 + 519597 * 2 ^ 59
def prefixEnd_519597 : Nat := 4983230072969 + 3 ^ 40 * 519597 * 2
def baseEnd_519597 : Nat := 266803007634308808047923

theorem tailTrace_519597 : CollatzResearch.WordTrace tailWord_519597 prefixEnd_519597 266803007634308808047923 := by
  unfold tailWord_519597
  simp only [CollatzResearch.WordTrace]
  refine ⟨18951259498596283947749045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12634172999064189298499363 18951259498596283947749045)
  ·
    refine ⟨1776680577993401620101473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18951259498596283947749045 1776680577993401620101473)
    ·
      refine ⟨1332510433495051215076105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1776680577993401620101473 1332510433495051215076105)
      ·
        refine ⟨999382825121288411307079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1332510433495051215076105 999382825121288411307079)
        ·
          refine ⟨1499074237681932616960619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999382825121288411307079 1499074237681932616960619)
          ·
            refine ⟨2248611356522898925440929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499074237681932616960619 2248611356522898925440929)
            ·
              refine ⟨1686458517392174194080697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2248611356522898925440929 1686458517392174194080697)
              ·
                refine ⟨1264843888044130645560523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1686458517392174194080697 1264843888044130645560523)
                ·
                  refine ⟨1897265832066195968340785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1264843888044130645560523 1897265832066195968340785)
                  ·
                    refine ⟨1422949374049646976255589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1897265832066195968340785 1422949374049646976255589)
                    ·
                      refine ⟨266803007634308808047923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1422949374049646976255589 266803007634308808047923)
                      ·
                        rfl

theorem cell23_519597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_519597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519597 prefixEnd_519597 := by exact prefixLift 519597
  have htrace : WordTrace (prefixWord ++ tailWord_519597) baseStart_519597 baseEnd_519597 := by
    simpa [prefixWord, tailWord_519597, baseEnd_519597] using wordTrace_append hprefix tailTrace_519597
  have hstable : (prefixWord ++ tailWord_519597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519597).length < 2 ^ (prefixWord ++ tailWord_519597).sum := by decide
  have hdescent : baseEnd_519597 < baseStart_519597 := by decide
  rcases family_descends (prefixWord ++ tailWord_519597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519601 : List Nat := [1, 2, 2, 4, 1, 1, 4, 3, 1, 2, 2]
def baseStart_519601 : Nat := 118140960795 + 519601 * 2 ^ 59
def prefixEnd_519601 : Nat := 4983230072969 + 3 ^ 40 * 519601 * 2
def baseEnd_519601 : Nat := 266805061556926792397905

theorem tailTrace_519601 : CollatzResearch.WordTrace tailWord_519601 prefixEnd_519601 266805061556926792397905 := by
  unfold tailWord_519601
  simp only [CollatzResearch.WordTrace]
  refine ⟨18951405390581792630894657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12634270260387861753929771 18951405390581792630894657)
  ·
    refine ⟨14213554042936344473170993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18951405390581792630894657 14213554042936344473170993)
    ·
      refine ⟨10660165532202258354878245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14213554042936344473170993 10660165532202258354878245)
      ·
        refine ⟨1998781037287923441539671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10660165532202258354878245 1998781037287923441539671)
        ·
          refine ⟨2998171555931885162309507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1998781037287923441539671 2998171555931885162309507)
          ·
            refine ⟨4497257333897827743464261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2998171555931885162309507 4497257333897827743464261)
            ·
              refine ⟨843235750105842701899549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4497257333897827743464261 843235750105842701899549)
              ·
                refine ⟨316213406289691013212331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 843235750105842701899549 316213406289691013212331)
                ·
                  refine ⟨474320109434536519818497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316213406289691013212331 474320109434536519818497)
                  ·
                    refine ⟨355740082075902389863873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 474320109434536519818497 355740082075902389863873)
                    ·
                      refine ⟨266805061556926792397905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 355740082075902389863873 266805061556926792397905)
                      ·
                        rfl

theorem cell23_519601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_519601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519601 prefixEnd_519601 := by exact prefixLift 519601
  have htrace : WordTrace (prefixWord ++ tailWord_519601) baseStart_519601 baseEnd_519601 := by
    simpa [prefixWord, tailWord_519601, baseEnd_519601] using wordTrace_append hprefix tailTrace_519601
  have hstable : (prefixWord ++ tailWord_519601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519601).length < 2 ^ (prefixWord ++ tailWord_519601).sum := by decide
  have hdescent : baseEnd_519601 < baseStart_519601 := by decide
  rcases family_descends (prefixWord ++ tailWord_519601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519643 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 5]
def baseStart_519643 : Nat := 118140960795 + 519643 * 2 ^ 59
def prefixEnd_519643 : Nat := 4983230072969 + 3 ^ 40 * 519643 * 2
def baseEnd_519643 : Nat := 266826627744415628072711

theorem tailTrace_519643 : CollatzResearch.WordTrace tailWord_519643 prefixEnd_519643 266826627744415628072711 := by
  unfold tailWord_519643
  simp only [CollatzResearch.WordTrace]
  refine ⟨18952937256429633803923583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12635291504286422535949055 18952937256429633803923583)
  ·
    refine ⟨28429405884644450705885375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18952937256429633803923583 28429405884644450705885375)
    ·
      refine ⟨42644108826966676058828063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28429405884644450705885375 42644108826966676058828063)
      ·
        refine ⟨63966163240450014088242095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42644108826966676058828063 63966163240450014088242095)
        ·
          refine ⟨95949244860675021132363143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63966163240450014088242095 95949244860675021132363143)
          ·
            refine ⟨143923867291012531698544715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95949244860675021132363143 143923867291012531698544715)
            ·
              refine ⟨215885800936518797547817073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143923867291012531698544715 215885800936518797547817073)
              ·
                refine ⟨161914350702389098160862805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215885800936518797547817073 161914350702389098160862805)
                ·
                  refine ⟨1897433797293622244072611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 161914350702389098160862805 1897433797293622244072611)
                  ·
                    refine ⟨2846150695940433366108917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1897433797293622244072611 2846150695940433366108917)
                    ·
                      refine ⟨266826627744415628072711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2846150695940433366108917 266826627744415628072711)
                      ·
                        rfl

theorem cell23_519643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 5].length) (baseStart_519643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519643 prefixEnd_519643 := by exact prefixLift 519643
  have htrace : WordTrace (prefixWord ++ tailWord_519643) baseStart_519643 baseEnd_519643 := by
    simpa [prefixWord, tailWord_519643, baseEnd_519643] using wordTrace_append hprefix tailTrace_519643
  have hstable : (prefixWord ++ tailWord_519643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519643).length < 2 ^ (prefixWord ++ tailWord_519643).sum := by decide
  have hdescent : baseEnd_519643 < baseStart_519643 := by decide
  rcases family_descends (prefixWord ++ tailWord_519643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519663 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 9]
def baseStart_519663 : Nat := 118140960795 + 519663 * 2 ^ 59
def prefixEnd_519663 : Nat := 4983230072969 + 3 ^ 40 * 519663 * 2
def baseEnd_519663 : Nat := 29648544150833949980291

theorem tailTrace_519663 : CollatzResearch.WordTrace tailWord_519663 prefixEnd_519663 29648544150833949980291 := by
  unfold tailWord_519663
  simp only [CollatzResearch.WordTrace]
  refine ⟨18953666716357177219651643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12635777810904784813101095 18953666716357177219651643)
  ·
    refine ⟨28430500074535765829477465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18953666716357177219651643 28430500074535765829477465)
    ·
      refine ⟨21322875055901824372108099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28430500074535765829477465 21322875055901824372108099)
      ·
        refine ⟨31984312583852736558162149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21322875055901824372108099 31984312583852736558162149)
        ·
          refine ⟨5997058609472388104655403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31984312583852736558162149 5997058609472388104655403)
          ·
            refine ⟨8995587914208582156983105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5997058609472388104655403 8995587914208582156983105)
            ·
              refine ⟨6746690935656436617737329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8995587914208582156983105 6746690935656436617737329)
              ·
                refine ⟨5060018201742327463302997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6746690935656436617737329 5060018201742327463302997)
                ·
                  refine ⟨29648544150833949980291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5060018201742327463302997 29648544150833949980291)
                  ·
                    rfl

theorem cell23_519663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 9].length) (baseStart_519663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519663 prefixEnd_519663 := by exact prefixLift 519663
  have htrace : WordTrace (prefixWord ++ tailWord_519663) baseStart_519663 baseEnd_519663 := by
    simpa [prefixWord, tailWord_519663, baseEnd_519663] using wordTrace_append hprefix tailTrace_519663
  have hstable : (prefixWord ++ tailWord_519663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519663).length < 2 ^ (prefixWord ++ tailWord_519663).sum := by decide
  have hdescent : baseEnd_519663 < baseStart_519663 := by decide
  rcases family_descends (prefixWord ++ tailWord_519663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519673 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 9]
def baseStart_519673 : Nat := 118140960795 + 519673 * 2 ^ 59
def prefixEnd_519673 : Nat := 4983230072969 + 3 ^ 40 * 519673 * 2
def baseEnd_519673 : Nat := 266842032164050510697573

theorem tailTrace_519673 : CollatzResearch.WordTrace tailWord_519673 prefixEnd_519673 266842032164050510697573 := by
  unfold tailWord_519673
  simp only [CollatzResearch.WordTrace]
  refine ⟨18954031446320948927515673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12636020964213965951677115 18954031446320948927515673)
  ·
    refine ⟨14215523584740711695636755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18954031446320948927515673 14215523584740711695636755)
    ·
      refine ⟨21323285377111067543455133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14215523584740711695636755 21323285377111067543455133)
      ·
        refine ⟨7996232016416650328795675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21323285377111067543455133 7996232016416650328795675)
        ·
          refine ⟨11994348024624975493193513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7996232016416650328795675 11994348024624975493193513)
          ·
            refine ⟨8995761018468731619895135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11994348024624975493193513 8995761018468731619895135)
            ·
              refine ⟨13493641527703097429842703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8995761018468731619895135 13493641527703097429842703)
              ·
                refine ⟨20240462291554646144764055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13493641527703097429842703 20240462291554646144764055)
                ·
                  refine ⟨30360693437331969217146083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20240462291554646144764055 30360693437331969217146083)
                  ·
                    refine ⟨45541040155997953825719125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30360693437331969217146083 45541040155997953825719125)
                    ·
                      refine ⟨266842032164050510697573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 45541040155997953825719125 266842032164050510697573)
                      ·
                        rfl

theorem cell23_519673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_519673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519673 prefixEnd_519673 := by exact prefixLift 519673
  have htrace : WordTrace (prefixWord ++ tailWord_519673) baseStart_519673 baseEnd_519673 := by
    simpa [prefixWord, tailWord_519673, baseEnd_519673] using wordTrace_append hprefix tailTrace_519673
  have hstable : (prefixWord ++ tailWord_519673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519673).length < 2 ^ (prefixWord ++ tailWord_519673).sum := by decide
  have hdescent : baseEnd_519673 < baseStart_519673 := by decide
  rcases family_descends (prefixWord ++ tailWord_519673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519674 : List Nat := [3, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2]
def baseStart_519674 : Nat := 118140960795 + 519674 * 2 ^ 59
def prefixEnd_519674 : Nat := 4983230072969 + 3 ^ 40 * 519674 * 2
def baseEnd_519674 : Nat := 266842545644705006785069

theorem tailTrace_519674 : CollatzResearch.WordTrace tailWord_519674 prefixEnd_519674 266842545644705006785069 := by
  unfold tailWord_519674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4738516979829331524575519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12636045279544884065534717 4738516979829331524575519)
  ·
    refine ⟨7107775469743997286863279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4738516979829331524575519 7107775469743997286863279)
    ·
      refine ⟨10661663204615995930294919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7107775469743997286863279 10661663204615995930294919)
      ·
        refine ⟨15992494806923993895442379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10661663204615995930294919 15992494806923993895442379)
        ·
          refine ⟨23988742210385990843163569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15992494806923993895442379 23988742210385990843163569)
          ·
            refine ⟨17991556657789493132372677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23988742210385990843163569 17991556657789493132372677)
            ·
              refine ⟨3373416873335529962319877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17991556657789493132372677 3373416873335529962319877)
              ·
                refine ⟨632515663750411867934977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3373416873335529962319877 632515663750411867934977)
                ·
                  refine ⟨474386747812808900951233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632515663750411867934977 474386747812808900951233)
                  ·
                    refine ⟨355790060859606675713425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 474386747812808900951233 355790060859606675713425)
                    ·
                      refine ⟨266842545644705006785069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 355790060859606675713425 266842545644705006785069)
                      ·
                        rfl

theorem cell23_519674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2].length) (baseStart_519674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519674 prefixEnd_519674 := by exact prefixLift 519674
  have htrace : WordTrace (prefixWord ++ tailWord_519674) baseStart_519674 baseEnd_519674 := by
    simpa [prefixWord, tailWord_519674, baseEnd_519674] using wordTrace_append hprefix tailTrace_519674
  have hstable : (prefixWord ++ tailWord_519674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519674).length < 2 ^ (prefixWord ++ tailWord_519674).sum := by decide
  have hdescent : baseEnd_519674 < baseStart_519674 := by decide
  rcases family_descends (prefixWord ++ tailWord_519674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519683 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 8]
def baseStart_519683 : Nat := 118140960795 + 519683 * 2 ^ 59
def prefixEnd_519683 : Nat := 4983230072969 + 3 ^ 40 * 519683 * 2
def baseEnd_519683 : Nat := 266847166970595471572527

theorem tailTrace_519683 : CollatzResearch.WordTrace tailWord_519683 prefixEnd_519683 266847166970595471572527 := by
  unfold tailWord_519683
  simp only [CollatzResearch.WordTrace]
  refine ⟨18954396176284720635379703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12636264117523147090253135 18954396176284720635379703)
  ·
    refine ⟨28431594264427080953069555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18954396176284720635379703 28431594264427080953069555)
    ·
      refine ⟨42647391396640621429604333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28431594264427080953069555 42647391396640621429604333)
      ·
        refine ⟨15992771773740233036101625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42647391396640621429604333 15992771773740233036101625)
        ·
          refine ⟨11994578830305174777076219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15992771773740233036101625 11994578830305174777076219)
          ·
            refine ⟨17991868245457762165614329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11994578830305174777076219 17991868245457762165614329)
            ·
              refine ⟨13493901184093321624210747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17991868245457762165614329 13493901184093321624210747)
              ·
                refine ⟨20240851776139982436316121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13493901184093321624210747 20240851776139982436316121)
                ·
                  refine ⟨15180638832104986827237091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20240851776139982436316121 15180638832104986827237091)
                  ·
                    refine ⟨22770958248157480240855637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15180638832104986827237091 22770958248157480240855637)
                    ·
                      refine ⟨266847166970595471572527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 22770958248157480240855637 266847166970595471572527)
                      ·
                        rfl

theorem cell23_519683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_519683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519683 prefixEnd_519683 := by exact prefixLift 519683
  have htrace : WordTrace (prefixWord ++ tailWord_519683) baseStart_519683 baseEnd_519683 := by
    simpa [prefixWord, tailWord_519683, baseEnd_519683] using wordTrace_append hprefix tailTrace_519683
  have hstable : (prefixWord ++ tailWord_519683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519683).length < 2 ^ (prefixWord ++ tailWord_519683).sum := by decide
  have hdescent : baseEnd_519683 < baseStart_519683 := by decide
  rcases family_descends (prefixWord ++ tailWord_519683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519691 : List Nat := [1, 1, 1, 1, 8, 1, 1, 3, 2, 2, 2]
def baseStart_519691 : Nat := 118140960795 + 519691 * 2 ^ 59
def prefixEnd_519691 : Nat := 4983230072969 + 3 ^ 40 * 519691 * 2
def baseEnd_519691 : Nat := 266851274815831440272491

theorem tailTrace_519691 : CollatzResearch.WordTrace tailWord_519691 prefixEnd_519691 266851274815831440272491 := by
  unfold tailWord_519691
  simp only [CollatzResearch.WordTrace]
  refine ⟨18954687960255738001670927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12636458640170492001113951 18954687960255738001670927)
  ·
    refine ⟨28432031940383607002506391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18954687960255738001670927 28432031940383607002506391)
    ·
      refine ⟨42648047910575410503759587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28432031940383607002506391 42648047910575410503759587)
      ·
        refine ⟨63972071865863115755639381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42648047910575410503759587 63972071865863115755639381)
        ·
          refine ⟨749672717178083387761399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 63972071865863115755639381 749672717178083387761399)
          ·
            refine ⟨1124509075767125081642099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749672717178083387761399 1124509075767125081642099)
            ·
              refine ⟨1686763613650687622463149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124509075767125081642099 1686763613650687622463149)
              ·
                refine ⟨632536355119007858423681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1686763613650687622463149 632536355119007858423681)
                ·
                  refine ⟨474402266339255893817761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632536355119007858423681 474402266339255893817761)
                  ·
                    refine ⟨355801699754441920363321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 474402266339255893817761 355801699754441920363321)
                    ·
                      refine ⟨266851274815831440272491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 355801699754441920363321 266851274815831440272491)
                      ·
                        rfl

theorem cell23_519691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 2, 2].length) (baseStart_519691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519691 prefixEnd_519691 := by exact prefixLift 519691
  have htrace : WordTrace (prefixWord ++ tailWord_519691) baseStart_519691 baseEnd_519691 := by
    simpa [prefixWord, tailWord_519691, baseEnd_519691] using wordTrace_append hprefix tailTrace_519691
  have hstable : (prefixWord ++ tailWord_519691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519691).length < 2 ^ (prefixWord ++ tailWord_519691).sum := by decide
  have hdescent : baseEnd_519691 < baseStart_519691 := by decide
  rcases family_descends (prefixWord ++ tailWord_519691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519730 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_519730 : Nat := 118140960795 + 519730 * 2 ^ 59
def prefixEnd_519730 : Nat := 4983230072969 + 3 ^ 40 * 519730 * 2
def baseEnd_519730 : Nat := 266871300561356787684811

theorem tailTrace_519730 : CollatzResearch.WordTrace tailWord_519730 prefixEnd_519730 266871300561356787684811 := by
  unfold tailWord_519730
  simp only [CollatzResearch.WordTrace]
  refine ⟨4739027601778611915585161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12637406938076298441560429 4739027601778611915585161)
  ·
    refine ⟨3554270701333958936688871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4739027601778611915585161 3554270701333958936688871)
    ·
      refine ⟨5331406052000938405033307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3554270701333958936688871 5331406052000938405033307)
      ·
        refine ⟨7997109078001407607549961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5331406052000938405033307 7997109078001407607549961)
        ·
          refine ⟨5997831808501055705662471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7997109078001407607549961 5997831808501055705662471)
          ·
            refine ⟨8996747712751583558493707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5997831808501055705662471 8996747712751583558493707)
            ·
              refine ⟨13495121569127375337740561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8996747712751583558493707 13495121569127375337740561)
              ·
                refine ⟨10121341176845531503305421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13495121569127375337740561 10121341176845531503305421)
                ·
                  refine ⟨3795502941317074313739533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10121341176845531503305421 3795502941317074313739533)
                  ·
                    refine ⟨1423313602993902867652325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3795502941317074313739533 1423313602993902867652325)
                    ·
                      refine ⟨266871300561356787684811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1423313602993902867652325 266871300561356787684811)
                      ·
                        rfl

theorem cell23_519730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_519730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519730 prefixEnd_519730 := by exact prefixLift 519730
  have htrace : WordTrace (prefixWord ++ tailWord_519730) baseStart_519730 baseEnd_519730 := by
    simpa [prefixWord, tailWord_519730, baseEnd_519730] using wordTrace_append hprefix tailTrace_519730
  have hstable : (prefixWord ++ tailWord_519730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519730).length < 2 ^ (prefixWord ++ tailWord_519730).sum := by decide
  have hdescent : baseEnd_519730 < baseStart_519730 := by decide
  rcases family_descends (prefixWord ++ tailWord_519730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519767 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 3]
def baseStart_519767 : Nat := 118140960795 + 519767 * 2 ^ 59
def prefixEnd_519767 : Nat := 4983230072969 + 3 ^ 40 * 519767 * 2
def baseEnd_519767 : Nat := 266890299345573142922141

theorem tailTrace_519767 : CollatzResearch.WordTrace tailWord_519767 prefixEnd_519767 266890299345573142922141 := by
  unfold tailWord_519767
  simp only [CollatzResearch.WordTrace]
  refine ⟨18957459907980402981437555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12638306605320268654291703 18957459907980402981437555)
  ·
    refine ⟨28436189861970604472156333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18957459907980402981437555 28436189861970604472156333)
    ·
      refine ⟨10663571198238976677058625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28436189861970604472156333 10663571198238976677058625)
      ·
        refine ⟨7997678398679232507793969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10663571198238976677058625 7997678398679232507793969)
        ·
          refine ⟨5998258799009424380845477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7997678398679232507793969 5998258799009424380845477)
          ·
            refine ⟨1124673524814267071408527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5998258799009424380845477 1124673524814267071408527)
            ·
              refine ⟨1687010287221400607112791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124673524814267071408527 1687010287221400607112791)
              ·
                refine ⟨2530515430832100910669187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1687010287221400607112791 2530515430832100910669187)
                ·
                  refine ⟨3795773146248151366003781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2530515430832100910669187 3795773146248151366003781)
                  ·
                    refine ⟨711707464921528381125709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3795773146248151366003781 711707464921528381125709)
                    ·
                      refine ⟨266890299345573142922141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 711707464921528381125709 266890299345573142922141)
                      ·
                        rfl

theorem cell23_519767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_519767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519767 prefixEnd_519767 := by exact prefixLift 519767
  have htrace : WordTrace (prefixWord ++ tailWord_519767) baseStart_519767 baseEnd_519767 := by
    simpa [prefixWord, tailWord_519767, baseEnd_519767] using wordTrace_append hprefix tailTrace_519767
  have hstable : (prefixWord ++ tailWord_519767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519767).length < 2 ^ (prefixWord ++ tailWord_519767).sum := by decide
  have hdescent : baseEnd_519767 < baseStart_519767 := by decide
  rcases family_descends (prefixWord ++ tailWord_519767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519817 : List Nat := [1, 2, 1, 1, 4, 1, 3, 4, 1, 5]
def baseStart_519817 : Nat := 118140960795 + 519817 * 2 ^ 59
def prefixEnd_519817 : Nat := 4983230072969 + 3 ^ 40 * 519817 * 2
def baseEnd_519817 : Nat := 88971991126099315765637

theorem tailTrace_519817 : CollatzResearch.WordTrace tailWord_519817 prefixEnd_519817 88971991126099315765637 := by
  unfold tailWord_519817
  simp only [CollatzResearch.WordTrace]
  refine ⟨18959283557799261520757705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12639522371866174347171803 18959283557799261520757705)
  ·
    refine ⟨14219462668349446140568279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18959283557799261520757705 14219462668349446140568279)
    ·
      refine ⟨21329194002524169210852419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14219462668349446140568279 21329194002524169210852419)
      ·
        refine ⟨31993791003786253816278629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21329194002524169210852419 31993791003786253816278629)
        ·
          refine ⟨5998835813209922590552243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31993791003786253816278629 5998835813209922590552243)
          ·
            refine ⟨8998253719814883885828365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5998835813209922590552243 8998253719814883885828365)
            ·
              refine ⟨3374345144930581457185637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8998253719814883885828365 3374345144930581457185637)
              ·
                refine ⟨632689714674484023222307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3374345144930581457185637 632689714674484023222307)
                ·
                  refine ⟨949034572011726034833461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632689714674484023222307 949034572011726034833461)
                  ·
                    refine ⟨88971991126099315765637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 949034572011726034833461 88971991126099315765637)
                    ·
                      rfl

theorem cell23_519817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 5].length) (baseStart_519817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519817 prefixEnd_519817 := by exact prefixLift 519817
  have htrace : WordTrace (prefixWord ++ tailWord_519817) baseStart_519817 baseEnd_519817 := by
    simpa [prefixWord, tailWord_519817, baseEnd_519817] using wordTrace_append hprefix tailTrace_519817
  have hstable : (prefixWord ++ tailWord_519817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519817).length < 2 ^ (prefixWord ++ tailWord_519817).sum := by decide
  have hdescent : baseEnd_519817 < baseStart_519817 := by decide
  rcases family_descends (prefixWord ++ tailWord_519817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519837 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_519837 : Nat := 118140960795 + 519837 * 2 ^ 59
def prefixEnd_519837 : Nat := 4983230072969 + 3 ^ 40 * 519837 * 2
def baseEnd_519837 : Nat := 266926242991387869046819

theorem tailTrace_519837 : CollatzResearch.WordTrace tailWord_519837 prefixEnd_519837 266926242991387869046819 := by
  unfold tailWord_519837
  simp only [CollatzResearch.WordTrace]
  refine ⟨18960013017726804936485765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12640008678484536624323843 18960013017726804936485765)
  ·
    refine ⟨3555002440823775925591081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18960013017726804936485765 3555002440823775925591081)
    ·
      refine ⟨2666251830617831944193311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3555002440823775925591081 2666251830617831944193311)
      ·
        refine ⟨3999377745926747916289967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2666251830617831944193311 3999377745926747916289967)
        ·
          refine ⟨5999066618890121874434951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3999377745926747916289967 5999066618890121874434951)
          ·
            refine ⟨8998599928335182811652427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5999066618890121874434951 8998599928335182811652427)
            ·
              refine ⟨13497899892502774217478641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8998599928335182811652427 13497899892502774217478641)
              ·
                refine ⟨10123424919377080663108981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13497899892502774217478641 10123424919377080663108981)
                ·
                  refine ⟨949071086191601312166467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10123424919377080663108981 949071086191601312166467)
                  ·
                    refine ⟨1423606629287401968249701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 949071086191601312166467 1423606629287401968249701)
                    ·
                      refine ⟨266926242991387869046819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1423606629287401968249701 266926242991387869046819)
                      ·
                        rfl

theorem cell23_519837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_519837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519837 prefixEnd_519837 := by exact prefixLift 519837
  have htrace : WordTrace (prefixWord ++ tailWord_519837) baseStart_519837 baseEnd_519837 := by
    simpa [prefixWord, tailWord_519837, baseEnd_519837] using wordTrace_append hprefix tailTrace_519837
  have hstable : (prefixWord ++ tailWord_519837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519837).length < 2 ^ (prefixWord ++ tailWord_519837).sum := by decide
  have hdescent : baseEnd_519837 < baseStart_519837 := by decide
  rcases family_descends (prefixWord ++ tailWord_519837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519841 : List Nat := [1, 2, 3, 3, 2, 2, 1, 2, 2, 3, 2]
def baseStart_519841 : Nat := 118140960795 + 519841 * 2 ^ 59
def prefixEnd_519841 : Nat := 4983230072969 + 3 ^ 40 * 519841 * 2
def baseEnd_519841 : Nat := 266928296914005853396801

theorem tailTrace_519841 : CollatzResearch.WordTrace tailWord_519841 prefixEnd_519841 266928296914005853396801 := by
  unfold tailWord_519841
  simp only [CollatzResearch.WordTrace]
  refine ⟨18960158909712313619631377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12640105939808209079754251 18960158909712313619631377)
  ·
    refine ⟨14220119182284235214723533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18960158909712313619631377 14220119182284235214723533)
    ·
      refine ⟨5332544693356588205521325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14220119182284235214723533 5332544693356588205521325)
      ·
        refine ⟨1999704260008720577070497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5332544693356588205521325 1999704260008720577070497)
        ·
          refine ⟨1499778195006540432802873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1999704260008720577070497 1499778195006540432802873)
          ·
            refine ⟨1124833646254905324602155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1499778195006540432802873 1124833646254905324602155)
            ·
              refine ⟨1687250469382357986903233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124833646254905324602155 1687250469382357986903233)
              ·
                refine ⟨1265437852036768490177425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1687250469382357986903233 1265437852036768490177425)
                ·
                  refine ⟨949078389027576367633069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1265437852036768490177425 949078389027576367633069)
                  ·
                    refine ⟨355904395885341137862401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 949078389027576367633069 355904395885341137862401)
                    ·
                      refine ⟨266928296914005853396801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 355904395885341137862401 266928296914005853396801)
                      ·
                        rfl

theorem cell23_519841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_519841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519841 prefixEnd_519841 := by exact prefixLift 519841
  have htrace : WordTrace (prefixWord ++ tailWord_519841) baseStart_519841 baseEnd_519841 := by
    simpa [prefixWord, tailWord_519841, baseEnd_519841] using wordTrace_append hprefix tailTrace_519841
  have hstable : (prefixWord ++ tailWord_519841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519841).length < 2 ^ (prefixWord ++ tailWord_519841).sum := by decide
  have hdescent : baseEnd_519841 < baseStart_519841 := by decide
  rcases family_descends (prefixWord ++ tailWord_519841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519894 : List Nat := [5, 2, 1, 3, 12]
def baseStart_519894 : Nat := 118140960795 + 519894 * 2 ^ 59
def prefixEnd_519894 : Nat := 4983230072969 + 3 ^ 40 * 519894 * 2
def baseEnd_519894 : Nat := 366194117131267690033

theorem tailTrace_519894 : CollatzResearch.WordTrace tailWord_519894 prefixEnd_519894 366194117131267690033 := by
  unfold tailWord_519894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1185130748657518979456921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12641394652346869114207157 1185130748657518979456921)
  ·
    refine ⟨888848061493139234592691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1185130748657518979456921 888848061493139234592691)
    ·
      refine ⟨1333272092239708851889037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 888848061493139234592691 1333272092239708851889037)
      ·
        refine ⟨499977034589890819458389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1333272092239708851889037 499977034589890819458389)
        ·
          refine ⟨366194117131267690033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 499977034589890819458389 366194117131267690033)
          ·
            rfl

theorem cell23_519894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 12].length) (baseStart_519894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519894 prefixEnd_519894 := by exact prefixLift 519894
  have htrace : WordTrace (prefixWord ++ tailWord_519894) baseStart_519894 baseEnd_519894 := by
    simpa [prefixWord, tailWord_519894, baseEnd_519894] using wordTrace_append hprefix tailTrace_519894
  have hstable : (prefixWord ++ tailWord_519894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519894).length < 2 ^ (prefixWord ++ tailWord_519894).sum := by decide
  have hdescent : baseEnd_519894 < baseStart_519894 := by decide
  rcases family_descends (prefixWord ++ tailWord_519894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519904 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 4, 1, 3]
def baseStart_519904 : Nat := 118140960795 + 519904 * 2 ^ 59
def prefixEnd_519904 : Nat := 4983230072969 + 3 ^ 40 * 519904 * 2
def baseEnd_519904 : Nat := 266960646195239106909011

theorem tailTrace_519904 : CollatzResearch.WordTrace tailWord_519904 prefixEnd_519904 266960646195239106909011 := by
  unfold tailWord_519904
  simp only [CollatzResearch.WordTrace]
  refine ⟨9481228354242037689587383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12641637805656050252783177 9481228354242037689587383)
  ·
    refine ⟨14221842531363056534381075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9481228354242037689587383 14221842531363056534381075)
    ·
      refine ⟨21332763797044584801571613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14221842531363056534381075 21332763797044584801571613)
      ·
        refine ⟨7999786423891719300589355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21332763797044584801571613 7999786423891719300589355)
        ·
          refine ⟨11999679635837578950884033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7999786423891719300589355 11999679635837578950884033)
          ·
            refine ⟨8999759726878184213163025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11999679635837578950884033 8999759726878184213163025)
            ·
              refine ⟨6749819795158638159872269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8999759726878184213163025 6749819795158638159872269)
              ·
                refine ⟨2531182423184489309952101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6749819795158638159872269 2531182423184489309952101)
                ·
                  refine ⟨474596704347091745616019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2531182423184489309952101 474596704347091745616019)
                  ·
                    refine ⟨711895056520637618424029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 474596704347091745616019 711895056520637618424029)
                    ·
                      refine ⟨266960646195239106909011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 711895056520637618424029 266960646195239106909011)
                      ·
                        rfl

theorem cell23_519904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_519904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519904 prefixEnd_519904 := by exact prefixLift 519904
  have htrace : WordTrace (prefixWord ++ tailWord_519904) baseStart_519904 baseEnd_519904 := by
    simpa [prefixWord, tailWord_519904, baseEnd_519904] using wordTrace_append hprefix tailTrace_519904
  have hstable : (prefixWord ++ tailWord_519904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519904).length < 2 ^ (prefixWord ++ tailWord_519904).sum := by decide
  have hdescent : baseEnd_519904 < baseStart_519904 := by decide
  rcases family_descends (prefixWord ++ tailWord_519904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519905 : List Nat := [1, 2, 3, 1, 5, 1, 1, 4, 1, 2, 2]
def baseStart_519905 : Nat := 118140960795 + 519905 * 2 ^ 59
def prefixEnd_519905 : Nat := 4983230072969 + 3 ^ 40 * 519905 * 2
def baseEnd_519905 : Nat := 266961159675893602996507

theorem tailTrace_519905 : CollatzResearch.WordTrace tailWord_519905 prefixEnd_519905 266961159675893602996507 := by
  unfold tailWord_519905
  simp only [CollatzResearch.WordTrace]
  refine ⟨18962493181480452549961169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12641662120986968366640779 18962493181480452549961169)
  ·
    refine ⟨14221869886110339412470877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18962493181480452549961169 14221869886110339412470877)
    ·
      refine ⟨5333201207291377279676579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14221869886110339412470877 5333201207291377279676579)
      ·
        refine ⟨7999801810937065919514869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5333201207291377279676579 7999801810937065919514869)
        ·
          refine ⟨749981419775349929954519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7999801810937065919514869 749981419775349929954519)
          ·
            refine ⟨1124972129663024894931779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749981419775349929954519 1124972129663024894931779)
            ·
              refine ⟨1687458194494537342397669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124972129663024894931779 1687458194494537342397669)
              ·
                refine ⟨316398411467725751699563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1687458194494537342397669 316398411467725751699563)
                ·
                  refine ⟨474597617201588627549345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316398411467725751699563 474597617201588627549345)
                  ·
                    refine ⟨355948212901191470662009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 474597617201588627549345 355948212901191470662009)
                    ·
                      refine ⟨266961159675893602996507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 355948212901191470662009 266961159675893602996507)
                      ·
                        rfl

theorem cell23_519905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 1, 2, 2].length) (baseStart_519905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519905 prefixEnd_519905 := by exact prefixLift 519905
  have htrace : WordTrace (prefixWord ++ tailWord_519905) baseStart_519905 baseEnd_519905 := by
    simpa [prefixWord, tailWord_519905, baseEnd_519905] using wordTrace_append hprefix tailTrace_519905
  have hstable : (prefixWord ++ tailWord_519905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519905).length < 2 ^ (prefixWord ++ tailWord_519905).sum := by decide
  have hdescent : baseEnd_519905 < baseStart_519905 := by decide
  rcases family_descends (prefixWord ++ tailWord_519905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519911 : List Nat := [1, 1, 5, 4, 1, 2, 1, 8]
def baseStart_519911 : Nat := 118140960795 + 519911 * 2 ^ 59
def prefixEnd_519911 : Nat := 4983230072969 + 3 ^ 40 * 519911 * 2
def baseEnd_519911 : Nat := 9887564465178539982277

theorem tailTrace_519911 : CollatzResearch.WordTrace tailWord_519911 prefixEnd_519911 9887564465178539982277 := by
  unfold tailWord_519911
  simp only [CollatzResearch.WordTrace]
  refine ⟨18962712019458715574679587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12641808012972477049786391 18962712019458715574679587)
  ·
    refine ⟨28444068029188073362019381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18962712019458715574679587 28444068029188073362019381)
    ·
      refine ⟨2666631377736381877689317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28444068029188073362019381 2666631377736381877689317)
      ·
        refine ⟨499993383325571602066747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2666631377736381877689317 499993383325571602066747)
        ·
          refine ⟨749990074988357403100121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499993383325571602066747 749990074988357403100121)
          ·
            refine ⟨562492556241268052325091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 749990074988357403100121 562492556241268052325091)
            ·
              refine ⟨843738834361902078487637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562492556241268052325091 843738834361902078487637)
              ·
                refine ⟨9887564465178539982277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 843738834361902078487637 9887564465178539982277)
                ·
                  rfl

theorem cell23_519911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 8].length) (baseStart_519911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519911 prefixEnd_519911 := by exact prefixLift 519911
  have htrace : WordTrace (prefixWord ++ tailWord_519911) baseStart_519911 baseEnd_519911 := by
    simpa [prefixWord, tailWord_519911, baseEnd_519911] using wordTrace_append hprefix tailTrace_519911
  have hstable : (prefixWord ++ tailWord_519911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519911).length < 2 ^ (prefixWord ++ tailWord_519911).sum := by decide
  have hdescent : baseEnd_519911 < baseStart_519911 := by decide
  rcases family_descends (prefixWord ++ tailWord_519911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519921 : List Nat := [1, 2, 2, 2, 2, 3, 2, 3, 2, 1, 3]
def baseStart_519921 : Nat := 118140960795 + 519921 * 2 ^ 59
def prefixEnd_519921 : Nat := 4983230072969 + 3 ^ 40 * 519921 * 2
def baseEnd_519921 : Nat := 266969375366365540396433

theorem tailTrace_519921 : CollatzResearch.WordTrace tailWord_519921 prefixEnd_519921 266969375366365540396433 := by
  unfold tailWord_519921
  simp only [CollatzResearch.WordTrace]
  refine ⟨18963076749422487282543617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12642051166281658188362411 18963076749422487282543617)
  ·
    refine ⟨14222307562066865461907713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18963076749422487282543617 14222307562066865461907713)
    ·
      refine ⟨10666730671550149096430785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14222307562066865461907713 10666730671550149096430785)
      ·
        refine ⟨8000048003662611822323089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10666730671550149096430785 8000048003662611822323089)
        ·
          refine ⟨6000036002746958866742317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8000048003662611822323089 6000036002746958866742317)
          ·
            refine ⟨2250013501030109575028369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6000036002746958866742317 2250013501030109575028369)
            ·
              refine ⟨1687510125772582181271277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2250013501030109575028369 1687510125772582181271277)
              ·
                refine ⟨632816297164718317976729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1687510125772582181271277 632816297164718317976729)
                ·
                  refine ⟨474612222873538738482547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632816297164718317976729 474612222873538738482547)
                  ·
                    refine ⟨711918334310308107723821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 474612222873538738482547 711918334310308107723821)
                    ·
                      refine ⟨266969375366365540396433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 711918334310308107723821 266969375366365540396433)
                      ·
                        rfl

theorem cell23_519921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_519921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519921 prefixEnd_519921 := by exact prefixLift 519921
  have htrace : WordTrace (prefixWord ++ tailWord_519921) baseStart_519921 baseEnd_519921 := by
    simpa [prefixWord, tailWord_519921, baseEnd_519921] using wordTrace_append hprefix tailTrace_519921
  have hstable : (prefixWord ++ tailWord_519921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519921).length < 2 ^ (prefixWord ++ tailWord_519921).sum := by decide
  have hdescent : baseEnd_519921 < baseStart_519921 := by decide
  rcases family_descends (prefixWord ++ tailWord_519921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519947 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 5]
def baseStart_519947 : Nat := 118140960795 + 519947 * 2 ^ 59
def prefixEnd_519947 : Nat := 4983230072969 + 3 ^ 40 * 519947 * 2
def baseEnd_519947 : Nat := 266982725863382438671313

theorem tailTrace_519947 : CollatzResearch.WordTrace tailWord_519947 prefixEnd_519947 266982725863382438671313 := by
  unfold tailWord_519947
  simp only [CollatzResearch.WordTrace]
  refine ⟨18964025047328293722990095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12642683364885529148660063 18964025047328293722990095)
  ·
    refine ⟨28446037570992440584485143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18964025047328293722990095 28446037570992440584485143)
    ·
      refine ⟨42669056356488660876727715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28446037570992440584485143 42669056356488660876727715)
      ·
        refine ⟨64003584534732991315091573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42669056356488660876727715 64003584534732991315091573)
        ·
          refine ⟨6000336050131217935789835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64003584534732991315091573 6000336050131217935789835)
          ·
            refine ⟨9000504075196826903684753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6000336050131217935789835 9000504075196826903684753)
            ·
              refine ⟨6750378056397620177763565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9000504075196826903684753 6750378056397620177763565)
              ·
                refine ⟨2531391771149107566661337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6750378056397620177763565 2531391771149107566661337)
                ·
                  refine ⟨1898543828361830674996003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2531391771149107566661337 1898543828361830674996003)
                  ·
                    refine ⟨2847815742542746012494005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1898543828361830674996003 2847815742542746012494005)
                    ·
                      refine ⟨266982725863382438671313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2847815742542746012494005 266982725863382438671313)
                      ·
                        rfl

theorem cell23_519947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 5].length) (baseStart_519947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519947 prefixEnd_519947 := by exact prefixLift 519947
  have htrace : WordTrace (prefixWord ++ tailWord_519947) baseStart_519947 baseEnd_519947 := by
    simpa [prefixWord, tailWord_519947, baseEnd_519947] using wordTrace_append hprefix tailTrace_519947
  have hstable : (prefixWord ++ tailWord_519947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519947).length < 2 ^ (prefixWord ++ tailWord_519947).sum := by decide
  have hdescent : baseEnd_519947 < baseStart_519947 := by decide
  rcases family_descends (prefixWord ++ tailWord_519947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519948 : List Nat := [2, 2, 1, 2, 2, 1, 6, 1, 1, 3, 2]
def baseStart_519948 : Nat := 118140960795 + 519948 * 2 ^ 59
def prefixEnd_519948 : Nat := 4983230072969 + 3 ^ 40 * 519948 * 2
def baseEnd_519948 : Nat := 266983239344036934758809

theorem tailTrace_519948 : CollatzResearch.WordTrace tailWord_519948 prefixEnd_519948 266983239344036934758809 := by
  unfold tailWord_519948
  simp only [CollatzResearch.WordTrace]
  refine ⟨9482030760162335446888249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12642707680216447262517665 9482030760162335446888249)
  ·
    refine ⟨7111523070121751585166187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9482030760162335446888249 7111523070121751585166187)
    ·
      refine ⟨10667284605182627377749281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7111523070121751585166187 10667284605182627377749281)
      ·
        refine ⟨8000463453886970533311961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10667284605182627377749281 8000463453886970533311961)
        ·
          refine ⟨6000347590415227899983971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8000463453886970533311961 6000347590415227899983971)
          ·
            refine ⟨9000521385622841849975957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6000347590415227899983971 9000521385622841849975957)
            ·
              refine ⟨421899439951070711717623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9000521385622841849975957 421899439951070711717623)
              ·
                refine ⟨632849159926606067576435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421899439951070711717623 632849159926606067576435)
                ·
                  refine ⟨949273739889909101364653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632849159926606067576435 949273739889909101364653)
                  ·
                    refine ⟨355977652458715913011745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 949273739889909101364653 355977652458715913011745)
                    ·
                      refine ⟨266983239344036934758809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 355977652458715913011745 266983239344036934758809)
                      ·
                        rfl

theorem cell23_519948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_519948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519948 prefixEnd_519948 := by exact prefixLift 519948
  have htrace : WordTrace (prefixWord ++ tailWord_519948) baseStart_519948 baseEnd_519948 := by
    simpa [prefixWord, tailWord_519948, baseEnd_519948] using wordTrace_append hprefix tailTrace_519948
  have hstable : (prefixWord ++ tailWord_519948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519948).length < 2 ^ (prefixWord ++ tailWord_519948).sum := by decide
  have hdescent : baseEnd_519948 < baseStart_519948 := by decide
  rcases family_descends (prefixWord ++ tailWord_519948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519949 : List Nat := [1, 7, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_519949 : Nat := 118140960795 + 519949 * 2 ^ 59
def prefixEnd_519949 : Nat := 4983230072969 + 3 ^ 40 * 519949 * 2
def baseEnd_519949 : Nat := 88994584274897143615435

theorem tailTrace_519949 : CollatzResearch.WordTrace tailWord_519949 prefixEnd_519949 88994584274897143615435 := by
  unfold tailWord_519949
  simp only [CollatzResearch.WordTrace]
  refine ⟨18964097993321048064562901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12642731995547365376375267 18964097993321048064562901)
  ·
    refine ⟨444471046718462064013193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 18964097993321048064562901 444471046718462064013193)
    ·
      refine ⟨333353285038846548009895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444471046718462064013193 333353285038846548009895)
      ·
        refine ⟨500029927558269822014843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333353285038846548009895 500029927558269822014843)
        ·
          refine ⟨750044891337404733022265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500029927558269822014843 750044891337404733022265)
          ·
            refine ⟨562533668503053549766699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 750044891337404733022265 562533668503053549766699)
            ·
              refine ⟨843800502754580324650049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562533668503053549766699 843800502754580324650049)
              ·
                refine ⟨632850377065935243487537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843800502754580324650049 632850377065935243487537)
                ·
                  refine ⟨474637782799451432615653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632850377065935243487537 474637782799451432615653)
                  ·
                    refine ⟨88994584274897143615435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 474637782799451432615653 88994584274897143615435)
                    ·
                      rfl

theorem cell23_519949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_519949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_519949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_519949 prefixEnd_519949 := by exact prefixLift 519949
  have htrace : WordTrace (prefixWord ++ tailWord_519949) baseStart_519949 baseEnd_519949 := by
    simpa [prefixWord, tailWord_519949, baseEnd_519949] using wordTrace_append hprefix tailTrace_519949
  have hstable : (prefixWord ++ tailWord_519949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519949).length < 2 ^ (prefixWord ++ tailWord_519949).sum := by decide
  have hdescent : baseEnd_519949 < baseStart_519949 := by decide
  rcases family_descends (prefixWord ++ tailWord_519949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520018 : List Nat := [3, 2, 2, 1, 1, 4, 3, 2, 5]
def baseStart_520018 : Nat := 118140960795 + 520018 * 2 ^ 59
def prefixEnd_520018 : Nat := 4983230072969 + 3 ^ 40 * 520018 * 2
def baseEnd_520018 : Nat := 29668798109983517875943

theorem tailTrace_520018 : CollatzResearch.WordTrace tailWord_520018 prefixEnd_520018 29668798109983517875943 := by
  unfold tailWord_520018
  simp only [CollatzResearch.WordTrace]
  refine ⟨4741653657517768212206177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12644409753380715232549805 4741653657517768212206177)
  ·
    refine ⟨3556240243138326159154633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4741653657517768212206177 3556240243138326159154633)
    ·
      refine ⟨2667180182353744619365975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3556240243138326159154633 2667180182353744619365975)
      ·
        refine ⟨4000770273530616929048963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2667180182353744619365975 4000770273530616929048963)
        ·
          refine ⟨6001155410295925393573445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4000770273530616929048963 6001155410295925393573445)
          ·
            refine ⟨1125216639430486011295021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6001155410295925393573445 1125216639430486011295021)
            ·
              refine ⟨421956239786432254235633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1125216639430486011295021 421956239786432254235633)
              ·
                refine ⟨316467179839824190676725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421956239786432254235633 316467179839824190676725)
                ·
                  refine ⟨29668798109983517875943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 316467179839824190676725 29668798109983517875943)
                  ·
                    rfl

theorem cell23_520018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_520018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520018 prefixEnd_520018 := by exact prefixLift 520018
  have htrace : WordTrace (prefixWord ++ tailWord_520018) baseStart_520018 baseEnd_520018 := by
    simpa [prefixWord, tailWord_520018, baseEnd_520018] using wordTrace_append hprefix tailTrace_520018
  have hstable : (prefixWord ++ tailWord_520018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520018).length < 2 ^ (prefixWord ++ tailWord_520018).sum := by decide
  have hdescent : baseEnd_520018 < baseStart_520018 := by decide
  rcases family_descends (prefixWord ++ tailWord_520018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520047 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 6]
def baseStart_520047 : Nat := 118140960795 + 520047 * 2 ^ 59
def prefixEnd_520047 : Nat := 4983230072969 + 3 ^ 40 * 520047 * 2
def baseEnd_520047 : Nat := 267034073928832047420853

theorem tailTrace_520047 : CollatzResearch.WordTrace tailWord_520047 prefixEnd_520047 267034073928832047420853 := by
  unfold tailWord_520047
  simp only [CollatzResearch.WordTrace]
  refine ⟨18967672346966010801630395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12645114897977340534420263 18967672346966010801630395)
  ·
    refine ⟨28451508520449016202445593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18967672346966010801630395 28451508520449016202445593)
    ·
      refine ⟨21338631390336762151834195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28451508520449016202445593 21338631390336762151834195)
      ·
        refine ⟨32007947085505143227751293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21338631390336762151834195 32007947085505143227751293)
        ·
          refine ⟨12002980157064428710406735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32007947085505143227751293 12002980157064428710406735)
          ·
            refine ⟨18004470235596643065610103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12002980157064428710406735 18004470235596643065610103)
            ·
              refine ⟨27006705353394964598415155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18004470235596643065610103 27006705353394964598415155)
              ·
                refine ⟨40510058030092446897622733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27006705353394964598415155 40510058030092446897622733)
                ·
                  refine ⟨15191271761284667586608525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40510058030092446897622733 15191271761284667586608525)
                  ·
                    refine ⟨5696726910481750344978197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15191271761284667586608525 5696726910481750344978197)
                    ·
                      refine ⟨267034073928832047420853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5696726910481750344978197 267034073928832047420853)
                      ·
                        rfl

theorem cell23_520047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_520047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520047 prefixEnd_520047 := by exact prefixLift 520047
  have htrace : WordTrace (prefixWord ++ tailWord_520047) baseStart_520047 baseEnd_520047 := by
    simpa [prefixWord, tailWord_520047, baseEnd_520047] using wordTrace_append hprefix tailTrace_520047
  have hstable : (prefixWord ++ tailWord_520047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520047).length < 2 ^ (prefixWord ++ tailWord_520047).sum := by decide
  have hdescent : baseEnd_520047 < baseStart_520047 := by decide
  rcases family_descends (prefixWord ++ tailWord_520047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520111 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 1, 5, 2]
def baseStart_520111 : Nat := 118140960795 + 520111 * 2 ^ 59
def prefixEnd_520111 : Nat := 4983230072969 + 3 ^ 40 * 520111 * 2
def baseEnd_520111 : Nat := 267066936690719797020559

theorem tailTrace_520111 : CollatzResearch.WordTrace tailWord_520111 prefixEnd_520111 267066936690719797020559 := by
  unfold tailWord_520111
  simp only [CollatzResearch.WordTrace]
  refine ⟨18970006618734149731960187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12646671079156099821306791 18970006618734149731960187)
  ·
    refine ⟨28455009928101224597940281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18970006618734149731960187 28455009928101224597940281)
    ·
      refine ⟨21341257446075918448455211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28455009928101224597940281 21341257446075918448455211)
      ·
        refine ⟨32011886169113877672682817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21341257446075918448455211 32011886169113877672682817)
        ·
          refine ⟨24008914626835408254512113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32011886169113877672682817 24008914626835408254512113)
          ·
            refine ⟨18006685970126556190884085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24008914626835408254512113 18006685970126556190884085)
            ·
              refine ⟨1688126809699364642895383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18006685970126556190884085 1688126809699364642895383)
              ·
                refine ⟨2532190214549046964343075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1688126809699364642895383 2532190214549046964343075)
                ·
                  refine ⟨3798285321823570446514613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2532190214549046964343075 3798285321823570446514613)
                  ·
                    refine ⟨356089248920959729360745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3798285321823570446514613 356089248920959729360745)
                    ·
                      refine ⟨267066936690719797020559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 356089248920959729360745 267066936690719797020559)
                      ·
                        rfl

theorem cell23_520111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 5, 2].length) (baseStart_520111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520111 prefixEnd_520111 := by exact prefixLift 520111
  have htrace : WordTrace (prefixWord ++ tailWord_520111) baseStart_520111 baseEnd_520111 := by
    simpa [prefixWord, tailWord_520111, baseEnd_520111] using wordTrace_append hprefix tailTrace_520111
  have hstable : (prefixWord ++ tailWord_520111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520111).length < 2 ^ (prefixWord ++ tailWord_520111).sum := by decide
  have hdescent : baseEnd_520111 < baseStart_520111 := by decide
  rcases family_descends (prefixWord ++ tailWord_520111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520121 : List Nat := [1, 2, 1, 4, 2, 1, 3, 3, 1, 5]
def baseStart_520121 : Nat := 118140960795 + 520121 * 2 ^ 59
def prefixEnd_520121 : Nat := 4983230072969 + 3 ^ 40 * 520121 * 2
def baseEnd_520121 : Nat := 89024023832421585965171

theorem tailTrace_520121 : CollatzResearch.WordTrace tailWord_520121 prefixEnd_520121 89024023832421585965171 := by
  unfold tailWord_520121
  simp only [CollatzResearch.WordTrace]
  refine ⟨18970371348697921439824217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12646914232465280959882811 18970371348697921439824217)
  ·
    refine ⟨14227778511523441079868163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18970371348697921439824217 14227778511523441079868163)
    ·
      refine ⟨21341667767285161619802245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14227778511523441079868163 21341667767285161619802245)
      ·
        refine ⟨4001562706365967803712921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21341667767285161619802245 4001562706365967803712921)
        ·
          refine ⟨3001172029774475852784691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4001562706365967803712921 3001172029774475852784691)
          ·
            refine ⟨4501758044661713779177037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3001172029774475852784691 4501758044661713779177037)
            ·
              refine ⟨1688159266748142667191389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4501758044661713779177037 1688159266748142667191389)
              ·
                refine ⟨633059725030553500196771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1688159266748142667191389 633059725030553500196771)
                ·
                  refine ⟨949589587545830250295157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 633059725030553500196771 949589587545830250295157)
                  ·
                    refine ⟨89024023832421585965171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 949589587545830250295157 89024023832421585965171)
                    ·
                      rfl

theorem cell23_520121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 5].length) (baseStart_520121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520121 prefixEnd_520121 := by exact prefixLift 520121
  have htrace : WordTrace (prefixWord ++ tailWord_520121) baseStart_520121 baseEnd_520121 := by
    simpa [prefixWord, tailWord_520121, baseEnd_520121] using wordTrace_append hprefix tailTrace_520121
  have hstable : (prefixWord ++ tailWord_520121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520121).length < 2 ^ (prefixWord ++ tailWord_520121).sum := by decide
  have hdescent : baseEnd_520121 < baseStart_520121 := by decide
  rcases family_descends (prefixWord ++ tailWord_520121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520144 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 5]
def baseStart_520144 : Nat := 118140960795 + 520144 * 2 ^ 59
def prefixEnd_520144 : Nat := 4983230072969 + 3 ^ 40 * 520144 * 2
def baseEnd_520144 : Nat := 267083881552318167907907

theorem tailTrace_520144 : CollatzResearch.WordTrace tailWord_520144 prefixEnd_520144 267083881552318167907907 := by
  unfold tailWord_520144
  simp only [CollatzResearch.WordTrace]
  refine ⟨9485605113807298183955743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12647473485076397578607657 9485605113807298183955743)
  ·
    refine ⟨14228407670710947275933615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9485605113807298183955743 14228407670710947275933615)
    ·
      refine ⟨21342611506066420913900423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14228407670710947275933615 21342611506066420913900423)
      ·
        refine ⟨32013917259099631370850635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21342611506066420913900423 32013917259099631370850635)
        ·
          refine ⟨48020875888649447056275953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32013917259099631370850635 48020875888649447056275953)
          ·
            refine ⟨36015656916487085292206965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48020875888649447056275953 36015656916487085292206965)
            ·
              refine ⟨3376467835920664246144403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36015656916487085292206965 3376467835920664246144403)
              ·
                refine ⟨5064701753880996369216605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376467835920664246144403 5064701753880996369216605)
                ·
                  refine ⟨1899263157705373638456227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5064701753880996369216605 1899263157705373638456227)
                  ·
                    refine ⟨2848894736558060457684341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1899263157705373638456227 2848894736558060457684341)
                    ·
                      refine ⟨267083881552318167907907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2848894736558060457684341 267083881552318167907907)
                      ·
                        rfl

theorem cell23_520144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_520144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520144 prefixEnd_520144 := by exact prefixLift 520144
  have htrace : WordTrace (prefixWord ++ tailWord_520144) baseStart_520144 baseEnd_520144 := by
    simpa [prefixWord, tailWord_520144, baseEnd_520144] using wordTrace_append hprefix tailTrace_520144
  have hstable : (prefixWord ++ tailWord_520144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520144).length < 2 ^ (prefixWord ++ tailWord_520144).sum := by decide
  have hdescent : baseEnd_520144 < baseStart_520144 := by decide
  rcases family_descends (prefixWord ++ tailWord_520144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520161 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 3, 2, 3]
def baseStart_520161 : Nat := 118140960795 + 520161 * 2 ^ 59
def prefixEnd_520161 : Nat := 4983230072969 + 3 ^ 40 * 520161 * 2
def baseEnd_520161 : Nat := 267092610723444601395329

theorem tailTrace_520161 : CollatzResearch.WordTrace tailWord_520161 prefixEnd_520161 267092610723444601395329 := by
  unfold tailWord_520161
  simp only [CollatzResearch.WordTrace]
  refine ⟨18971830268553008271280337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12647886845702005514186891 18971830268553008271280337)
  ·
    refine ⟨14228872701414756203460253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18971830268553008271280337 14228872701414756203460253)
    ·
      refine ⟨5335827263030533576297595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14228872701414756203460253 5335827263030533576297595)
      ·
        refine ⟨8003740894545800364446393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5335827263030533576297595 8003740894545800364446393)
        ·
          refine ⟨6002805670909350273334795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8003740894545800364446393 6002805670909350273334795)
          ·
            refine ⟨9004208506364025410002193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6002805670909350273334795 9004208506364025410002193)
            ·
              refine ⟨6753156379773019057501645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9004208506364025410002193 6753156379773019057501645)
              ·
                refine ⟨2532433642414882146563117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6753156379773019057501645 2532433642414882146563117)
                ·
                  refine ⟨949662615905580804961169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2532433642414882146563117 949662615905580804961169)
                  ·
                    refine ⟨712246961929185603720877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 949662615905580804961169 712246961929185603720877)
                    ·
                      refine ⟨267092610723444601395329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 712246961929185603720877 267092610723444601395329)
                      ·
                        rfl

theorem cell23_520161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_520161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520161 prefixEnd_520161 := by exact prefixLift 520161
  have htrace : WordTrace (prefixWord ++ tailWord_520161) baseStart_520161 baseEnd_520161 := by
    simpa [prefixWord, tailWord_520161, baseEnd_520161] using wordTrace_append hprefix tailTrace_520161
  have hstable : (prefixWord ++ tailWord_520161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520161).length < 2 ^ (prefixWord ++ tailWord_520161).sum := by decide
  have hdescent : baseEnd_520161 < baseStart_520161 := by decide
  rcases family_descends (prefixWord ++ tailWord_520161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520164 : List Nat := [2, 3, 1, 1, 1, 1, 5, 9]
def baseStart_520164 : Nat := 118140960795 + 520164 * 2 ^ 59
def prefixEnd_520164 : Nat := 4983230072969 + 3 ^ 40 * 520164 * 2
def baseEnd_520164 : Nat := 9892375969089188505845

theorem tailTrace_520164 : CollatzResearch.WordTrace tailWord_520164 prefixEnd_520164 9892375969089188505845 := by
  unfold tailWord_520164
  simp only [CollatzResearch.WordTrace]
  refine ⟨9485969843771069891819773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12647959791694759855759697 9485969843771069891819773)
  ·
    refine ⟨3557238691414151209432415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9485969843771069891819773 3557238691414151209432415)
    ·
      refine ⟨5335858037121226814148623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3557238691414151209432415 5335858037121226814148623)
      ·
        refine ⟨8003787055681840221222935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5335858037121226814148623 8003787055681840221222935)
        ·
          refine ⟨12005680583522760331834403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8003787055681840221222935 12005680583522760331834403)
          ·
            refine ⟨18008520875284140497751605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12005680583522760331834403 18008520875284140497751605)
            ·
              refine ⟨1688298832057888171664213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18008520875284140497751605 1688298832057888171664213)
              ·
                refine ⟨9892375969089188505845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1688298832057888171664213 9892375969089188505845)
                ·
                  rfl

theorem cell23_520164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 9].length) (baseStart_520164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520164 prefixEnd_520164 := by exact prefixLift 520164
  have htrace : WordTrace (prefixWord ++ tailWord_520164) baseStart_520164 baseEnd_520164 := by
    simpa [prefixWord, tailWord_520164, baseEnd_520164] using wordTrace_append hprefix tailTrace_520164
  have hstable : (prefixWord ++ tailWord_520164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520164).length < 2 ^ (prefixWord ++ tailWord_520164).sum := by decide
  have hdescent : baseEnd_520164 < baseStart_520164 := by decide
  rcases family_descends (prefixWord ++ tailWord_520164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520201 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 1, 9, 2]
def baseStart_520201 : Nat := 118140960795 + 520201 * 2 ^ 59
def prefixEnd_520201 : Nat := 4983230072969 + 3 ^ 40 * 520201 * 2
def baseEnd_520201 : Nat := 267113149949624444895145

theorem tailTrace_520201 : CollatzResearch.WordTrace tailWord_520201 prefixEnd_520201 267113149949624444895145 := by
  unfold tailWord_520201
  simp only [CollatzResearch.WordTrace]
  refine ⟨18973289188408095102736457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12648859458938730068490971 18973289188408095102736457)
  ·
    refine ⟨14229966891306071327052343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18973289188408095102736457 14229966891306071327052343)
    ·
      refine ⟨21344950336959106990578515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14229966891306071327052343 21344950336959106990578515)
      ·
        refine ⟨32017425505438660485867773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21344950336959106990578515 32017425505438660485867773)
        ·
          refine ⟨12006534564539497682200415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32017425505438660485867773 12006534564539497682200415)
          ·
            refine ⟨18009801846809246523300623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12006534564539497682200415 18009801846809246523300623)
            ·
              refine ⟨27014702770213869784950935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18009801846809246523300623 27014702770213869784950935)
              ·
                refine ⟨40522054155320804677426403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27014702770213869784950935 40522054155320804677426403)
                ·
                  refine ⟨60783081232981207016139605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40522054155320804677426403 60783081232981207016139605)
                  ·
                    refine ⟨356150866599499259860193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 60783081232981207016139605 356150866599499259860193)
                    ·
                      refine ⟨267113149949624444895145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 356150866599499259860193 267113149949624444895145)
                      ·
                        rfl

theorem cell23_520201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 9, 2].length) (baseStart_520201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520201 prefixEnd_520201 := by exact prefixLift 520201
  have htrace : WordTrace (prefixWord ++ tailWord_520201) baseStart_520201 baseEnd_520201 := by
    simpa [prefixWord, tailWord_520201, baseEnd_520201] using wordTrace_append hprefix tailTrace_520201
  have hstable : (prefixWord ++ tailWord_520201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520201).length < 2 ^ (prefixWord ++ tailWord_520201).sum := by decide
  have hdescent : baseEnd_520201 < baseStart_520201 := by decide
  rcases family_descends (prefixWord ++ tailWord_520201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520202 : List Nat := [3, 1, 2, 2, 4, 2, 2, 1, 2, 4]
def baseStart_520202 : Nat := 118140960795 + 520202 * 2 ^ 59
def prefixEnd_520202 : Nat := 4983230072969 + 3 ^ 40 * 520202 * 2
def baseEnd_520202 : Nat := 89037887810092980327547

theorem tailTrace_520202 : CollatzResearch.WordTrace tailWord_520202 prefixEnd_520202 89037887810092980327547 := by
  unfold tailWord_520202
  simp only [CollatzResearch.WordTrace]
  refine ⟨4743331415351118068380715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12648883774269648182348573 4743331415351118068380715)
  ·
    refine ⟨7114997123026677102571073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4743331415351118068380715 7114997123026677102571073)
    ·
      refine ⟨5336247842270007826928305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7114997123026677102571073 5336247842270007826928305)
      ·
        refine ⟨4002185881702505870196229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5336247842270007826928305 4002185881702505870196229)
        ·
          refine ⟨750409852819219850661793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4002185881702505870196229 750409852819219850661793)
          ·
            refine ⟨562807389614414887996345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 750409852819219850661793 562807389614414887996345)
            ·
              refine ⟨422105542210811165997259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562807389614414887996345 422105542210811165997259)
              ·
                refine ⟨633158313316216748995889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422105542210811165997259 633158313316216748995889)
                ·
                  refine ⟨474868734987162561746917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633158313316216748995889 474868734987162561746917)
                  ·
                    refine ⟨89037887810092980327547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 474868734987162561746917 89037887810092980327547)
                    ·
                      rfl

theorem cell23_520202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_520202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520202 prefixEnd_520202 := by exact prefixLift 520202
  have htrace : WordTrace (prefixWord ++ tailWord_520202) baseStart_520202 baseEnd_520202 := by
    simpa [prefixWord, tailWord_520202, baseEnd_520202] using wordTrace_append hprefix tailTrace_520202
  have hstable : (prefixWord ++ tailWord_520202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520202).length < 2 ^ (prefixWord ++ tailWord_520202).sum := by decide
  have hdescent : baseEnd_520202 < baseStart_520202 := by decide
  rcases family_descends (prefixWord ++ tailWord_520202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520208 : List Nat := [2, 1, 1, 1, 1, 1, 1, 9, 2, 1, 3]
def baseStart_520208 : Nat := 118140960795 + 520208 * 2 ^ 59
def prefixEnd_520208 : Nat := 4983230072969 + 3 ^ 40 * 520208 * 2
def baseEnd_520208 : Nat := 267116744314205917507613

theorem tailTrace_520208 : CollatzResearch.WordTrace tailWord_520208 prefixEnd_520208 267116744314205917507613 := by
  unfold tailWord_520208
  simp only [CollatzResearch.WordTrace]
  refine ⟨9486772249691367649120639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12649029666255156865494185 9486772249691367649120639)
  ·
    refine ⟨14230158374537051473680959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9486772249691367649120639 14230158374537051473680959)
    ·
      refine ⟨21345237561805577210521439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14230158374537051473680959 21345237561805577210521439)
      ·
        refine ⟨32017856342708365815782159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21345237561805577210521439 32017856342708365815782159)
        ·
          refine ⟨48026784514062548723673239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32017856342708365815782159 48026784514062548723673239)
          ·
            refine ⟨72040176771093823085509859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48026784514062548723673239 72040176771093823085509859)
            ·
              refine ⟨108060265156640734628264789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72040176771093823085509859 108060265156640734628264789)
              ·
                refine ⟨633165616152191804462489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 108060265156640734628264789 633165616152191804462489)
                ·
                  refine ⟨474874212114143853346867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633165616152191804462489 474874212114143853346867)
                  ·
                    refine ⟨712311318171215780020301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 474874212114143853346867 712311318171215780020301)
                    ·
                      refine ⟨267116744314205917507613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 712311318171215780020301 267116744314205917507613)
                      ·
                        rfl

theorem cell23_520208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 2, 1, 3].length) (baseStart_520208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520208 prefixEnd_520208 := by exact prefixLift 520208
  have htrace : WordTrace (prefixWord ++ tailWord_520208) baseStart_520208 baseEnd_520208 := by
    simpa [prefixWord, tailWord_520208, baseEnd_520208] using wordTrace_append hprefix tailTrace_520208
  have hstable : (prefixWord ++ tailWord_520208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520208).length < 2 ^ (prefixWord ++ tailWord_520208).sum := by decide
  have hdescent : baseEnd_520208 < baseStart_520208 := by decide
  rcases family_descends (prefixWord ++ tailWord_520208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520212 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_520212 : Nat := 118140960795 + 520212 * 2 ^ 59
def prefixEnd_520212 : Nat := 4983230072969 + 3 ^ 40 * 520212 * 2
def baseEnd_520212 : Nat := 267118798236823901857595

theorem tailTrace_520212 : CollatzResearch.WordTrace tailWord_520212 prefixEnd_520212 267118798236823901857595 := by
  unfold tailWord_520212
  simp only [CollatzResearch.WordTrace]
  refine ⟨9486845195684121990693445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12649126927578829320924593 9486845195684121990693445)
  ·
    refine ⟨1778783474190772873255021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9486845195684121990693445 1778783474190772873255021)
    ·
      refine ⟨667043802821539827470633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1778783474190772873255021 667043802821539827470633)
      ·
        refine ⟨500282852116154870602975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667043802821539827470633 500282852116154870602975)
        ·
          refine ⟨750424278174232305904463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500282852116154870602975 750424278174232305904463)
          ·
            refine ⟨1125636417261348458856695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750424278174232305904463 1125636417261348458856695)
            ·
              refine ⟨1688454625892022688285043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125636417261348458856695 1688454625892022688285043)
              ·
                refine ⟨2532681938838034032427565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1688454625892022688285043 2532681938838034032427565)
                ·
                  refine ⟨949755727064262762160337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2532681938838034032427565 949755727064262762160337)
                  ·
                    refine ⟨712316795298197071620253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 949755727064262762160337 712316795298197071620253)
                    ·
                      refine ⟨267118798236823901857595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 712316795298197071620253 267118798236823901857595)
                      ·
                        rfl

theorem cell23_520212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_520212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520212 prefixEnd_520212 := by exact prefixLift 520212
  have htrace : WordTrace (prefixWord ++ tailWord_520212) baseStart_520212 baseEnd_520212 := by
    simpa [prefixWord, tailWord_520212, baseEnd_520212] using wordTrace_append hprefix tailTrace_520212
  have hstable : (prefixWord ++ tailWord_520212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520212).length < 2 ^ (prefixWord ++ tailWord_520212).sum := by decide
  have hdescent : baseEnd_520212 < baseStart_520212 := by decide
  rcases family_descends (prefixWord ++ tailWord_520212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520265 : List Nat := [1, 2, 1, 1, 2, 2, 3, 5, 2, 2, 2]
def baseStart_520265 : Nat := 118140960795 + 520265 * 2 ^ 59
def prefixEnd_520265 : Nat := 4983230072969 + 3 ^ 40 * 520265 * 2
def baseEnd_520265 : Nat := 267146012711512194494851

theorem tailTrace_520265 : CollatzResearch.WordTrace tailWord_520265 prefixEnd_520265 267146012711512194494851 := by
  unfold tailWord_520265
  simp only [CollatzResearch.WordTrace]
  refine ⟨18975623460176234033066249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12650415640117489355377499 18975623460176234033066249)
  ·
    refine ⟨14231717595132175524799687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18975623460176234033066249 14231717595132175524799687)
    ·
      refine ⟨21347576392698263287199531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14231717595132175524799687 21347576392698263287199531)
      ·
        refine ⟨32021364589047394930799297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21347576392698263287199531 32021364589047394930799297)
        ·
          refine ⟨24016023441785546198099473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32021364589047394930799297 24016023441785546198099473)
          ·
            refine ⟨18012017581339159648574605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24016023441785546198099473 18012017581339159648574605)
            ·
              refine ⟨6754506593002184868215477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18012017581339159648574605 6754506593002184868215477)
              ·
                refine ⟨633234993093954831395201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6754506593002184868215477 633234993093954831395201)
                ·
                  refine ⟨474926244820466123546401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633234993093954831395201 474926244820466123546401)
                  ·
                    refine ⟨356194683615349592659801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 474926244820466123546401 356194683615349592659801)
                    ·
                      refine ⟨267146012711512194494851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 356194683615349592659801 267146012711512194494851)
                      ·
                        rfl

theorem cell23_520265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 2, 2].length) (baseStart_520265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520265 prefixEnd_520265 := by exact prefixLift 520265
  have htrace : WordTrace (prefixWord ++ tailWord_520265) baseStart_520265 baseEnd_520265 := by
    simpa [prefixWord, tailWord_520265, baseEnd_520265] using wordTrace_append hprefix tailTrace_520265
  have hstable : (prefixWord ++ tailWord_520265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520265).length < 2 ^ (prefixWord ++ tailWord_520265).sum := by decide
  have hdescent : baseEnd_520265 < baseStart_520265 := by decide
  rcases family_descends (prefixWord ++ tailWord_520265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520281 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 1, 5, 3]
def baseStart_520281 : Nat := 118140960795 + 520281 * 2 ^ 59
def prefixEnd_520281 : Nat := 4983230072969 + 3 ^ 40 * 520281 * 2
def baseEnd_520281 : Nat := 267154228401984131894777

theorem tailTrace_520281 : CollatzResearch.WordTrace tailWord_520281 prefixEnd_520281 267154228401984131894777 := by
  unfold tailWord_520281
  simp only [CollatzResearch.WordTrace]
  refine ⟨18976207028118268765648697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12650804685412179177099131 18976207028118268765648697)
  ·
    refine ⟨14232155271088701574236523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18976207028118268765648697 14232155271088701574236523)
    ·
      refine ⟨21348232906633052361354785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14232155271088701574236523 21348232906633052361354785)
      ·
        refine ⟨16011174679974789271016089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21348232906633052361354785 16011174679974789271016089)
        ·
          refine ⟨12008381009981091953262067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16011174679974789271016089 12008381009981091953262067)
          ·
            refine ⟨18012571514971637929893101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12008381009981091953262067 18012571514971637929893101)
            ·
              refine ⟨6754714318114364223709913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18012571514971637929893101 6754714318114364223709913)
              ·
                refine ⟨5066035738585773167782435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6754714318114364223709913 5066035738585773167782435)
                ·
                  refine ⟨7599053607878659751673653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5066035738585773167782435 7599053607878659751673653)
                  ·
                    refine ⟨712411275738624351719405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7599053607878659751673653 712411275738624351719405)
                    ·
                      refine ⟨267154228401984131894777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 712411275738624351719405 267154228401984131894777)
                      ·
                        rfl

theorem cell23_520281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_520281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520281 prefixEnd_520281 := by exact prefixLift 520281
  have htrace : WordTrace (prefixWord ++ tailWord_520281) baseStart_520281 baseEnd_520281 := by
    simpa [prefixWord, tailWord_520281, baseEnd_520281] using wordTrace_append hprefix tailTrace_520281
  have hstable : (prefixWord ++ tailWord_520281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520281).length < 2 ^ (prefixWord ++ tailWord_520281).sum := by decide
  have hdescent : baseEnd_520281 < baseStart_520281 := by decide
  rcases family_descends (prefixWord ++ tailWord_520281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520286 : List Nat := [4, 4, 1, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_520286 : Nat := 118140960795 + 520286 * 2 ^ 59
def prefixEnd_520286 : Nat := 4983230072969 + 3 ^ 40 * 520286 * 2
def baseEnd_520286 : Nat := 267156795805256612332255

theorem tailTrace_520286 : CollatzResearch.WordTrace tailWord_520286 prefixEnd_520286 267156795805256612332255 := by
  unfold tailWord_520286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2372048674137519327447589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12650926262066769746387141 2372048674137519327447589)
  ·
    refine ⟨444759126400784873896423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2372048674137519327447589 444759126400784873896423)
    ·
      refine ⟨667138689601177310844635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444759126400784873896423 667138689601177310844635)
      ·
        refine ⟨1000708034401765966266953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667138689601177310844635 1000708034401765966266953)
        ·
          refine ⟨750531025801324474700215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1000708034401765966266953 750531025801324474700215)
          ·
            refine ⟨1125796538701986712050323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750531025801324474700215 1125796538701986712050323)
            ·
              refine ⟨1688694808052980068075485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125796538701986712050323 1688694808052980068075485)
              ·
                refine ⟨633260553019867525528307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1688694808052980068075485 633260553019867525528307)
                ·
                  refine ⟨949890829529801288292461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 633260553019867525528307 949890829529801288292461)
                  ·
                    refine ⟨356209061073675483109673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 949890829529801288292461 356209061073675483109673)
                    ·
                      refine ⟨267156795805256612332255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 356209061073675483109673 267156795805256612332255)
                      ·
                        rfl

theorem cell23_520286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_520286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520286 prefixEnd_520286 := by exact prefixLift 520286
  have htrace : WordTrace (prefixWord ++ tailWord_520286) baseStart_520286 baseEnd_520286 := by
    simpa [prefixWord, tailWord_520286, baseEnd_520286] using wordTrace_append hprefix tailTrace_520286
  have hstable : (prefixWord ++ tailWord_520286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520286).length < 2 ^ (prefixWord ++ tailWord_520286).sum := by decide
  have hdescent : baseEnd_520286 < baseStart_520286 := by decide
  rcases family_descends (prefixWord ++ tailWord_520286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520288 : List Nat := [2, 1, 1, 3, 2, 3, 1, 5, 5]
def baseStart_520288 : Nat := 118140960795 + 520288 * 2 ^ 59
def prefixEnd_520288 : Nat := 4983230072969 + 3 ^ 40 * 520288 * 2
def baseEnd_520288 : Nat := 29684202529618400500805

theorem tailTrace_520288 : CollatzResearch.WordTrace tailWord_520288 prefixEnd_520288 29684202529618400500805 := by
  unfold tailWord_520288
  simp only [CollatzResearch.WordTrace]
  refine ⟨9488231169546454480576759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12650974892728605974102345 9488231169546454480576759)
  ·
    refine ⟨14232346754319681720865139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9488231169546454480576759 14232346754319681720865139)
    ·
      refine ⟨21348520131479522581297709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14232346754319681720865139 21348520131479522581297709)
      ·
        refine ⟨8005695049304820967986641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21348520131479522581297709 8005695049304820967986641)
        ·
          refine ⟨6004271286978615725989981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8005695049304820967986641 6004271286978615725989981)
          ·
            refine ⟨2251601732616980897246243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6004271286978615725989981 2251601732616980897246243)
            ·
              refine ⟨3377402598925471345869365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2251601732616980897246243 3377402598925471345869365)
              ·
                refine ⟨316631493649262938675253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3377402598925471345869365 316631493649262938675253)
                ·
                  refine ⟨29684202529618400500805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 316631493649262938675253 29684202529618400500805)
                  ·
                    rfl

theorem cell23_520288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 5].length) (baseStart_520288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520288 prefixEnd_520288 := by exact prefixLift 520288
  have htrace : WordTrace (prefixWord ++ tailWord_520288) baseStart_520288 baseEnd_520288 := by
    simpa [prefixWord, tailWord_520288, baseEnd_520288] using wordTrace_append hprefix tailTrace_520288
  have hstable : (prefixWord ++ tailWord_520288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520288).length < 2 ^ (prefixWord ++ tailWord_520288).sum := by decide
  have hdescent : baseEnd_520288 < baseStart_520288 := by decide
  rcases family_descends (prefixWord ++ tailWord_520288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520338 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_520338 : Nat := 118140960795 + 520338 * 2 ^ 59
def prefixEnd_520338 : Nat := 4983230072969 + 3 ^ 40 * 520338 * 2
def baseEnd_520338 : Nat := 267183496799290408882015

theorem tailTrace_520338 : CollatzResearch.WordTrace tailWord_520338 prefixEnd_520338 267183496799290408882015 := by
  unfold tailWord_520338
  simp only [CollatzResearch.WordTrace]
  refine ⟨4744571497227941875118417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12652190659274511666982445 4744571497227941875118417)
  ·
    refine ⟨3558428622920956406338813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4744571497227941875118417 3558428622920956406338813)
    ·
      refine ⟨1334410733595358652377055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3558428622920956406338813 1334410733595358652377055)
      ·
        refine ⟨2001616100393037978565583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1334410733595358652377055 2001616100393037978565583)
        ·
          refine ⟨3002424150589556967848375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2001616100393037978565583 3002424150589556967848375)
          ·
            refine ⟨4503636225884335451772563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3002424150589556967848375 4503636225884335451772563)
            ·
              refine ⟨6755454338826503177658845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4503636225884335451772563 6755454338826503177658845)
              ·
                refine ⟨2533295377059938691622067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6755454338826503177658845 2533295377059938691622067)
                ·
                  refine ⟨3799943065589908037433101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533295377059938691622067 3799943065589908037433101)
                  ·
                    refine ⟨1424978649596215514037413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3799943065589908037433101 1424978649596215514037413)
                    ·
                      refine ⟨267183496799290408882015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1424978649596215514037413 267183496799290408882015)
                      ·
                        rfl

theorem cell23_520338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_520338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520338 prefixEnd_520338 := by exact prefixLift 520338
  have htrace : WordTrace (prefixWord ++ tailWord_520338) baseStart_520338 baseEnd_520338 := by
    simpa [prefixWord, tailWord_520338, baseEnd_520338] using wordTrace_append hprefix tailTrace_520338
  have hstable : (prefixWord ++ tailWord_520338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520338).length < 2 ^ (prefixWord ++ tailWord_520338).sum := by decide
  have hdescent : baseEnd_520338 < baseStart_520338 := by decide
  rcases family_descends (prefixWord ++ tailWord_520338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520428 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 4]
def baseStart_520428 : Nat := 118140960795 + 520428 * 2 ^ 59
def prefixEnd_520428 : Nat := 4983230072969 + 3 ^ 40 * 520428 * 2
def baseEnd_520428 : Nat := 267229710058195056756601

theorem tailTrace_520428 : CollatzResearch.WordTrace tailWord_520428 prefixEnd_520428 267229710058195056756601 := by
  unfold tailWord_520428
  simp only [CollatzResearch.WordTrace]
  refine ⟨9490784279292856435624969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12654379039057141914166625 9490784279292856435624969)
  ·
    refine ⟨7118088209469642326718727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9490784279292856435624969 7118088209469642326718727)
    ·
      refine ⟨10677132314204463490078091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7118088209469642326718727 10677132314204463490078091)
      ·
        refine ⟨16015698471306695235117137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10677132314204463490078091 16015698471306695235117137)
        ·
          refine ⟨12011773853480021426337853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16015698471306695235117137 12011773853480021426337853)
          ·
            refine ⟨4504415195055008034876695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12011773853480021426337853 4504415195055008034876695)
            ·
              refine ⟨6756622792582512052315043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4504415195055008034876695 6756622792582512052315043)
              ·
                refine ⟨10134934188873768078472565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6756622792582512052315043 10134934188873768078472565)
                ·
                  refine ⟨950150080206915757356803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10134934188873768078472565 950150080206915757356803)
                  ·
                    refine ⟨1425225120310373636035205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 950150080206915757356803 1425225120310373636035205)
                    ·
                      refine ⟨267229710058195056756601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1425225120310373636035205 267229710058195056756601)
                      ·
                        rfl

theorem cell23_520428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_520428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520428 prefixEnd_520428 := by exact prefixLift 520428
  have htrace : WordTrace (prefixWord ++ tailWord_520428) baseStart_520428 baseEnd_520428 := by
    simpa [prefixWord, tailWord_520428, baseEnd_520428] using wordTrace_append hprefix tailTrace_520428
  have hstable : (prefixWord ++ tailWord_520428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520428).length < 2 ^ (prefixWord ++ tailWord_520428).sum := by decide
  have hdescent : baseEnd_520428 < baseStart_520428 := by decide
  rcases family_descends (prefixWord ++ tailWord_520428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520462 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2]
def baseStart_520462 : Nat := 118140960795 + 520462 * 2 ^ 59
def prefixEnd_520462 : Nat := 4983230072969 + 3 ^ 40 * 520462 * 2
def baseEnd_520462 : Nat := 267247168400447923731445

theorem tailTrace_520462 : CollatzResearch.WordTrace tailWord_520462 prefixEnd_520462 267247168400447923731445 := by
  unfold tailWord_520462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2372851080057817084748455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12655205760308357785325093 2372851080057817084748455)
  ·
    refine ⟨3559276620086725627122683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2372851080057817084748455 3559276620086725627122683)
    ·
      refine ⟨5338914930130088440684025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3559276620086725627122683 5338914930130088440684025)
      ·
        refine ⟨4004186197597566330513019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5338914930130088440684025 4004186197597566330513019)
        ·
          refine ⟨6006279296396349495769529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4004186197597566330513019 6006279296396349495769529)
          ·
            refine ⟨4504709472297262121827147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6006279296396349495769529 4504709472297262121827147)
            ·
              refine ⟨6757064208445893182740721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4504709472297262121827147 6757064208445893182740721)
              ·
                refine ⟨5067798156334419887055541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6757064208445893182740721 5067798156334419887055541)
                ·
                  refine ⟨475106077156351864411457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5067798156334419887055541 475106077156351864411457)
                  ·
                    refine ⟨356329557867263898308593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 475106077156351864411457 356329557867263898308593)
                    ·
                      refine ⟨267247168400447923731445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 356329557867263898308593 267247168400447923731445)
                      ·
                        rfl

theorem cell23_520462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_520462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520462 prefixEnd_520462 := by exact prefixLift 520462
  have htrace : WordTrace (prefixWord ++ tailWord_520462) baseStart_520462 baseEnd_520462 := by
    simpa [prefixWord, tailWord_520462, baseEnd_520462] using wordTrace_append hprefix tailTrace_520462
  have hstable : (prefixWord ++ tailWord_520462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520462).length < 2 ^ (prefixWord ++ tailWord_520462).sum := by decide
  have hdescent : baseEnd_520462 < baseStart_520462 := by decide
  rcases family_descends (prefixWord ++ tailWord_520462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520479 : List Nat := [1, 1, 2, 4, 3, 2, 2, 1, 3, 2, 2]
def baseStart_520479 : Nat := 118140960795 + 520479 * 2 ^ 59
def prefixEnd_520479 : Nat := 4983230072969 + 3 ^ 40 * 520479 * 2
def baseEnd_520479 : Nat := 267255897571574357218867

theorem tailTrace_520479 : CollatzResearch.WordTrace tailWord_520479 prefixEnd_520479 267255897571574357218867 := by
  unfold tailWord_520479
  simp only [CollatzResearch.WordTrace]
  refine ⟨18983428681400948581356491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12655619120933965720904327 18983428681400948581356491)
  ·
    refine ⟨28475143022101422872034737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18983428681400948581356491 28475143022101422872034737)
    ·
      refine ⟨21356357266576067154026053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28475143022101422872034737 21356357266576067154026053)
      ·
        refine ⟨4004316987483012591379885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21356357266576067154026053 4004316987483012591379885)
        ·
          refine ⟨1501618870306129721767457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4004316987483012591379885 1501618870306129721767457)
          ·
            refine ⟨1126214152729597291325593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1501618870306129721767457 1126214152729597291325593)
            ·
              refine ⟨844660614547197968494195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1126214152729597291325593 844660614547197968494195)
              ·
                refine ⟨1266990921820796952741293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 844660614547197968494195 1266990921820796952741293)
                ·
                  refine ⟨475121595682798857277985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1266990921820796952741293 475121595682798857277985)
                  ·
                    refine ⟨356341196762099142958489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 475121595682798857277985 356341196762099142958489)
                    ·
                      refine ⟨267255897571574357218867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 356341196762099142958489 267255897571574357218867)
                      ·
                        rfl

theorem cell23_520479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_520479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520479 prefixEnd_520479 := by exact prefixLift 520479
  have htrace : WordTrace (prefixWord ++ tailWord_520479) baseStart_520479 baseEnd_520479 := by
    simpa [prefixWord, tailWord_520479, baseEnd_520479] using wordTrace_append hprefix tailTrace_520479
  have hstable : (prefixWord ++ tailWord_520479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520479).length < 2 ^ (prefixWord ++ tailWord_520479).sum := by decide
  have hdescent : baseEnd_520479 < baseStart_520479 := by decide
  rcases family_descends (prefixWord ++ tailWord_520479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520495 : List Nat := [1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 3]
def baseStart_520495 : Nat := 118140960795 + 520495 * 2 ^ 59
def prefixEnd_520495 : Nat := 4983230072969 + 3 ^ 40 * 520495 * 2
def baseEnd_520495 : Nat := 267264113262046294618793

theorem tailTrace_520495 : CollatzResearch.WordTrace tailWord_520495 prefixEnd_520495 267264113262046294618793 := by
  unfold tailWord_520495
  simp only [CollatzResearch.WordTrace]
  refine ⟨18984012249342983313938939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12656008166228655542625959 18984012249342983313938939)
  ·
    refine ⟨28476018374014474970908409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18984012249342983313938939 28476018374014474970908409)
    ·
      refine ⟨21357013780510856228181307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28476018374014474970908409 21357013780510856228181307)
      ·
        refine ⟨32035520670766284342271961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21357013780510856228181307 32035520670766284342271961)
        ·
          refine ⟨24026640503074713256703971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32035520670766284342271961 24026640503074713256703971)
          ·
            refine ⟨36039960754612069885055957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24026640503074713256703971 36039960754612069885055957)
            ·
              refine ⟨844686580186220387930999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 36039960754612069885055957 844686580186220387930999)
              ·
                refine ⟨1267029870279330581896499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 844686580186220387930999 1267029870279330581896499)
                ·
                  refine ⟨1900544805418995872844749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1267029870279330581896499 1900544805418995872844749)
                  ·
                    refine ⟨712704302032123452316781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1900544805418995872844749 712704302032123452316781)
                    ·
                      refine ⟨267264113262046294618793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 712704302032123452316781 267264113262046294618793)
                      ·
                        rfl

theorem cell23_520495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 3].length) (baseStart_520495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520495 prefixEnd_520495 := by exact prefixLift 520495
  have htrace : WordTrace (prefixWord ++ tailWord_520495) baseStart_520495 baseEnd_520495 := by
    simpa [prefixWord, tailWord_520495, baseEnd_520495] using wordTrace_append hprefix tailTrace_520495
  have hstable : (prefixWord ++ tailWord_520495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520495).length < 2 ^ (prefixWord ++ tailWord_520495).sum := by decide
  have hdescent : baseEnd_520495 < baseStart_520495 := by decide
  rcases family_descends (prefixWord ++ tailWord_520495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520508 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_520508 : Nat := 118140960795 + 520508 * 2 ^ 59
def prefixEnd_520508 : Nat := 4983230072969 + 3 ^ 40 * 520508 * 2
def baseEnd_520508 : Nat := 267270788510554743756233

theorem tailTrace_520508 : CollatzResearch.WordTrace tailWord_520508 prefixEnd_520508 267270788510554743756233 := by
  unfold tailWord_520508
  simp only [CollatzResearch.WordTrace]
  refine ⟨9492243199147943267081089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12656324265530591022774785 9492243199147943267081089)
  ·
    refine ⟨7119182399360957450310817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9492243199147943267081089 7119182399360957450310817)
    ·
      refine ⟨5339386799520718087733113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7119182399360957450310817 5339386799520718087733113)
      ·
        refine ⟨4004540099640538565799835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5339386799520718087733113 4004540099640538565799835)
        ·
          refine ⟨6006810149460807848699753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4004540099640538565799835 6006810149460807848699753)
          ·
            refine ⟨4505107612095605886524815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6006810149460807848699753 4505107612095605886524815)
            ·
              refine ⟨6757661418143408829787223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4505107612095605886524815 6757661418143408829787223)
              ·
                refine ⟨10136492127215113244680835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6757661418143408829787223 10136492127215113244680835)
                ·
                  refine ⟨15204738190822669867021253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10136492127215113244680835 15204738190822669867021253)
                  ·
                    refine ⟨2850888410779250600066485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15204738190822669867021253 2850888410779250600066485)
                    ·
                      refine ⟨267270788510554743756233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2850888410779250600066485 267270788510554743756233)
                      ·
                        rfl

theorem cell23_520508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_520508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520508 prefixEnd_520508 := by exact prefixLift 520508
  have htrace : WordTrace (prefixWord ++ tailWord_520508) baseStart_520508 baseEnd_520508 := by
    simpa [prefixWord, tailWord_520508, baseEnd_520508] using wordTrace_append hprefix tailTrace_520508
  have hstable : (prefixWord ++ tailWord_520508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520508).length < 2 ^ (prefixWord ++ tailWord_520508).sum := by decide
  have hdescent : baseEnd_520508 < baseStart_520508 := by decide
  rcases family_descends (prefixWord ++ tailWord_520508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520538 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5]
def baseStart_520538 : Nat := 118140960795 + 520538 * 2 ^ 59
def prefixEnd_520538 : Nat := 4983230072969 + 3 ^ 40 * 520538 * 2
def baseEnd_520538 : Nat := 267286192930189626381095

theorem tailTrace_520538 : CollatzResearch.WordTrace tailWord_520538 prefixEnd_520538 267286192930189626381095 := by
  unfold tailWord_520538
  simp only [CollatzResearch.WordTrace]
  refine ⟨4746395147046800414438567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12657053725458134438502845 4746395147046800414438567)
  ·
    refine ⟨7119592720570200621657851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4746395147046800414438567 7119592720570200621657851)
    ·
      refine ⟨10679389080855300932486777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7119592720570200621657851 10679389080855300932486777)
      ·
        refine ⟨8009541810641475699365083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10679389080855300932486777 8009541810641475699365083)
        ·
          refine ⟨12014312715962213549047625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8009541810641475699365083 12014312715962213549047625)
          ·
            refine ⟨9010734536971660161785719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12014312715962213549047625 9010734536971660161785719)
            ·
              refine ⟨13516101805457490242678579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9010734536971660161785719 13516101805457490242678579)
              ·
                refine ⟨20274152708186235364017869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13516101805457490242678579 20274152708186235364017869)
                ·
                  refine ⟨7602807265569838261506701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20274152708186235364017869 7602807265569838261506701)
                  ·
                    refine ⟨2851052724588689348065013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7602807265569838261506701 2851052724588689348065013)
                    ·
                      refine ⟨267286192930189626381095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2851052724588689348065013 267286192930189626381095)
                      ·
                        rfl

theorem cell23_520538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_520538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520538 prefixEnd_520538 := by exact prefixLift 520538
  have htrace : WordTrace (prefixWord ++ tailWord_520538) baseStart_520538 baseEnd_520538 := by
    simpa [prefixWord, tailWord_520538, baseEnd_520538] using wordTrace_append hprefix tailTrace_520538
  have hstable : (prefixWord ++ tailWord_520538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520538).length < 2 ^ (prefixWord ++ tailWord_520538).sum := by decide
  have hdescent : baseEnd_520538 < baseStart_520538 := by decide
  rcases family_descends (prefixWord ++ tailWord_520538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520546 : List Nat := [3, 3, 2, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_520546 : Nat := 118140960795 + 520546 * 2 ^ 59
def prefixEnd_520546 : Nat := 4983230072969 + 3 ^ 40 * 520546 * 2
def baseEnd_520546 : Nat := 267290300775425595081059

theorem tailTrace_520546 : CollatzResearch.WordTrace tailWord_520546 prefixEnd_520546 267290300775425595081059 := by
  unfold tailWord_520546
  simp only [CollatzResearch.WordTrace]
  refine ⟨4746468093039554756011373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12657248248105479349363661 4746468093039554756011373)
  ·
    refine ⟨1779925534889833033504265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4746468093039554756011373 1779925534889833033504265)
    ·
      refine ⟨1334944151167374775128199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1779925534889833033504265 1334944151167374775128199)
      ·
        refine ⟨2002416226751062162692299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1334944151167374775128199 2002416226751062162692299)
        ·
          refine ⟨3003624340126593244038449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2002416226751062162692299 3003624340126593244038449)
          ·
            refine ⟨2252718255094944933028837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3003624340126593244038449 2252718255094944933028837)
            ·
              refine ⟨422384672830302174942907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2252718255094944933028837 422384672830302174942907)
              ·
                refine ⟨633577009245453262414361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422384672830302174942907 633577009245453262414361)
                ·
                  refine ⟨475182756934089946810771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633577009245453262414361 475182756934089946810771)
                  ·
                    refine ⟨712774135401134920216157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 475182756934089946810771 712774135401134920216157)
                    ·
                      refine ⟨267290300775425595081059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 712774135401134920216157 267290300775425595081059)
                      ·
                        rfl

theorem cell23_520546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_520546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520546 prefixEnd_520546 := by exact prefixLift 520546
  have htrace : WordTrace (prefixWord ++ tailWord_520546) baseStart_520546 baseEnd_520546 := by
    simpa [prefixWord, tailWord_520546, baseEnd_520546] using wordTrace_append hprefix tailTrace_520546
  have hstable : (prefixWord ++ tailWord_520546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520546).length < 2 ^ (prefixWord ++ tailWord_520546).sum := by decide
  have hdescent : baseEnd_520546 < baseStart_520546 := by decide
  rcases family_descends (prefixWord ++ tailWord_520546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520556 : List Nat := [2, 2, 1, 1, 6, 2, 1, 2, 1, 3, 2]
def baseStart_520556 : Nat := 118140960795 + 520556 * 2 ^ 59
def prefixEnd_520556 : Nat := 4983230072969 + 3 ^ 40 * 520556 * 2
def baseEnd_520556 : Nat := 267295435581970555956013

theorem tailTrace_520556 : CollatzResearch.WordTrace tailWord_520556 prefixEnd_520556 267295435581970555956013 := by
  unfold tailWord_520556
  simp only [CollatzResearch.WordTrace]
  refine ⟨9493118551060995365954761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12657491401414660487939681 9493118551060995365954761)
  ·
    refine ⟨7119838913295746524466071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9493118551060995365954761 7119838913295746524466071)
    ·
      refine ⟨10679758369943619786699107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7119838913295746524466071 10679758369943619786699107)
      ·
        refine ⟨16019637554915429680048661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10679758369943619786699107 16019637554915429680048661)
        ·
          refine ⟨750920510386660766252281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16019637554915429680048661 750920510386660766252281)
          ·
            refine ⟨563190382789995574689211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 750920510386660766252281 563190382789995574689211)
            ·
              refine ⟨844785574184993362033817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563190382789995574689211 844785574184993362033817)
              ·
                refine ⟨633589180638745021525363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844785574184993362033817 633589180638745021525363)
                ·
                  refine ⟨950383770958117532288045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 633589180638745021525363 950383770958117532288045)
                  ·
                    refine ⟨356393914109294074608017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 950383770958117532288045 356393914109294074608017)
                    ·
                      refine ⟨267295435581970555956013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 356393914109294074608017 267295435581970555956013)
                      ·
                        rfl

theorem cell23_520556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 3, 2].length) (baseStart_520556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520556 prefixEnd_520556 := by exact prefixLift 520556
  have htrace : WordTrace (prefixWord ++ tailWord_520556) baseStart_520556 baseEnd_520556 := by
    simpa [prefixWord, tailWord_520556, baseEnd_520556] using wordTrace_append hprefix tailTrace_520556
  have hstable : (prefixWord ++ tailWord_520556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520556).length < 2 ^ (prefixWord ++ tailWord_520556).sum := by decide
  have hdescent : baseEnd_520556 < baseStart_520556 := by decide
  rcases family_descends (prefixWord ++ tailWord_520556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520602 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3]
def baseStart_520602 : Nat := 118140960795 + 520602 * 2 ^ 59
def prefixEnd_520602 : Nat := 4983230072969 + 3 ^ 40 * 520602 * 2
def baseEnd_520602 : Nat := 267319055692077375980801

theorem tailTrace_520602 : CollatzResearch.WordTrace tailWord_520602 prefixEnd_520602 267319055692077375980801 := by
  unfold tailWord_520602
  simp only [CollatzResearch.WordTrace]
  refine ⟨4746978714988835147021015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12658609906636893725389373 4746978714988835147021015)
  ·
    refine ⟨7120468072483252720531523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4746978714988835147021015 7120468072483252720531523)
    ·
      refine ⟨10680702108724879080797285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7120468072483252720531523 10680702108724879080797285)
      ·
        refine ⟨2002631645385914827649491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10680702108724879080797285 2002631645385914827649491)
        ·
          refine ⟨3003947468078872241474237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2002631645385914827649491 3003947468078872241474237)
          ·
            refine ⟨1126480300529577090552839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3003947468078872241474237 1126480300529577090552839)
            ·
              refine ⟨1689720450794365635829259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1126480300529577090552839 1689720450794365635829259)
              ·
                refine ⟨2534580676191548453743889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1689720450794365635829259 2534580676191548453743889)
                ·
                  refine ⟨1900935507143661340307917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2534580676191548453743889 1900935507143661340307917)
                  ·
                    refine ⟨712850815178873002615469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1900935507143661340307917 712850815178873002615469)
                    ·
                      refine ⟨267319055692077375980801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 712850815178873002615469 267319055692077375980801)
                      ·
                        rfl

theorem cell23_520602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_520602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520602 prefixEnd_520602 := by exact prefixLift 520602
  have htrace : WordTrace (prefixWord ++ tailWord_520602) baseStart_520602 baseEnd_520602 := by
    simpa [prefixWord, tailWord_520602, baseEnd_520602] using wordTrace_append hprefix tailTrace_520602
  have hstable : (prefixWord ++ tailWord_520602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520602).length < 2 ^ (prefixWord ++ tailWord_520602).sum := by decide
  have hdescent : baseEnd_520602 < baseStart_520602 := by decide
  rcases family_descends (prefixWord ++ tailWord_520602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520686 : List Nat := [4, 1, 2, 1, 2, 2, 3, 3, 1, 4]
def baseStart_520686 : Nat := 118140960795 + 520686 * 2 ^ 59
def prefixEnd_520686 : Nat := 4983230072969 + 3 ^ 40 * 520686 * 2
def baseEnd_520686 : Nat := 89120729355685015776805

theorem tailTrace_520686 : CollatzResearch.WordTrace tailWord_520686 prefixEnd_520686 89120729355685015776805 := by
  unfold tailWord_520686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2373872323956377866767739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12660652394434015289427941 2373872323956377866767739)
  ·
    refine ⟨3560808485934566800151609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2373872323956377866767739 3560808485934566800151609)
    ·
      refine ⟨2670606364450925100113707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3560808485934566800151609 2670606364450925100113707)
      ·
        refine ⟨4005909546676387650170561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2670606364450925100113707 4005909546676387650170561)
        ·
          refine ⟨3004432160007290737627921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4005909546676387650170561 3004432160007290737627921)
          ·
            refine ⟨2253324120005468053220941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3004432160007290737627921 2253324120005468053220941)
            ·
              refine ⟨844996545002050519957853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2253324120005468053220941 844996545002050519957853)
              ·
                refine ⟨316873704375768944984195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 844996545002050519957853 316873704375768944984195)
                ·
                  refine ⟨475310556563653417476293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316873704375768944984195 475310556563653417476293)
                  ·
                    refine ⟨89120729355685015776805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 475310556563653417476293 89120729355685015776805)
                    ·
                      rfl

theorem cell23_520686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_520686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520686 prefixEnd_520686 := by exact prefixLift 520686
  have htrace : WordTrace (prefixWord ++ tailWord_520686) baseStart_520686 baseEnd_520686 := by
    simpa [prefixWord, tailWord_520686, baseEnd_520686] using wordTrace_append hprefix tailTrace_520686
  have hstable : (prefixWord ++ tailWord_520686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520686).length < 2 ^ (prefixWord ++ tailWord_520686).sum := by decide
  have hdescent : baseEnd_520686 < baseStart_520686 := by decide
  rcases family_descends (prefixWord ++ tailWord_520686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520709 : List Nat := [1, 3, 1, 1, 2, 2, 5, 1, 3, 1, 3]
def baseStart_520709 : Nat := 118140960795 + 520709 * 2 ^ 59
def prefixEnd_520709 : Nat := 4983230072969 + 3 ^ 40 * 520709 * 2
def baseEnd_520709 : Nat := 267373998122108457342809

theorem tailTrace_520709 : CollatzResearch.WordTrace tailWord_520709 prefixEnd_520709 267373998122108457342809 := by
  unfold tailWord_520709
  simp only [CollatzResearch.WordTrace]
  refine ⟨18991817470567697862229181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12661211647045131908152787 18991817470567697862229181)
  ·
    refine ⟨7121931551462886698335943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18991817470567697862229181 7121931551462886698335943)
    ·
      refine ⟨10682897327194330047503915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7121931551462886698335943 10682897327194330047503915)
      ·
        refine ⟨16024345990791495071255873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10682897327194330047503915 16024345990791495071255873)
        ·
          refine ⟨12018259493093621303441905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16024345990791495071255873 12018259493093621303441905)
          ·
            refine ⟨9013694619820215977581429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12018259493093621303441905 9013694619820215977581429)
            ·
              refine ⟨845033870608145247898259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9013694619820215977581429 845033870608145247898259)
              ·
                refine ⟨1267550805912217871847389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 845033870608145247898259 1267550805912217871847389)
                ·
                  refine ⟨475331552217081701942771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1267550805912217871847389 475331552217081701942771)
                  ·
                    refine ⟨712997328325622552914157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 475331552217081701942771 712997328325622552914157)
                    ·
                      refine ⟨267373998122108457342809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 712997328325622552914157 267373998122108457342809)
                      ·
                        rfl

theorem cell23_520709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 1, 3].length) (baseStart_520709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520709 prefixEnd_520709 := by exact prefixLift 520709
  have htrace : WordTrace (prefixWord ++ tailWord_520709) baseStart_520709 baseEnd_520709 := by
    simpa [prefixWord, tailWord_520709, baseEnd_520709] using wordTrace_append hprefix tailTrace_520709
  have hstable : (prefixWord ++ tailWord_520709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520709).length < 2 ^ (prefixWord ++ tailWord_520709).sum := by decide
  have hdescent : baseEnd_520709 < baseStart_520709 := by decide
  rcases family_descends (prefixWord ++ tailWord_520709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520746 : List Nat := [3, 1, 4, 1, 1, 3, 3, 1, 1, 5]
def baseStart_520746 : Nat := 118140960795 + 520746 * 2 ^ 59
def prefixEnd_520746 : Nat := 4983230072969 + 3 ^ 40 * 520746 * 2
def baseEnd_520746 : Nat := 89130998968774937526713

theorem tailTrace_520746 : CollatzResearch.WordTrace tailWord_520746 prefixEnd_520746 89130998968774937526713 := by
  unfold tailWord_520746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4748291742858413295331523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12662111314289102120884061 4748291742858413295331523)
  ·
    refine ⟨7122437614287619942997285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4748291742858413295331523 7122437614287619942997285)
    ·
      refine ⟨1335457052678928739311991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7122437614287619942997285 1335457052678928739311991)
      ·
        refine ⟨2003185579018393108967987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1335457052678928739311991 2003185579018393108967987)
        ·
          refine ⟨3004778368527589663451981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003185579018393108967987 3004778368527589663451981)
          ·
            refine ⟨1126791888197846123794493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3004778368527589663451981 1126791888197846123794493)
            ·
              refine ⟨422546958074192296422935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1126791888197846123794493 422546958074192296422935)
              ·
                refine ⟨633820437111288444634403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422546958074192296422935 633820437111288444634403)
                ·
                  refine ⟨950730655666932666951605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 633820437111288444634403 950730655666932666951605)
                  ·
                    refine ⟨89130998968774937526713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 950730655666932666951605 89130998968774937526713)
                    ·
                      rfl

theorem cell23_520746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_520746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520746 prefixEnd_520746 := by exact prefixLift 520746
  have htrace : WordTrace (prefixWord ++ tailWord_520746) baseStart_520746 baseEnd_520746 := by
    simpa [prefixWord, tailWord_520746, baseEnd_520746] using wordTrace_append hprefix tailTrace_520746
  have hstable : (prefixWord ++ tailWord_520746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520746).length < 2 ^ (prefixWord ++ tailWord_520746).sum := by decide
  have hdescent : baseEnd_520746 < baseStart_520746 := by decide
  rcases family_descends (prefixWord ++ tailWord_520746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520752 : List Nat := [2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 5]
def baseStart_520752 : Nat := 118140960795 + 520752 * 2 ^ 59
def prefixEnd_520752 : Nat := 4983230072969 + 3 ^ 40 * 520752 * 2
def baseEnd_520752 : Nat := 267396077790251789105111

theorem tailTrace_520752 : CollatzResearch.WordTrace tailWord_520752 prefixEnd_520752 267396077790251789105111 := by
  unfold tailWord_520752
  simp only [CollatzResearch.WordTrace]
  refine ⟨9496692904705958103022255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12662257206274610804029673 9496692904705958103022255)
  ·
    refine ⟨14245039357058937154533383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9496692904705958103022255 14245039357058937154533383)
    ·
      refine ⟨21367559035588405731800075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14245039357058937154533383 21367559035588405731800075)
      ·
        refine ⟨32051338553382608597700113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21367559035588405731800075 32051338553382608597700113)
        ·
          refine ⟨24038503915036956448275085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32051338553382608597700113 24038503915036956448275085)
          ·
            refine ⟨9014438968138858668103157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24038503915036956448275085 9014438968138858668103157)
            ·
              refine ⟨845103653263018000134671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9014438968138858668103157 845103653263018000134671)
              ·
                refine ⟨1267655479894527000202007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 845103653263018000134671 1267655479894527000202007)
                ·
                  refine ⟨1901483219841790500303011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1267655479894527000202007 1901483219841790500303011)
                  ·
                    refine ⟨2852224829762685750454517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1901483219841790500303011 2852224829762685750454517)
                    ·
                      refine ⟨267396077790251789105111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2852224829762685750454517 267396077790251789105111)
                      ·
                        rfl

theorem cell23_520752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 5].length) (baseStart_520752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520752 prefixEnd_520752 := by exact prefixLift 520752
  have htrace : WordTrace (prefixWord ++ tailWord_520752) baseStart_520752 baseEnd_520752 := by
    simpa [prefixWord, tailWord_520752, baseEnd_520752] using wordTrace_append hprefix tailTrace_520752
  have hstable : (prefixWord ++ tailWord_520752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520752).length < 2 ^ (prefixWord ++ tailWord_520752).sum := by decide
  have hdescent : baseEnd_520752 < baseStart_520752 := by decide
  rcases family_descends (prefixWord ++ tailWord_520752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520759 : List Nat := [1, 1, 3, 1, 2, 3, 4, 2, 2, 4]
def baseStart_520759 : Nat := 118140960795 + 520759 * 2 ^ 59
def prefixEnd_520759 : Nat := 4983230072969 + 3 ^ 40 * 520759 * 2
def baseEnd_520759 : Nat := 89133224051611087239193

theorem tailTrace_520759 : CollatzResearch.WordTrace tailWord_520759 prefixEnd_520759 89133224051611087239193 := by
  unfold tailWord_520759
  simp only [CollatzResearch.WordTrace]
  refine ⟨18993641120386556401549331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12662427413591037601032887 18993641120386556401549331)
  ·
    refine ⟨28490461680579834602323997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18993641120386556401549331 28490461680579834602323997)
    ·
      refine ⟨10683923130217437975871499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28490461680579834602323997 10683923130217437975871499)
      ·
        refine ⟨16025884695326156963807249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10683923130217437975871499 16025884695326156963807249)
        ·
          refine ⟨12019413521494617722855437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16025884695326156963807249 12019413521494617722855437)
          ·
            refine ⟨4507280070560481646070789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12019413521494617722855437 4507280070560481646070789)
            ·
              refine ⟨845115013230090308638273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4507280070560481646070789 845115013230090308638273)
              ·
                refine ⟨633836259922567731478705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 845115013230090308638273 633836259922567731478705)
                ·
                  refine ⟨475377194941925798609029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633836259922567731478705 475377194941925798609029)
                  ·
                    refine ⟨89133224051611087239193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 475377194941925798609029 89133224051611087239193)
                    ·
                      rfl

theorem cell23_520759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_520759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520759 prefixEnd_520759 := by exact prefixLift 520759
  have htrace : WordTrace (prefixWord ++ tailWord_520759) baseStart_520759 baseEnd_520759 := by
    simpa [prefixWord, tailWord_520759, baseEnd_520759] using wordTrace_append hprefix tailTrace_520759
  have hstable : (prefixWord ++ tailWord_520759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520759).length < 2 ^ (prefixWord ++ tailWord_520759).sum := by decide
  have hdescent : baseEnd_520759 < baseStart_520759 := by decide
  rcases family_descends (prefixWord ++ tailWord_520759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520769 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_520769 : Nat := 118140960795 + 520769 * 2 ^ 59
def prefixEnd_520769 : Nat := 4983230072969 + 3 ^ 40 * 520769 * 2
def baseEnd_520769 : Nat := 267404806961378222592533

theorem tailTrace_520769 : CollatzResearch.WordTrace tailWord_520769 prefixEnd_520769 267404806961378222592533 := by
  unfold tailWord_520769
  simp only [CollatzResearch.WordTrace]
  refine ⟨18994005850350328109413361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12662670566900218739608907 18994005850350328109413361)
  ·
    refine ⟨14245504387762746082060021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18994005850350328109413361 14245504387762746082060021)
    ·
      refine ⟨1335516036352757445193127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14245504387762746082060021 1335516036352757445193127)
      ·
        refine ⟨2003274054529136167789691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1335516036352757445193127 2003274054529136167789691)
        ·
          refine ⟨3004911081793704251684537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003274054529136167789691 3004911081793704251684537)
          ·
            refine ⟨2253683311345278188763403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3004911081793704251684537 2253683311345278188763403)
            ·
              refine ⟨3380524967017917283145105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2253683311345278188763403 3380524967017917283145105)
              ·
                refine ⟨2535393725263437962358829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3380524967017917283145105 2535393725263437962358829)
                ·
                  refine ⟨950772646973789235884561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2535393725263437962358829 950772646973789235884561)
                  ·
                    refine ⟨713079485230341926913421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 950772646973789235884561 713079485230341926913421)
                    ·
                      refine ⟨267404806961378222592533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 713079485230341926913421 267404806961378222592533)
                      ·
                        rfl

theorem cell23_520769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_520769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520769 prefixEnd_520769 := by exact prefixLift 520769
  have htrace : WordTrace (prefixWord ++ tailWord_520769) baseStart_520769 baseEnd_520769 := by
    simpa [prefixWord, tailWord_520769, baseEnd_520769] using wordTrace_append hprefix tailTrace_520769
  have hstable : (prefixWord ++ tailWord_520769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520769).length < 2 ^ (prefixWord ++ tailWord_520769).sum := by decide
  have hdescent : baseEnd_520769 < baseStart_520769 := by decide
  rcases family_descends (prefixWord ++ tailWord_520769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520816 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 4, 1, 3]
def baseStart_520816 : Nat := 118140960795 + 520816 * 2 ^ 59
def prefixEnd_520816 : Nat := 4983230072969 + 3 ^ 40 * 520816 * 2
def baseEnd_520816 : Nat := 267428940552139538704817

theorem tailTrace_520816 : CollatzResearch.WordTrace tailWord_520816 prefixEnd_520816 267428940552139538704817 := by
  unfold tailWord_520816
  simp only [CollatzResearch.WordTrace]
  refine ⟨9497860040590027568187151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12663813387453370090916201 9497860040590027568187151)
  ·
    refine ⟨14246790060885041352280727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9497860040590027568187151 14246790060885041352280727)
    ·
      refine ⟨21370185091327562028421091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14246790060885041352280727 21370185091327562028421091)
      ·
        refine ⟨32055277636991343042631637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21370185091327562028421091 32055277636991343042631637)
        ·
          refine ⟨751295569616984602561679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 32055277636991343042631637 751295569616984602561679)
          ·
            refine ⟨1126943354425476903842519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751295569616984602561679 1126943354425476903842519)
            ·
              refine ⟨1690415031638215355763779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1126943354425476903842519 1690415031638215355763779)
              ·
                refine ⟨2535622547457323033645669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1690415031638215355763779 2535622547457323033645669)
                ·
                  refine ⟨475429227648248068808563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2535622547457323033645669 475429227648248068808563)
                  ·
                    refine ⟨713143841472372103212845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 475429227648248068808563 713143841472372103212845)
                    ·
                      refine ⟨267428940552139538704817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 713143841472372103212845 267428940552139538704817)
                      ·
                        rfl

theorem cell23_520816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 4, 1, 3].length) (baseStart_520816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520816 prefixEnd_520816 := by exact prefixLift 520816
  have htrace : WordTrace (prefixWord ++ tailWord_520816) baseStart_520816 baseEnd_520816 := by
    simpa [prefixWord, tailWord_520816, baseEnd_520816] using wordTrace_append hprefix tailTrace_520816
  have hstable : (prefixWord ++ tailWord_520816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520816).length < 2 ^ (prefixWord ++ tailWord_520816).sum := by decide
  have hdescent : baseEnd_520816 < baseStart_520816 := by decide
  rcases family_descends (prefixWord ++ tailWord_520816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520832 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 2, 6]
def baseStart_520832 : Nat := 118140960795 + 520832 * 2 ^ 59
def prefixEnd_520832 : Nat := 4983230072969 + 3 ^ 40 * 520832 * 2
def baseEnd_520832 : Nat := 89145718747537158701581

theorem tailTrace_520832 : CollatzResearch.WordTrace tailWord_520832 prefixEnd_520832 89145718747537158701581 := by
  unfold tailWord_520832
  simp only [CollatzResearch.WordTrace]
  refine ⟨9498151824561044934478375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12664202432748059912637833 9498151824561044934478375)
  ·
    refine ⟨14247227736841567401717563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9498151824561044934478375 14247227736841567401717563)
    ·
      refine ⟨21370841605262351102576345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14247227736841567401717563 21370841605262351102576345)
      ·
        refine ⟨16028131203946763326932259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21370841605262351102576345 16028131203946763326932259)
        ·
          refine ⟨24042196805920144990398389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16028131203946763326932259 24042196805920144990398389)
          ·
            refine ⟨2253955950555013592849849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24042196805920144990398389 2253955950555013592849849)
            ·
              refine ⟨1690466962916260194637387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2253955950555013592849849 1690466962916260194637387)
              ·
                refine ⟨2535700444374390291956081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1690466962916260194637387 2535700444374390291956081)
                ·
                  refine ⟨1901775333280792718967061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2535700444374390291956081 1901775333280792718967061)
                  ·
                    refine ⟨89145718747537158701581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1901775333280792718967061 89145718747537158701581)
                    ·
                      rfl

theorem cell23_520832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 2, 6].length) (baseStart_520832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520832 prefixEnd_520832 := by exact prefixLift 520832
  have htrace : WordTrace (prefixWord ++ tailWord_520832) baseStart_520832 baseEnd_520832 := by
    simpa [prefixWord, tailWord_520832, baseEnd_520832] using wordTrace_append hprefix tailTrace_520832
  have hstable : (prefixWord ++ tailWord_520832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520832).length < 2 ^ (prefixWord ++ tailWord_520832).sum := by decide
  have hdescent : baseEnd_520832 < baseStart_520832 := by decide
  rcases family_descends (prefixWord ++ tailWord_520832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520833 : List Nat := [1, 2, 4, 2, 1, 1, 5, 1, 2, 1, 3]
def baseStart_520833 : Nat := 118140960795 + 520833 * 2 ^ 59
def prefixEnd_520833 : Nat := 4983230072969 + 3 ^ 40 * 520833 * 2
def baseEnd_520833 : Nat := 267437669723265972192239

theorem tailTrace_520833 : CollatzResearch.WordTrace tailWord_520833 prefixEnd_520833 267437669723265972192239 := by
  unfold tailWord_520833
  simp only [CollatzResearch.WordTrace]
  refine ⟨18996340122118467039743153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12664226748078978026495435 18996340122118467039743153)
  ·
    refine ⟨14247255091588850279807365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18996340122118467039743153 14247255091588850279807365)
    ·
      refine ⟨2671360329672909427463881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14247255091588850279807365 2671360329672909427463881)
      ·
        refine ⟨2003520247254682070597911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2671360329672909427463881 2003520247254682070597911)
        ·
          refine ⟨3005280370882023105896867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003520247254682070597911 3005280370882023105896867)
          ·
            refine ⟨4507920556323034658845301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3005280370882023105896867 4507920556323034658845301)
            ·
              refine ⟨422617552155284499266747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4507920556323034658845301 422617552155284499266747)
              ·
                refine ⟨633926328232926748900121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422617552155284499266747 633926328232926748900121)
                ·
                  refine ⟨475444746174695061675091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633926328232926748900121 475444746174695061675091)
                  ·
                    refine ⟨713167119262042592512637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 475444746174695061675091 713167119262042592512637)
                    ·
                      refine ⟨267437669723265972192239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 713167119262042592512637 267437669723265972192239)
                      ·
                        rfl

theorem cell23_520833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_520833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520833 prefixEnd_520833 := by exact prefixLift 520833
  have htrace : WordTrace (prefixWord ++ tailWord_520833) baseStart_520833 baseEnd_520833 := by
    simpa [prefixWord, tailWord_520833, baseEnd_520833] using wordTrace_append hprefix tailTrace_520833
  have hstable : (prefixWord ++ tailWord_520833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520833).length < 2 ^ (prefixWord ++ tailWord_520833).sum := by decide
  have hdescent : baseEnd_520833 < baseStart_520833 := by decide
  rcases family_descends (prefixWord ++ tailWord_520833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520856 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 6, 2, 2]
def baseStart_520856 : Nat := 118140960795 + 520856 * 2 ^ 59
def prefixEnd_520856 : Nat := 4983230072969 + 3 ^ 40 * 520856 * 2
def baseEnd_520856 : Nat := 267449479778319382204633

theorem tailTrace_520856 : CollatzResearch.WordTrace tailWord_520856 prefixEnd_520856 267449479778319382204633 := by
  unfold tailWord_520856
  simp only [CollatzResearch.WordTrace]
  refine ⟨9498589500517570983915211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12664786000690094645220281 9498589500517570983915211)
  ·
    refine ⟨14247884250776356475872817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9498589500517570983915211 14247884250776356475872817)
    ·
      refine ⟨10685913188082267356904613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14247884250776356475872817 10685913188082267356904613)
      ·
        refine ⟨2003608722765425129419615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10685913188082267356904613 2003608722765425129419615)
        ·
          refine ⟨3005413084148137694129423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003608722765425129419615 3005413084148137694129423)
          ·
            refine ⟨4508119626222206541194135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3005413084148137694129423 4508119626222206541194135)
            ·
              refine ⟨6762179439333309811791203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4508119626222206541194135 6762179439333309811791203)
              ·
                refine ⟨10143269158999964717686805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6762179439333309811791203 10143269158999964717686805)
                ·
                  refine ⟨475465741828123346141569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10143269158999964717686805 475465741828123346141569)
                  ·
                    refine ⟨356599306371092509606177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 475465741828123346141569 356599306371092509606177)
                    ·
                      refine ⟨267449479778319382204633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 356599306371092509606177 267449479778319382204633)
                      ·
                        rfl

theorem cell23_520856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_520856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520856 prefixEnd_520856 := by exact prefixLift 520856
  have htrace : WordTrace (prefixWord ++ tailWord_520856) baseStart_520856 baseEnd_520856 := by
    simpa [prefixWord, tailWord_520856, baseEnd_520856] using wordTrace_append hprefix tailTrace_520856
  have hstable : (prefixWord ++ tailWord_520856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520856).length < 2 ^ (prefixWord ++ tailWord_520856).sum := by decide
  have hdescent : baseEnd_520856 < baseStart_520856 := by decide
  rcases family_descends (prefixWord ++ tailWord_520856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520879 : List Nat := [1, 1, 2, 1, 2, 7, 1, 1, 7]
def baseStart_520879 : Nat := 118140960795 + 520879 * 2 ^ 59
def prefixEnd_520879 : Nat := 4983230072969 + 3 ^ 40 * 520879 * 2
def baseEnd_520879 : Nat := 29717921092596976913003

theorem tailTrace_520879 : CollatzResearch.WordTrace tailWord_520879 prefixEnd_520879 29717921092596976913003 := by
  unfold tailWord_520879
  simp only [CollatzResearch.WordTrace]
  refine ⟨18998017879951816895917691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12665345253301211263945127 18998017879951816895917691)
  ·
    refine ⟨28497026819927725343876537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18998017879951816895917691 28497026819927725343876537)
    ·
      refine ⟨21372770114945794007907403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28497026819927725343876537 21372770114945794007907403)
      ·
        refine ⟨32059155172418691011861105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21372770114945794007907403 32059155172418691011861105)
        ·
          refine ⟨24044366379314018258895829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32059155172418691011861105 24044366379314018258895829)
          ·
            refine ⟨563539837015172302942871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 24044366379314018258895829 563539837015172302942871)
            ·
              refine ⟨845309755522758454414307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563539837015172302942871 845309755522758454414307)
              ·
                refine ⟨1267964633284137681621461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 845309755522758454414307 1267964633284137681621461)
                ·
                  refine ⟨29717921092596976913003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1267964633284137681621461 29717921092596976913003)
                  ·
                    rfl

theorem cell23_520879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 7].length) (baseStart_520879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520879 prefixEnd_520879 := by exact prefixLift 520879
  have htrace : WordTrace (prefixWord ++ tailWord_520879) baseStart_520879 baseEnd_520879 := by
    simpa [prefixWord, tailWord_520879, baseEnd_520879] using wordTrace_append hprefix tailTrace_520879
  have hstable : (prefixWord ++ tailWord_520879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520879).length < 2 ^ (prefixWord ++ tailWord_520879).sum := by decide
  have hdescent : baseEnd_520879 < baseStart_520879 := by decide
  rcases family_descends (prefixWord ++ tailWord_520879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520912 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 4]
def baseStart_520912 : Nat := 118140960795 + 520912 * 2 ^ 59
def prefixEnd_520912 : Nat := 4983230072969 + 3 ^ 40 * 520912 * 2
def baseEnd_520912 : Nat := 267478234694971163104375

theorem tailTrace_520912 : CollatzResearch.WordTrace tailWord_520912 prefixEnd_520912 267478234694971163104375 := by
  unfold tailWord_520912
  simp only [CollatzResearch.WordTrace]
  refine ⟨9499610744416131765934495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12666147659221509021245993 9499610744416131765934495)
  ·
    refine ⟨14249416116624197648901743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9499610744416131765934495 14249416116624197648901743)
    ·
      refine ⟨21374124174936296473352615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14249416116624197648901743 21374124174936296473352615)
      ·
        refine ⟨32061186262404444710028923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21374124174936296473352615 32061186262404444710028923)
        ·
          refine ⟨48091779393606667065043385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32061186262404444710028923 48091779393606667065043385)
          ·
            refine ⟨36068834545205000298782539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48091779393606667065043385 36068834545205000298782539)
            ·
              refine ⟨54103251817807500448173809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36068834545205000298782539 54103251817807500448173809)
              ·
                refine ⟨40577438863355625336130357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54103251817807500448173809 40577438863355625336130357)
                ·
                  refine ⟨3804134893439589875262221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40577438863355625336130357 3804134893439589875262221)
                  ·
                    refine ⟨1426550585039846203223333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3804134893439589875262221 1426550585039846203223333)
                    ·
                      refine ⟨267478234694971163104375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1426550585039846203223333 267478234694971163104375)
                      ·
                        rfl

theorem cell23_520912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_520912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520912 prefixEnd_520912 := by exact prefixLift 520912
  have htrace : WordTrace (prefixWord ++ tailWord_520912) baseStart_520912 baseEnd_520912 := by
    simpa [prefixWord, tailWord_520912, baseEnd_520912] using wordTrace_append hprefix tailTrace_520912
  have hstable : (prefixWord ++ tailWord_520912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520912).length < 2 ^ (prefixWord ++ tailWord_520912).sum := by decide
  have hdescent : baseEnd_520912 < baseStart_520912 := by decide
  rcases family_descends (prefixWord ++ tailWord_520912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520939 : List Nat := [1, 1, 1, 1, 2, 4, 1, 5, 3, 4]
def baseStart_520939 : Nat := 118140960795 + 520939 * 2 ^ 59
def prefixEnd_520939 : Nat := 4983230072969 + 3 ^ 40 * 520939 * 2
def baseEnd_520939 : Nat := 89164032890880852488917

theorem tailTrace_520939 : CollatzResearch.WordTrace tailWord_520939 prefixEnd_520939 89164032890880852488917 := by
  unfold tailWord_520939
  simp only [CollatzResearch.WordTrace]
  refine ⟨19000206259734447143101871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12666804173156298095401247 19000206259734447143101871)
  ·
    refine ⟨28500309389601670714652807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19000206259734447143101871 28500309389601670714652807)
    ·
      refine ⟨42750464084402506071979211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28500309389601670714652807 42750464084402506071979211)
      ·
        refine ⟨64125696126603759107968817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42750464084402506071979211 64125696126603759107968817)
        ·
          refine ⟨48094272094952819330976613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64125696126603759107968817 48094272094952819330976613)
          ·
            refine ⟨9017676017803653624558115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48094272094952819330976613 9017676017803653624558115)
            ·
              refine ⟨13526514026705480436837173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9017676017803653624558115 13526514026705480436837173)
              ·
                refine ⟨1268110690003638790953485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13526514026705480436837173 1268110690003638790953485)
                ·
                  refine ⟨475541508751364546607557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268110690003638790953485 475541508751364546607557)
                  ·
                    refine ⟨89164032890880852488917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 475541508751364546607557 89164032890880852488917)
                    ·
                      rfl

theorem cell23_520939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 4].length) (baseStart_520939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520939 prefixEnd_520939 := by exact prefixLift 520939
  have htrace : WordTrace (prefixWord ++ tailWord_520939) baseStart_520939 baseEnd_520939 := by
    simpa [prefixWord, tailWord_520939, baseEnd_520939] using wordTrace_append hprefix tailTrace_520939
  have hstable : (prefixWord ++ tailWord_520939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520939).length < 2 ^ (prefixWord ++ tailWord_520939).sum := by decide
  have hdescent : baseEnd_520939 < baseStart_520939 := by decide
  rcases family_descends (prefixWord ++ tailWord_520939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520946 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 1, 6, 2]
def baseStart_520946 : Nat := 118140960795 + 520946 * 2 ^ 59
def prefixEnd_520946 : Nat := 4983230072969 + 3 ^ 40 * 520946 * 2
def baseEnd_520946 : Nat := 267495693037224030079219

theorem tailTrace_520946 : CollatzResearch.WordTrace tailWord_520946 prefixEnd_520946 267495693037224030079219 := by
  unfold tailWord_520946
  simp only [CollatzResearch.WordTrace]
  refine ⟨4750115392677271834651673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12666974380472724892404461 4750115392677271834651673)
  ·
    refine ⟨3562586544507953875988755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4750115392677271834651673 3562586544507953875988755)
    ·
      refine ⟨5343879816761930813983133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3562586544507953875988755 5343879816761930813983133)
      ·
        refine ⟨2003954931285724055243675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5343879816761930813983133 2003954931285724055243675)
        ·
          refine ⟨3005932396928586082865513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003954931285724055243675 3005932396928586082865513)
          ·
            refine ⟨2254449297696439562149135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3005932396928586082865513 2254449297696439562149135)
            ·
              refine ⟨3381673946544659343223703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254449297696439562149135 3381673946544659343223703)
              ·
                refine ⟨5072510919816989014835555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3381673946544659343223703 5072510919816989014835555)
                ·
                  refine ⟨7608766379725483522253333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5072510919816989014835555 7608766379725483522253333)
                  ·
                    refine ⟨356660924049632040105625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7608766379725483522253333 356660924049632040105625)
                    ·
                      refine ⟨267495693037224030079219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 356660924049632040105625 267495693037224030079219)
                      ·
                        rfl

theorem cell23_520946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_520946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520946 prefixEnd_520946 := by exact prefixLift 520946
  have htrace : WordTrace (prefixWord ++ tailWord_520946) baseStart_520946 baseEnd_520946 := by
    simpa [prefixWord, tailWord_520946, baseEnd_520946] using wordTrace_append hprefix tailTrace_520946
  have hstable : (prefixWord ++ tailWord_520946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520946).length < 2 ^ (prefixWord ++ tailWord_520946).sum := by decide
  have hdescent : baseEnd_520946 < baseStart_520946 := by decide
  rcases family_descends (prefixWord ++ tailWord_520946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520956 : List Nat := [2, 2, 2, 1, 3, 3, 1, 2, 3, 4]
def baseStart_520956 : Nat := 118140960795 + 520956 * 2 ^ 59
def prefixEnd_520956 : Nat := 4983230072969 + 3 ^ 40 * 520956 * 2
def baseEnd_520956 : Nat := 89166942614589663651391

theorem tailTrace_520956 : CollatzResearch.WordTrace tailWord_520956 prefixEnd_520956 89166942614589663651391 := by
  unfold tailWord_520956
  simp only [CollatzResearch.WordTrace]
  refine ⟨9500413150336429523235361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12667217533781906030980481 9500413150336429523235361)
  ·
    refine ⟨7125309862752322142426521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9500413150336429523235361 7125309862752322142426521)
    ·
      refine ⟨5343982397064241606819891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7125309862752322142426521 5343982397064241606819891)
      ·
        refine ⟨8015973595596362410229837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5343982397064241606819891 8015973595596362410229837)
        ·
          refine ⟨3005990098348635903836189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8015973595596362410229837 3005990098348635903836189)
          ·
            refine ⟨1127246286880738463938571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3005990098348635903836189 1127246286880738463938571)
            ·
              refine ⟨1690869430321107695907857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127246286880738463938571 1690869430321107695907857)
              ·
                refine ⟨1268152072740830771930893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1690869430321107695907857 1268152072740830771930893)
                ·
                  refine ⟨475557027277811539474085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268152072740830771930893 475557027277811539474085)
                  ·
                    refine ⟨89166942614589663651391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 475557027277811539474085 89166942614589663651391)
                    ·
                      rfl

theorem cell23_520956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_520956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_520956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_520956 prefixEnd_520956 := by exact prefixLift 520956
  have htrace : WordTrace (prefixWord ++ tailWord_520956) baseStart_520956 baseEnd_520956 := by
    simpa [prefixWord, tailWord_520956, baseEnd_520956] using wordTrace_append hprefix tailTrace_520956
  have hstable : (prefixWord ++ tailWord_520956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520956).length < 2 ^ (prefixWord ++ tailWord_520956).sum := by decide
  have hdescent : baseEnd_520956 < baseStart_520956 := by decide
  rcases family_descends (prefixWord ++ tailWord_520956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521013 : List Nat := [1, 3, 3, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_521013 : Nat := 118140960795 + 521013 * 2 ^ 59
def prefixEnd_521013 : Nat := 4983230072969 + 3 ^ 40 * 521013 * 2
def baseEnd_521013 : Nat := 267530096241075267941411

theorem tailTrace_521013 : CollatzResearch.WordTrace tailWord_521013 prefixEnd_521013 267530096241075267941411 := by
  unfold tailWord_521013
  simp only [CollatzResearch.WordTrace]
  refine ⟨19002905261466357781295693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12668603507644238520863795 19002905261466357781295693)
  ·
    refine ⟨7126089473049884167985885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19002905261466357781295693 7126089473049884167985885)
    ·
      refine ⟨2672283552393706562994707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7126089473049884167985885 2672283552393706562994707)
      ·
        refine ⟨4008425328590559844492061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2672283552393706562994707 4008425328590559844492061)
        ·
          refine ⟨1503159498221459941684523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4008425328590559844492061 1503159498221459941684523)
          ·
            refine ⟨2254739247332189912526785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503159498221459941684523 2254739247332189912526785)
            ·
              refine ⟨1691054435499142434395089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2254739247332189912526785 1691054435499142434395089)
              ·
                refine ⟨1268290826624356825796317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1691054435499142434395089 1268290826624356825796317)
                ·
                  refine ⟨475609059984133809673619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268290826624356825796317 475609059984133809673619)
                  ·
                    refine ⟨713413589976200714510429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 475609059984133809673619 713413589976200714510429)
                    ·
                      refine ⟨267530096241075267941411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 713413589976200714510429 267530096241075267941411)
                      ·
                        rfl

theorem cell23_521013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_521013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521013 prefixEnd_521013 := by exact prefixLift 521013
  have htrace : WordTrace (prefixWord ++ tailWord_521013) baseStart_521013 baseEnd_521013 := by
    simpa [prefixWord, tailWord_521013, baseEnd_521013] using wordTrace_append hprefix tailTrace_521013
  have hstable : (prefixWord ++ tailWord_521013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521013).length < 2 ^ (prefixWord ++ tailWord_521013).sum := by decide
  have hdescent : baseEnd_521013 < baseStart_521013 := by decide
  rcases family_descends (prefixWord ++ tailWord_521013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521016 : List Nat := [2, 1, 2, 1, 3, 2, 4, 2, 1, 5]
def baseStart_521016 : Nat := 118140960795 + 521016 * 2 ^ 59
def prefixEnd_521016 : Nat := 4983230072969 + 3 ^ 40 * 521016 * 2
def baseEnd_521016 : Nat := 89177212227679585401299

theorem tailTrace_521016 : CollatzResearch.WordTrace tailWord_521016 prefixEnd_521016 89177212227679585401299 := by
  unfold tailWord_521016
  simp only [CollatzResearch.WordTrace]
  refine ⟨9501507340227744646827451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12668676453636992862436601 9501507340227744646827451)
  ·
    refine ⟨14252261010341616970241177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9501507340227744646827451 14252261010341616970241177)
    ·
      refine ⟨10689195757756212727680883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14252261010341616970241177 10689195757756212727680883)
      ·
        refine ⟨16033793636634319091521325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10689195757756212727680883 16033793636634319091521325)
        ·
          refine ⟨6012672613737869659320497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16033793636634319091521325 6012672613737869659320497)
          ·
            refine ⟨4509504460303402244490373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6012672613737869659320497 4509504460303402244490373)
            ·
              refine ⟨845532086306887920841945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4509504460303402244490373 845532086306887920841945)
              ·
                refine ⟨634149064730165940631459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 845532086306887920841945 634149064730165940631459)
                ·
                  refine ⟨951223597095248910947189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 634149064730165940631459 951223597095248910947189)
                  ·
                    refine ⟨89177212227679585401299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 951223597095248910947189 89177212227679585401299)
                    ·
                      rfl

theorem cell23_521016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_521016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521016 prefixEnd_521016 := by exact prefixLift 521016
  have htrace : WordTrace (prefixWord ++ tailWord_521016) baseStart_521016 baseEnd_521016 := by
    simpa [prefixWord, tailWord_521016, baseEnd_521016] using wordTrace_append hprefix tailTrace_521016
  have hstable : (prefixWord ++ tailWord_521016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521016).length < 2 ^ (prefixWord ++ tailWord_521016).sum := by decide
  have hdescent : baseEnd_521016 < baseStart_521016 := by decide
  rcases family_descends (prefixWord ++ tailWord_521016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521047 : List Nat := [1, 1, 3, 2, 4, 2, 3, 2, 1, 1, 3]
def baseStart_521047 : Nat := 118140960795 + 521047 * 2 ^ 59
def prefixEnd_521047 : Nat := 4983230072969 + 3 ^ 40 * 521047 * 2
def baseEnd_521047 : Nat := 267547554583328134916255

theorem tailTrace_521047 : CollatzResearch.WordTrace tailWord_521047 prefixEnd_521047 267547554583328134916255 := by
  unfold tailWord_521047
  simp only [CollatzResearch.WordTrace]
  refine ⟨19004145343343181588033395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12669430228895454392022263 19004145343343181588033395)
  ·
    refine ⟨28506218015014772382050093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19004145343343181588033395 28506218015014772382050093)
    ·
      refine ⟨10689831755630539643268785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28506218015014772382050093 10689831755630539643268785)
      ·
        refine ⟨8017373816722904732451589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10689831755630539643268785 8017373816722904732451589)
        ·
          refine ⟨1503257590635544637334673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8017373816722904732451589 1503257590635544637334673)
          ·
            refine ⟨1127443192976658478001005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1503257590635544637334673 1127443192976658478001005)
            ·
              refine ⟨422791197366246929250377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1127443192976658478001005 422791197366246929250377)
              ·
                refine ⟨317093398024685196937783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422791197366246929250377 317093398024685196937783)
                ·
                  refine ⟨475640097037027795406675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317093398024685196937783 475640097037027795406675)
                  ·
                    refine ⟨713460145555541693110013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 475640097037027795406675 713460145555541693110013)
                    ·
                      refine ⟨267547554583328134916255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 713460145555541693110013 267547554583328134916255)
                      ·
                        rfl

theorem cell23_521047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 1, 1, 3].length) (baseStart_521047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521047 prefixEnd_521047 := by exact prefixLift 521047
  have htrace : WordTrace (prefixWord ++ tailWord_521047) baseStart_521047 baseEnd_521047 := by
    simpa [prefixWord, tailWord_521047, baseEnd_521047] using wordTrace_append hprefix tailTrace_521047
  have hstable : (prefixWord ++ tailWord_521047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521047).length < 2 ^ (prefixWord ++ tailWord_521047).sum := by decide
  have hdescent : baseEnd_521047 < baseStart_521047 := by decide
  rcases family_descends (prefixWord ++ tailWord_521047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521049 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 1, 1, 6]
def baseStart_521049 : Nat := 118140960795 + 521049 * 2 ^ 59
def prefixEnd_521049 : Nat := 4983230072969 + 3 ^ 40 * 521049 * 2
def baseEnd_521049 : Nat := 267548581544637127091245

theorem tailTrace_521049 : CollatzResearch.WordTrace tailWord_521049 prefixEnd_521049 267548581544637127091245 := by
  unfold tailWord_521049
  simp only [CollatzResearch.WordTrace]
  refine ⟨19004218289335935929606201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12669478859557290619737467 19004218289335935929606201)
  ·
    refine ⟨14253163717001951947204651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19004218289335935929606201 14253163717001951947204651)
    ·
      refine ⟨21379745575502927920806977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14253163717001951947204651 21379745575502927920806977)
      ·
        refine ⟨16034809181627195940605233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21379745575502927920806977 16034809181627195940605233)
        ·
          refine ⟨12026106886220396955453925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16034809181627195940605233 12026106886220396955453925)
          ·
            refine ⟨2254895041166324429147611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12026106886220396955453925 2254895041166324429147611)
            ·
              refine ⟨3382342561749486643721417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254895041166324429147611 3382342561749486643721417)
              ·
                refine ⟨2536756921312114982791063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3382342561749486643721417 2536756921312114982791063)
                ·
                  refine ⟨3805135381968172474186595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536756921312114982791063 3805135381968172474186595)
                  ·
                    refine ⟨5707703072952258711279893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3805135381968172474186595 5707703072952258711279893)
                    ·
                      refine ⟨267548581544637127091245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5707703072952258711279893 267548581544637127091245)
                      ·
                        rfl

theorem cell23_521049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_521049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521049 prefixEnd_521049 := by exact prefixLift 521049
  have htrace : WordTrace (prefixWord ++ tailWord_521049) baseStart_521049 baseEnd_521049 := by
    simpa [prefixWord, tailWord_521049, baseEnd_521049] using wordTrace_append hprefix tailTrace_521049
  have hstable : (prefixWord ++ tailWord_521049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521049).length < 2 ^ (prefixWord ++ tailWord_521049).sum := by decide
  have hdescent : baseEnd_521049 < baseStart_521049 := by decide
  rcases family_descends (prefixWord ++ tailWord_521049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521056 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 3]
def baseStart_521056 : Nat := 118140960795 + 521056 * 2 ^ 59
def prefixEnd_521056 : Nat := 4983230072969 + 3 ^ 40 * 521056 * 2
def baseEnd_521056 : Nat := 267552175909218599703713

theorem tailTrace_521056 : CollatzResearch.WordTrace tailWord_521056 prefixEnd_521056 267552175909218599703713 := by
  unfold tailWord_521056
  simp only [CollatzResearch.WordTrace]
  refine ⟨9502236800155288062555511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12669649066873717416740681 9502236800155288062555511)
  ·
    refine ⟨14253355200232932093833267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9502236800155288062555511 14253355200232932093833267)
    ·
      refine ⟨21380032800349398140749901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14253355200232932093833267 21380032800349398140749901)
      ·
        refine ⟨8017512300131024302781213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21380032800349398140749901 8017512300131024302781213)
        ·
          refine ⟨3006567112549134113542955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8017512300131024302781213 3006567112549134113542955)
          ·
            refine ⟨4509850668823701170314433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3006567112549134113542955 4509850668823701170314433)
            ·
              refine ⟨3382388001617775877735825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4509850668823701170314433 3382388001617775877735825)
              ·
                refine ⟨2536791001213331908301869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3382388001617775877735825 2536791001213331908301869)
                ·
                  refine ⟨951296625454999465613201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2536791001213331908301869 951296625454999465613201)
                  ·
                    refine ⟨713472469091249599209901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 951296625454999465613201 713472469091249599209901)
                    ·
                      refine ⟨267552175909218599703713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 713472469091249599209901 267552175909218599703713)
                      ·
                        rfl

theorem cell23_521056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_521056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521056 prefixEnd_521056 := by exact prefixLift 521056
  have htrace : WordTrace (prefixWord ++ tailWord_521056) baseStart_521056 baseEnd_521056 := by
    simpa [prefixWord, tailWord_521056, baseEnd_521056] using wordTrace_append hprefix tailTrace_521056
  have hstable : (prefixWord ++ tailWord_521056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521056).length < 2 ^ (prefixWord ++ tailWord_521056).sum := by decide
  have hdescent : baseEnd_521056 < baseStart_521056 := by decide
  rcases family_descends (prefixWord ++ tailWord_521056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521059 : List Nat := [1, 1, 1, 5, 3, 1, 1, 10]
def baseStart_521059 : Nat := 118140960795 + 521059 * 2 ^ 59
def prefixEnd_521059 : Nat := 4983230072969 + 3 ^ 40 * 521059 * 2
def baseEnd_521059 : Nat := 9909396901895632887637

theorem tailTrace_521059 : CollatzResearch.WordTrace tailWord_521059 prefixEnd_521059 9909396901895632887637 := by
  unfold tailWord_521059
  simp only [CollatzResearch.WordTrace]
  refine ⟨19004583019299707637470231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12669722012866471758313487 19004583019299707637470231)
  ·
    refine ⟨28506874528949561456205347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19004583019299707637470231 28506874528949561456205347)
    ·
      refine ⟨42760311793424342184308021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28506874528949561456205347 42760311793424342184308021)
      ·
        refine ⟨4008779230633532079778877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42760311793424342184308021 4008779230633532079778877)
        ·
          refine ⟨1503292211487574529917079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4008779230633532079778877 1503292211487574529917079)
          ·
            refine ⟨2254938317231361794875619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503292211487574529917079 2254938317231361794875619)
            ·
              refine ⟨3382407475847042692313429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254938317231361794875619 3382407475847042692313429)
              ·
                refine ⟨9909396901895632887637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3382407475847042692313429 9909396901895632887637)
                ·
                  rfl

theorem cell23_521059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 10].length) (baseStart_521059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521059 prefixEnd_521059 := by exact prefixLift 521059
  have htrace : WordTrace (prefixWord ++ tailWord_521059) baseStart_521059 baseEnd_521059 := by
    simpa [prefixWord, tailWord_521059, baseEnd_521059] using wordTrace_append hprefix tailTrace_521059
  have hstable : (prefixWord ++ tailWord_521059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521059).length < 2 ^ (prefixWord ++ tailWord_521059).sum := by decide
  have hdescent : baseEnd_521059 < baseStart_521059 := by decide
  rcases family_descends (prefixWord ++ tailWord_521059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521063 : List Nat := [1, 1, 5, 1, 2, 3, 1, 3, 2, 4]
def baseStart_521063 : Nat := 118140960795 + 521063 * 2 ^ 59
def prefixEnd_521063 : Nat := 4983230072969 + 3 ^ 40 * 521063 * 2
def baseEnd_521063 : Nat := 89185256757933357438727

theorem tailTrace_521063 : CollatzResearch.WordTrace tailWord_521063 prefixEnd_521063 89185256757933357438727 := by
  unfold tailWord_521063
  simp only [CollatzResearch.WordTrace]
  refine ⟨19004728911285216320615843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12669819274190144213743895 19004728911285216320615843)
  ·
    refine ⟨28507093366927824480923765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19004728911285216320615843 28507093366927824480923765)
    ·
      refine ⟨2672540003149483545086603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28507093366927824480923765 2672540003149483545086603)
      ·
        refine ⟨4008810004724225317629905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2672540003149483545086603 4008810004724225317629905)
        ·
          refine ⟨3006607503543168988222429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4008810004724225317629905 3006607503543168988222429)
          ·
            refine ⟨1127477813828688370583411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3006607503543168988222429 1127477813828688370583411)
            ·
              refine ⟨1691216720743032555875117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127477813828688370583411 1691216720743032555875117)
              ·
                refine ⟨634206270278637208453169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1691216720743032555875117 634206270278637208453169)
                ·
                  refine ⟨475654702708977906339877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 634206270278637208453169 475654702708977906339877)
                  ·
                    refine ⟨89185256757933357438727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 475654702708977906339877 89185256757933357438727)
                    ·
                      rfl

theorem cell23_521063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_521063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521063 prefixEnd_521063 := by exact prefixLift 521063
  have htrace : WordTrace (prefixWord ++ tailWord_521063) baseStart_521063 baseEnd_521063 := by
    simpa [prefixWord, tailWord_521063, baseEnd_521063] using wordTrace_append hprefix tailTrace_521063
  have hstable : (prefixWord ++ tailWord_521063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521063).length < 2 ^ (prefixWord ++ tailWord_521063).sum := by decide
  have hdescent : baseEnd_521063 < baseStart_521063 := by decide
  rcases family_descends (prefixWord ++ tailWord_521063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521073 : List Nat := [1, 2, 2, 2, 1, 4, 3, 2, 1, 2, 3]
def baseStart_521073 : Nat := 118140960795 + 521073 * 2 ^ 59
def prefixEnd_521073 : Nat := 4983230072969 + 3 ^ 40 * 521073 * 2
def baseEnd_521073 : Nat := 267560905080345033191135

theorem tailTrace_521073 : CollatzResearch.WordTrace tailWord_521073 prefixEnd_521073 267560905080345033191135 := by
  unfold tailWord_521073
  simp only [CollatzResearch.WordTrace]
  refine ⟨19005093641248988028479873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12670062427499325352319915 19005093641248988028479873)
  ·
    refine ⟨14253820230936741021359905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19005093641248988028479873 14253820230936741021359905)
    ·
      refine ⟨10690365173202555766019929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14253820230936741021359905 10690365173202555766019929)
      ·
        refine ⟨8017773879901916824514947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10690365173202555766019929 8017773879901916824514947)
        ·
          refine ⟨12026660819852875236772421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8017773879901916824514947 12026660819852875236772421)
          ·
            refine ⟨2254998903722414106894829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12026660819852875236772421 2254998903722414106894829)
            ·
              refine ⟨845624588895905290085561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2254998903722414106894829 845624588895905290085561)
              ·
                refine ⟨634218441671928967564171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 845624588895905290085561 634218441671928967564171)
                ·
                  refine ⟨951327662507893451346257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 634218441671928967564171 951327662507893451346257)
                  ·
                    refine ⟨713495746880920088509693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 951327662507893451346257 713495746880920088509693)
                    ·
                      refine ⟨267560905080345033191135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 713495746880920088509693 267560905080345033191135)
                      ·
                        rfl

theorem cell23_521073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_521073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521073 prefixEnd_521073 := by exact prefixLift 521073
  have htrace : WordTrace (prefixWord ++ tailWord_521073) baseStart_521073 baseEnd_521073 := by
    simpa [prefixWord, tailWord_521073, baseEnd_521073] using wordTrace_append hprefix tailTrace_521073
  have hstable : (prefixWord ++ tailWord_521073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521073).length < 2 ^ (prefixWord ++ tailWord_521073).sum := by decide
  have hdescent : baseEnd_521073 < baseStart_521073 := by decide
  rcases family_descends (prefixWord ++ tailWord_521073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521099 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 5]
def baseStart_521099 : Nat := 118140960795 + 521099 * 2 ^ 59
def prefixEnd_521099 : Nat := 4983230072969 + 3 ^ 40 * 521099 * 2
def baseEnd_521099 : Nat := 267574255577361931466015

theorem tailTrace_521099 : CollatzResearch.WordTrace tailWord_521099 prefixEnd_521099 267574255577361931466015 := by
  unfold tailWord_521099
  simp only [CollatzResearch.WordTrace]
  refine ⟨19006041939154794468926351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12670694626103196312617567 19006041939154794468926351)
  ·
    refine ⟨28509062908732191703389527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19006041939154794468926351 28509062908732191703389527)
    ·
      refine ⟨42763594363098287555084291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28509062908732191703389527 42763594363098287555084291)
      ·
        refine ⟨64145391544647431332626437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42763594363098287555084291 64145391544647431332626437)
        ·
          refine ⟨12027260914621393374867457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64145391544647431332626437 12027260914621393374867457)
          ·
            refine ⟨9020445685966045031150593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12027260914621393374867457 9020445685966045031150593)
            ·
              refine ⟨6765334264474533773362945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9020445685966045031150593 6765334264474533773362945)
              ·
                refine ⟨5074000698355900330022209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6765334264474533773362945 5074000698355900330022209)
                ·
                  refine ⟨3805500523766925247516657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5074000698355900330022209 3805500523766925247516657)
                  ·
                    refine ⟨2854125392825193935637493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3805500523766925247516657 2854125392825193935637493)
                    ·
                      refine ⟨267574255577361931466015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2854125392825193935637493 267574255577361931466015)
                      ·
                        rfl

theorem cell23_521099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 5].length) (baseStart_521099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521099 prefixEnd_521099 := by exact prefixLift 521099
  have htrace : WordTrace (prefixWord ++ tailWord_521099) baseStart_521099 baseEnd_521099 := by
    simpa [prefixWord, tailWord_521099, baseEnd_521099] using wordTrace_append hprefix tailTrace_521099
  have hstable : (prefixWord ++ tailWord_521099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521099).length < 2 ^ (prefixWord ++ tailWord_521099).sum := by decide
  have hdescent : baseEnd_521099 < baseStart_521099 := by decide
  rcases family_descends (prefixWord ++ tailWord_521099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521110 : List Nat := [5, 3, 1, 1, 1, 1, 3, 8]
def baseStart_521110 : Nat := 118140960795 + 521110 * 2 ^ 59
def prefixEnd_521110 : Nat := 4983230072969 + 3 ^ 40 * 521110 * 2
def baseEnd_521110 : Nat := 9910366809798569941795

theorem tailTrace_521110 : CollatzResearch.WordTrace tailWord_521110 prefixEnd_521110 9910366809798569941795 := by
  unfold tailWord_521110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1187902696382183959223549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12670962094743295565051189 1187902696382183959223549)
  ·
    refine ⟨445463511143318984708831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1187902696382183959223549 445463511143318984708831)
    ·
      refine ⟨668195266714978477063247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445463511143318984708831 668195266714978477063247)
      ·
        refine ⟨1002292900072467715594871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668195266714978477063247 1002292900072467715594871)
        ·
          refine ⟨1503439350108701573392307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002292900072467715594871 1503439350108701573392307)
          ·
            refine ⟨2255159025163052360088461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503439350108701573392307 2255159025163052360088461)
            ·
              refine ⟨845684634436144635033173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2255159025163052360088461 845684634436144635033173)
              ·
                refine ⟨9910366809798569941795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 845684634436144635033173 9910366809798569941795)
                ·
                  rfl

theorem cell23_521110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_521110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521110 prefixEnd_521110 := by exact prefixLift 521110
  have htrace : WordTrace (prefixWord ++ tailWord_521110) baseStart_521110 baseEnd_521110 := by
    simpa [prefixWord, tailWord_521110, baseEnd_521110] using wordTrace_append hprefix tailTrace_521110
  have hstable : (prefixWord ++ tailWord_521110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521110).length < 2 ^ (prefixWord ++ tailWord_521110).sum := by decide
  have hdescent : baseEnd_521110 < baseStart_521110 := by decide
  rcases family_descends (prefixWord ++ tailWord_521110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521143 : List Nat := [1, 1, 3, 1, 3, 1, 4, 2, 1, 4, 2]
def baseStart_521143 : Nat := 118140960795 + 521143 * 2 ^ 59
def prefixEnd_521143 : Nat := 4983230072969 + 3 ^ 40 * 521143 * 2
def baseEnd_521143 : Nat := 267596848726159759315813

theorem tailTrace_521143 : CollatzResearch.WordTrace tailWord_521143 prefixEnd_521143 267596848726159759315813 := by
  unfold tailWord_521143
  simp only [CollatzResearch.WordTrace]
  refine ⟨19007646750995389983528083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12671764500663593322352055 19007646750995389983528083)
  ·
    refine ⟨28511470126493084975292125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19007646750995389983528083 28511470126493084975292125)
    ·
      refine ⟨10691801297434906865734547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28511470126493084975292125 10691801297434906865734547)
      ·
        refine ⟨16037701946152360298601821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10691801297434906865734547 16037701946152360298601821)
        ·
          refine ⟨6014138229807135111975683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16037701946152360298601821 6014138229807135111975683)
          ·
            refine ⟨9021207344710702667963525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6014138229807135111975683 9021207344710702667963525)
            ·
              refine ⟨1691476377133256750243161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9021207344710702667963525 1691476377133256750243161)
              ·
                refine ⟨1268607282849942562682371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1691476377133256750243161 1268607282849942562682371)
                ·
                  refine ⟨1902910924274913844023557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1268607282849942562682371 1902910924274913844023557)
                  ·
                    refine ⟨356795798301546345754417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1902910924274913844023557 356795798301546345754417)
                    ·
                      refine ⟨267596848726159759315813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 356795798301546345754417 267596848726159759315813)
                      ·
                        rfl

theorem cell23_521143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 4, 2].length) (baseStart_521143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521143 prefixEnd_521143 := by exact prefixLift 521143
  have htrace : WordTrace (prefixWord ++ tailWord_521143) baseStart_521143 baseEnd_521143 := by
    simpa [prefixWord, tailWord_521143, baseEnd_521143] using wordTrace_append hprefix tailTrace_521143
  have hstable : (prefixWord ++ tailWord_521143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521143).length < 2 ^ (prefixWord ++ tailWord_521143).sum := by decide
  have hdescent : baseEnd_521143 < baseStart_521143 := by decide
  rcases family_descends (prefixWord ++ tailWord_521143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521166 : List Nat := [4, 1, 1, 1, 2, 3, 1, 3, 7]
def baseStart_521166 : Nat := 118140960795 + 521166 * 2 ^ 59
def prefixEnd_521166 : Nat := 4983230072969 + 3 ^ 40 * 521166 * 2
def baseEnd_521166 : Nat := 29734295420134796592023

theorem tailTrace_521166 : CollatzResearch.WordTrace tailWord_521166 prefixEnd_521166 29734295420134796592023 := by
  unfold tailWord_521166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2376060703739008113951919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12672323753274709941076901 2376060703739008113951919)
  ·
    refine ⟨3564091055608512170927879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2376060703739008113951919 3564091055608512170927879)
    ·
      refine ⟨5346136583412768256391819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3564091055608512170927879 5346136583412768256391819)
      ·
        refine ⟨8019204875119152384587729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5346136583412768256391819 8019204875119152384587729)
        ·
          refine ⟨6014403656339364288440797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8019204875119152384587729 6014403656339364288440797)
          ·
            refine ⟨2255401371127261608165299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6014403656339364288440797 2255401371127261608165299)
            ·
              refine ⟨3383102056690892412247949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255401371127261608165299 3383102056690892412247949)
              ·
                refine ⟨1268663271259084654592981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3383102056690892412247949 1268663271259084654592981)
                ·
                  refine ⟨29734295420134796592023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1268663271259084654592981 29734295420134796592023)
                  ·
                    rfl

theorem cell23_521166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_521166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521166 prefixEnd_521166 := by exact prefixLift 521166
  have htrace : WordTrace (prefixWord ++ tailWord_521166) baseStart_521166 baseEnd_521166 := by
    simpa [prefixWord, tailWord_521166, baseEnd_521166] using wordTrace_append hprefix tailTrace_521166
  have hstable : (prefixWord ++ tailWord_521166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521166).length < 2 ^ (prefixWord ++ tailWord_521166).sum := by decide
  have hdescent : baseEnd_521166 < baseStart_521166 := by decide
  rcases family_descends (prefixWord ++ tailWord_521166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521233 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 2, 4, 2]
def baseStart_521233 : Nat := 118140960795 + 521233 * 2 ^ 59
def prefixEnd_521233 : Nat := 4983230072969 + 3 ^ 40 * 521233 * 2
def baseEnd_521233 : Nat := 267643061985064407190399

theorem tailTrace_521233 : CollatzResearch.WordTrace tailWord_521233 prefixEnd_521233 267643061985064407190399 := by
  unfold tailWord_521233
  simp only [CollatzResearch.WordTrace]
  refine ⟨19010929320669335354304353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12673952880446223569536235 19010929320669335354304353)
  ·
    refine ⟨14258196990502001515728265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19010929320669335354304353 14258196990502001515728265)
    ·
      refine ⟨10693647742876501136796199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14258196990502001515728265 10693647742876501136796199)
      ·
        refine ⟨16040471614314751705194299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10693647742876501136796199 16040471614314751705194299)
        ·
          refine ⟨24060707421472127557791449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16040471614314751705194299 24060707421472127557791449)
          ·
            refine ⟨18045530566104095668343587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24060707421472127557791449 18045530566104095668343587)
            ·
              refine ⟨27068295849156143502515381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18045530566104095668343587 27068295849156143502515381)
              ·
                refine ⟨2537652735858388453360817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27068295849156143502515381 2537652735858388453360817)
                ·
                  refine ⟨1903239551893791340020613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2537652735858388453360817 1903239551893791340020613)
                  ·
                    refine ⟨356857415980085876253865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1903239551893791340020613 356857415980085876253865)
                    ·
                      refine ⟨267643061985064407190399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 356857415980085876253865 267643061985064407190399)
                      ·
                        rfl

theorem cell23_521233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 4, 2].length) (baseStart_521233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521233 prefixEnd_521233 := by exact prefixLift 521233
  have htrace : WordTrace (prefixWord ++ tailWord_521233) baseStart_521233 baseEnd_521233 := by
    simpa [prefixWord, tailWord_521233, baseEnd_521233] using wordTrace_append hprefix tailTrace_521233
  have hstable : (prefixWord ++ tailWord_521233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521233).length < 2 ^ (prefixWord ++ tailWord_521233).sum := by decide
  have hdescent : baseEnd_521233 < baseStart_521233 := by decide
  rcases family_descends (prefixWord ++ tailWord_521233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521250 : List Nat := [3, 3, 1, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_521250 : Nat := 118140960795 + 521250 * 2 ^ 59
def prefixEnd_521250 : Nat := 4983230072969 + 3 ^ 40 * 521250 * 2
def baseEnd_521250 : Nat := 267651791156190840677821

theorem tailTrace_521250 : CollatzResearch.WordTrace tailWord_521250 prefixEnd_521250 267651791156190840677821 := by
  unfold tailWord_521250
  simp only [CollatzResearch.WordTrace]
  refine ⟨4752887340401936814418301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12674366241071831505115469 4752887340401936814418301)
  ·
    refine ⟨1782332752650726305406863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4752887340401936814418301 1782332752650726305406863)
    ·
      refine ⟨2673499128976089458110295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1782332752650726305406863 2673499128976089458110295)
      ·
        refine ⟨4010248693464134187165443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2673499128976089458110295 4010248693464134187165443)
        ·
          refine ⟨6015373040196201280748165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4010248693464134187165443 6015373040196201280748165)
          ·
            refine ⟨1127882445036787740140281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6015373040196201280748165 1127882445036787740140281)
            ·
              refine ⟨845911833777590805105211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1127882445036787740140281 845911833777590805105211)
              ·
                refine ⟨1268867750666386207657817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 845911833777590805105211 1268867750666386207657817)
                ·
                  refine ⟨951650812999789655743363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1268867750666386207657817 951650812999789655743363)
                  ·
                    refine ⟨1427476219499684483615045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 951650812999789655743363 1427476219499684483615045)
                    ·
                      refine ⟨267651791156190840677821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1427476219499684483615045 267651791156190840677821)
                      ·
                        rfl

theorem cell23_521250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_521250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521250 prefixEnd_521250 := by exact prefixLift 521250
  have htrace : WordTrace (prefixWord ++ tailWord_521250) baseStart_521250 baseEnd_521250 := by
    simpa [prefixWord, tailWord_521250, baseEnd_521250] using wordTrace_append hprefix tailTrace_521250
  have hstable : (prefixWord ++ tailWord_521250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521250).length < 2 ^ (prefixWord ++ tailWord_521250).sum := by decide
  have hdescent : baseEnd_521250 < baseStart_521250 := by decide
  rcases family_descends (prefixWord ++ tailWord_521250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521260 : List Nat := [2, 2, 1, 1, 1, 2, 4, 5, 1, 4]
def baseStart_521260 : Nat := 118140960795 + 521260 * 2 ^ 59
def prefixEnd_521260 : Nat := 4983230072969 + 3 ^ 40 * 521260 * 2
def baseEnd_521260 : Nat := 89218975320911933850925

theorem tailTrace_521260 : CollatzResearch.WordTrace tailWord_521260 prefixEnd_521260 89218975320911933850925 := by
  unfold tailWord_521260
  simp only [CollatzResearch.WordTrace]
  refine ⟨9505957045785759482768617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12674609394381012643691489 9505957045785759482768617)
  ·
    refine ⟨7129467784339319612076463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9505957045785759482768617 7129467784339319612076463)
    ·
      refine ⟨10694201676508979418114695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7129467784339319612076463 10694201676508979418114695)
      ·
        refine ⟨16041302514763469127172043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10694201676508979418114695 16041302514763469127172043)
        ·
          refine ⟨24061953772145203690758065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16041302514763469127172043 24061953772145203690758065)
          ·
            refine ⟨18046465329108902768068549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24061953772145203690758065 18046465329108902768068549)
            ·
              refine ⟨3383712249207919269012853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18046465329108902768068549 3383712249207919269012853)
              ·
                refine ⟨317223023363242431469955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3383712249207919269012853 317223023363242431469955)
                ·
                  refine ⟨475834535044863647204933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317223023363242431469955 475834535044863647204933)
                  ·
                    refine ⟨89218975320911933850925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 475834535044863647204933 89218975320911933850925)
                    ·
                      rfl

theorem cell23_521260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 1, 4].length) (baseStart_521260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521260 prefixEnd_521260 := by exact prefixLift 521260
  have htrace : WordTrace (prefixWord ++ tailWord_521260) baseStart_521260 baseEnd_521260 := by
    simpa [prefixWord, tailWord_521260, baseEnd_521260] using wordTrace_append hprefix tailTrace_521260
  have hstable : (prefixWord ++ tailWord_521260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521260).length < 2 ^ (prefixWord ++ tailWord_521260).sum := by decide
  have hdescent : baseEnd_521260 < baseStart_521260 := by decide
  rcases family_descends (prefixWord ++ tailWord_521260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521273 : List Nat := [1, 2, 1, 5, 2, 1, 1, 4, 6]
def baseStart_521273 : Nat := 118140960795 + 521273 * 2 ^ 59
def prefixEnd_521273 : Nat := 4983230072969 + 3 ^ 40 * 521273 * 2
def baseEnd_521273 : Nat := 29740400134582694521135

theorem tailTrace_521273 : CollatzResearch.WordTrace tailWord_521273 prefixEnd_521273 29740400134582694521135 := by
  unfold tailWord_521273
  simp only [CollatzResearch.WordTrace]
  refine ⟨19012388240524422185760473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12674925493682948123840315 19012388240524422185760473)
  ·
    refine ⟨14259291180393316639320355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19012388240524422185760473 14259291180393316639320355)
    ·
      refine ⟨21388936770589974958980533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14259291180393316639320355 21388936770589974958980533)
      ·
        refine ⟨2005212822242810152404425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21388936770589974958980533 2005212822242810152404425)
        ·
          refine ⟨1503909616682107614303319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2005212822242810152404425 1503909616682107614303319)
          ·
            refine ⟨2255864425023161421454979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503909616682107614303319 2255864425023161421454979)
            ·
              refine ⟨3383796637534742132182469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255864425023161421454979 3383796637534742132182469)
              ·
                refine ⟨634461869537764149784213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3383796637534742132182469 634461869537764149784213)
                ·
                  refine ⟨29740400134582694521135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 634461869537764149784213 29740400134582694521135)
                  ·
                    rfl

theorem cell23_521273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 6].length) (baseStart_521273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521273 prefixEnd_521273 := by exact prefixLift 521273
  have htrace : WordTrace (prefixWord ++ tailWord_521273) baseStart_521273 baseEnd_521273 := by
    simpa [prefixWord, tailWord_521273, baseEnd_521273] using wordTrace_append hprefix tailTrace_521273
  have hstable : (prefixWord ++ tailWord_521273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521273).length < 2 ^ (prefixWord ++ tailWord_521273).sum := by decide
  have hdescent : baseEnd_521273 < baseStart_521273 := by decide
  rcases family_descends (prefixWord ++ tailWord_521273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521277 : List Nat := [1, 4, 1, 3, 1, 3, 1, 4, 1, 4]
def baseStart_521277 : Nat := 118140960795 + 521277 * 2 ^ 59
def prefixEnd_521277 : Nat := 4983230072969 + 3 ^ 40 * 521277 * 2
def baseEnd_521277 : Nat := 89221885044620745013399

theorem tailTrace_521277 : CollatzResearch.WordTrace tailWord_521277 prefixEnd_521277 89221885044620745013399 := by
  unfold tailWord_521277
  simp only [CollatzResearch.WordTrace]
  refine ⟨19012534132509930868906085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12675022755006620579270723 19012534132509930868906085)
  ·
    refine ⟨3564850149845612037919891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19012534132509930868906085 3564850149845612037919891)
    ·
      refine ⟨5347275224768418056879837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3564850149845612037919891 5347275224768418056879837)
      ·
        refine ⟨2005228209288156771329939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5347275224768418056879837 2005228209288156771329939)
        ·
          refine ⟨3007842313932235156994909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2005228209288156771329939 3007842313932235156994909)
          ·
            refine ⟨1127940867724588183873091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3007842313932235156994909 1127940867724588183873091)
            ·
              refine ⟨1691911301586882275809637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127940867724588183873091 1691911301586882275809637)
              ·
                refine ⟨317233369047540426714307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1691911301586882275809637 317233369047540426714307)
                ·
                  refine ⟨475850053571310640071461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317233369047540426714307 475850053571310640071461)
                  ·
                    refine ⟨89221885044620745013399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 475850053571310640071461 89221885044620745013399)
                    ·
                      rfl

theorem cell23_521277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_521277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521277 prefixEnd_521277 := by exact prefixLift 521277
  have htrace : WordTrace (prefixWord ++ tailWord_521277) baseStart_521277 baseEnd_521277 := by
    simpa [prefixWord, tailWord_521277, baseEnd_521277] using wordTrace_append hprefix tailTrace_521277
  have hstable : (prefixWord ++ tailWord_521277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521277).length < 2 ^ (prefixWord ++ tailWord_521277).sum := by decide
  have hdescent : baseEnd_521277 < baseStart_521277 := by decide
  rcases family_descends (prefixWord ++ tailWord_521277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521300 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_521300 : Nat := 118140960795 + 521300 * 2 ^ 59
def prefixEnd_521300 : Nat := 4983230072969 + 3 ^ 40 * 521300 * 2
def baseEnd_521300 : Nat := 267677465188915645052591

theorem tailTrace_521300 : CollatzResearch.WordTrace tailWord_521300 prefixEnd_521300 267677465188915645052591 := by
  unfold tailWord_521300
  simp only [CollatzResearch.WordTrace]
  refine ⟨9506686505713302898496677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12675582007617737197995569 9506686505713302898496677)
  ·
    refine ⟨1782503719821244293468127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9506686505713302898496677 1782503719821244293468127)
    ·
      refine ⟨2673755579731866440202191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1782503719821244293468127 2673755579731866440202191)
      ·
        refine ⟨4010633369597799660303287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2673755579731866440202191 4010633369597799660303287)
        ·
          refine ⟨6015950054396699490454931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4010633369597799660303287 6015950054396699490454931)
          ·
            refine ⟨9023925081595049235682397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6015950054396699490454931 9023925081595049235682397)
            ·
              refine ⟨3383971905598143463380899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9023925081595049235682397 3383971905598143463380899)
              ·
                refine ⟨5075957858397215195071349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3383971905598143463380899 5075957858397215195071349)
                ·
                  refine ⟨475871049224738924537939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5075957858397215195071349 475871049224738924537939)
                  ·
                    refine ⟨713806573837108386806909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 475871049224738924537939 713806573837108386806909)
                    ·
                      refine ⟨267677465188915645052591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 713806573837108386806909 267677465188915645052591)
                      ·
                        rfl

theorem cell23_521300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_521300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521300 prefixEnd_521300 := by exact prefixLift 521300
  have htrace : WordTrace (prefixWord ++ tailWord_521300) baseStart_521300 baseEnd_521300 := by
    simpa [prefixWord, tailWord_521300, baseEnd_521300] using wordTrace_append hprefix tailTrace_521300
  have hstable : (prefixWord ++ tailWord_521300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521300).length < 2 ^ (prefixWord ++ tailWord_521300).sum := by decide
  have hdescent : baseEnd_521300 < baseStart_521300 := by decide
  rcases family_descends (prefixWord ++ tailWord_521300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521303 : List Nat := [1, 1, 3, 2, 2, 1, 1, 6, 1, 5]
def baseStart_521303 : Nat := 118140960795 + 521303 * 2 ^ 59
def prefixEnd_521303 : Nat := 4983230072969 + 3 ^ 40 * 521303 * 2
def baseEnd_521303 : Nat := 89226335210293044438359

theorem tailTrace_521303 : CollatzResearch.WordTrace tailWord_521303 prefixEnd_521303 89226335210293044438359 := by
  unfold tailWord_521303
  simp only [CollatzResearch.WordTrace]
  refine ⟨19013482430415737309352563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12675654953610491539568375 19013482430415737309352563)
  ·
    refine ⟨28520223645623605964028845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19013482430415737309352563 28520223645623605964028845)
    ·
      refine ⟨10695083867108852236510817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28520223645623605964028845 10695083867108852236510817)
      ·
        refine ⟨8021312900331639177383113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10695083867108852236510817 8021312900331639177383113)
        ·
          refine ⟨6015984675248729383037335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8021312900331639177383113 6015984675248729383037335)
          ·
            refine ⟨9023977012873094074556003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6015984675248729383037335 9023977012873094074556003)
            ·
              refine ⟨13535965519309641111834005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9023977012873094074556003 13535965519309641111834005)
              ·
                refine ⟨634498383717639427117219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13535965519309641111834005 634498383717639427117219)
                ·
                  refine ⟨951747575576459140675829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 634498383717639427117219 951747575576459140675829)
                  ·
                    refine ⟨89226335210293044438359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 951747575576459140675829 89226335210293044438359)
                    ·
                      rfl

theorem cell23_521303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_521303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521303 prefixEnd_521303 := by exact prefixLift 521303
  have htrace : WordTrace (prefixWord ++ tailWord_521303) baseStart_521303 baseEnd_521303 := by
    simpa [prefixWord, tailWord_521303, baseEnd_521303] using wordTrace_append hprefix tailTrace_521303
  have hstable : (prefixWord ++ tailWord_521303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521303).length < 2 ^ (prefixWord ++ tailWord_521303).sum := by decide
  have hdescent : baseEnd_521303 < baseStart_521303 := by decide
  rcases family_descends (prefixWord ++ tailWord_521303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521323 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 3, 8, 2]
def baseStart_521323 : Nat := 118140960795 + 521323 * 2 ^ 59
def prefixEnd_521323 : Nat := 4983230072969 + 3 ^ 40 * 521323 * 2
def baseEnd_521323 : Nat := 267689275243969055064985

theorem tailTrace_521323 : CollatzResearch.WordTrace tailWord_521323 prefixEnd_521323 267689275243969055064985 := by
  unfold tailWord_521323
  simp only [CollatzResearch.WordTrace]
  refine ⟨19014211890343280725080623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12676141260228853816720415 19014211890343280725080623)
  ·
    refine ⟨28521317835514921087620935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19014211890343280725080623 28521317835514921087620935)
    ·
      refine ⟨42781976753272381631431403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28521317835514921087620935 42781976753272381631431403)
      ·
        refine ⟨64172965129908572447147105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42781976753272381631431403 64172965129908572447147105)
        ·
          refine ⟨48129723847431429335360329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64172965129908572447147105 48129723847431429335360329)
          ·
            refine ⟨36097292885573572001520247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48129723847431429335360329 36097292885573572001520247)
            ·
              refine ⟨54145939328360358002280371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36097292885573572001520247 54145939328360358002280371)
              ·
                refine ⟨81218908992540537003420557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54145939328360358002280371 81218908992540537003420557)
                ·
                  refine ⟨30457090872202701376282709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81218908992540537003420557 30457090872202701376282709)
                  ·
                    refine ⟨356919033658625406753313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30457090872202701376282709 356919033658625406753313)
                    ·
                      refine ⟨267689275243969055064985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 356919033658625406753313 267689275243969055064985)
                      ·
                        rfl

theorem cell23_521323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 8, 2].length) (baseStart_521323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521323 prefixEnd_521323 := by exact prefixLift 521323
  have htrace : WordTrace (prefixWord ++ tailWord_521323) baseStart_521323 baseEnd_521323 := by
    simpa [prefixWord, tailWord_521323, baseEnd_521323] using wordTrace_append hprefix tailTrace_521323
  have hstable : (prefixWord ++ tailWord_521323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521323).length < 2 ^ (prefixWord ++ tailWord_521323).sum := by decide
  have hdescent : baseEnd_521323 < baseStart_521323 := by decide
  rcases family_descends (prefixWord ++ tailWord_521323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521334 : List Nat := [5, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3]
def baseStart_521334 : Nat := 118140960795 + 521334 * 2 ^ 59
def prefixEnd_521334 : Nat := 4983230072969 + 3 ^ 40 * 521334 * 2
def baseEnd_521334 : Nat := 267694923531168512027435

theorem tailTrace_521334 : CollatzResearch.WordTrace tailWord_521334 prefixEnd_521334 267694923531168512027435 := by
  unfold tailWord_521334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1188413318331464350233191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12676408728868953069154037 1188413318331464350233191)
  ·
    refine ⟨1782619977497196525349787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1188413318331464350233191 1782619977497196525349787)
    ·
      refine ⟨2673929966245794788024681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1782619977497196525349787 2673929966245794788024681)
      ·
        refine ⟨2005447474684346091018511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2673929966245794788024681 2005447474684346091018511)
        ·
          refine ⟨3008171212026519136527767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2005447474684346091018511 3008171212026519136527767)
          ·
            refine ⟨4512256818039778704791651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3008171212026519136527767 4512256818039778704791651)
            ·
              refine ⟨6768385227059668057187477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4512256818039778704791651 6768385227059668057187477)
              ·
                refine ⟨317268057518421940180663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6768385227059668057187477 317268057518421940180663)
                ·
                  refine ⟨475902086277632910270995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317268057518421940180663 475902086277632910270995)
                  ·
                    refine ⟨713853129416449365406493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 475902086277632910270995 713853129416449365406493)
                    ·
                      refine ⟨267694923531168512027435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 713853129416449365406493 267694923531168512027435)
                      ·
                        rfl

theorem cell23_521334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_521334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521334 prefixEnd_521334 := by exact prefixLift 521334
  have htrace : WordTrace (prefixWord ++ tailWord_521334) baseStart_521334 baseEnd_521334 := by
    simpa [prefixWord, tailWord_521334, baseEnd_521334] using wordTrace_append hprefix tailTrace_521334
  have hstable : (prefixWord ++ tailWord_521334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521334).length < 2 ^ (prefixWord ++ tailWord_521334).sum := by decide
  have hdescent : baseEnd_521334 < baseStart_521334 := by decide
  rcases family_descends (prefixWord ++ tailWord_521334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521353 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 1, 1, 6]
def baseStart_521353 : Nat := 118140960795 + 521353 * 2 ^ 59
def prefixEnd_521353 : Nat := 4983230072969 + 3 ^ 40 * 521353 * 2
def baseEnd_521353 : Nat := 267704679663603937689847

theorem tailTrace_521353 : CollatzResearch.WordTrace tailWord_521353 prefixEnd_521353 267704679663603937689847 := by
  unfold tailWord_521353
  simp only [CollatzResearch.WordTrace]
  refine ⟨19015306080234595848672713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12676870720156397232448475 19015306080234595848672713)
  ·
    refine ⟨14261479560175946886504535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19015306080234595848672713 14261479560175946886504535)
    ·
      refine ⟨21392219340263920329756803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14261479560175946886504535 21392219340263920329756803)
      ·
        refine ⟨32088329010395880494635205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21392219340263920329756803 32088329010395880494635205)
        ·
          refine ⟨6016561689449227592744101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32088329010395880494635205 6016561689449227592744101)
          ·
            refine ⟨1128105316771730173639519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6016561689449227592744101 1128105316771730173639519)
            ·
              refine ⟨1692157975157595260459279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128105316771730173639519 1692157975157595260459279)
              ·
                refine ⟨2538236962736392890688919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692157975157595260459279 2538236962736392890688919)
                ·
                  refine ⟨3807355444104589336033379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538236962736392890688919 3807355444104589336033379)
                  ·
                    refine ⟨5711033166156884004050069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3807355444104589336033379 5711033166156884004050069)
                    ·
                      refine ⟨267704679663603937689847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5711033166156884004050069 267704679663603937689847)
                      ·
                        rfl

theorem cell23_521353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 1, 6].length) (baseStart_521353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521353 prefixEnd_521353 := by exact prefixLift 521353
  have htrace : WordTrace (prefixWord ++ tailWord_521353) baseStart_521353 baseEnd_521353 := by
    simpa [prefixWord, tailWord_521353, baseEnd_521353] using wordTrace_append hprefix tailTrace_521353
  have hstable : (prefixWord ++ tailWord_521353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521353).length < 2 ^ (prefixWord ++ tailWord_521353).sum := by decide
  have hdescent : baseEnd_521353 < baseStart_521353 := by decide
  rcases family_descends (prefixWord ++ tailWord_521353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521363 : List Nat := [1, 1, 1, 2, 1, 2, 8, 7]
def baseStart_521363 : Nat := 118140960795 + 521363 * 2 ^ 59
def prefixEnd_521363 : Nat := 4983230072969 + 3 ^ 40 * 521363 * 2
def baseEnd_521363 : Nat := 9915178313709218465363

theorem tailTrace_521363 : CollatzResearch.WordTrace tailWord_521363 prefixEnd_521363 9915178313709218465363 := by
  unfold tailWord_521363
  simp only [CollatzResearch.WordTrace]
  refine ⟨19015670810198367556536743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12677113873465578371024495 19015670810198367556536743)
  ·
    refine ⟨28523506215297551334805115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19015670810198367556536743 28523506215297551334805115)
    ·
      refine ⟨42785259322946327002207673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28523506215297551334805115 42785259322946327002207673)
      ·
        refine ⟨32088944492209745251655755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42785259322946327002207673 32088944492209745251655755)
        ·
          refine ⟨48133416738314617877483633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32088944492209745251655755 48133416738314617877483633)
          ·
            refine ⟨36100062553735963408112725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48133416738314617877483633 36100062553735963408112725)
            ·
              refine ⟨423047608051593321188821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 36100062553735963408112725 423047608051593321188821)
              ·
                refine ⟨9915178313709218465363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 423047608051593321188821 9915178313709218465363)
                ·
                  rfl

theorem cell23_521363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 7].length) (baseStart_521363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521363 prefixEnd_521363 := by exact prefixLift 521363
  have htrace : WordTrace (prefixWord ++ tailWord_521363) baseStart_521363 baseEnd_521363 := by
    simpa [prefixWord, tailWord_521363, baseEnd_521363] using wordTrace_append hprefix tailTrace_521363
  have hstable : (prefixWord ++ tailWord_521363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521363).length < 2 ^ (prefixWord ++ tailWord_521363).sum := by decide
  have hdescent : baseEnd_521363 < baseStart_521363 := by decide
  rcases family_descends (prefixWord ++ tailWord_521363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521450 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_521450 : Nat := 118140960795 + 521450 * 2 ^ 59
def prefixEnd_521450 : Nat := 4983230072969 + 3 ^ 40 * 521450 * 2
def baseEnd_521450 : Nat := 267754487287090058176901

theorem tailTrace_521450 : CollatzResearch.WordTrace tailWord_521450 prefixEnd_521450 267754487287090058176901 := by
  unfold tailWord_521450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4754710990220795353738451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12679229307255454276635869 4754710990220795353738451)
  ·
    refine ⟨7132066485331193030607677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4754710990220795353738451 7132066485331193030607677)
    ·
      refine ⟨2674524931999197386477879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7132066485331193030607677 2674524931999197386477879)
      ·
        refine ⟨4011787397998796079716819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2674524931999197386477879 4011787397998796079716819)
        ·
          refine ⟨6017681096998194119575229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4011787397998796079716819 6017681096998194119575229)
          ·
            refine ⟨2256630411374322794840711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6017681096998194119575229 2256630411374322794840711)
            ·
              refine ⟨3384945617061484192261067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2256630411374322794840711 3384945617061484192261067)
              ·
                refine ⟨5077418425592226288391601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3384945617061484192261067 5077418425592226288391601)
                ·
                  refine ⟨3808063819194169716293701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5077418425592226288391601 3808063819194169716293701)
                  ·
                    refine ⟨714011966098906821805069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3808063819194169716293701 714011966098906821805069)
                    ·
                      refine ⟨267754487287090058176901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 714011966098906821805069 267754487287090058176901)
                      ·
                        rfl

theorem cell23_521450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_521450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521450 prefixEnd_521450 := by exact prefixLift 521450
  have htrace : WordTrace (prefixWord ++ tailWord_521450) baseStart_521450 baseEnd_521450 := by
    simpa [prefixWord, tailWord_521450, baseEnd_521450] using wordTrace_append hprefix tailTrace_521450
  have hstable : (prefixWord ++ tailWord_521450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521450).length < 2 ^ (prefixWord ++ tailWord_521450).sum := by decide
  have hdescent : baseEnd_521450 < baseStart_521450 := by decide
  rcases family_descends (prefixWord ++ tailWord_521450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521470 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 9]
def baseStart_521470 : Nat := 118140960795 + 521470 * 2 ^ 59
def prefixEnd_521470 : Nat := 4983230072969 + 3 ^ 40 * 521470 * 2
def baseEnd_521470 : Nat := 29751639655575553325201

theorem tailTrace_521470 : CollatzResearch.WordTrace tailWord_521470 prefixEnd_521470 29751639655575553325201 := by
  unfold tailWord_521470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2377446677601340603835233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12679715613873816553787909 2377446677601340603835233)
  ·
    refine ⟨1783085008201005452876425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2377446677601340603835233 1783085008201005452876425)
    ·
      refine ⟨1337313756150754089657319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1783085008201005452876425 1337313756150754089657319)
      ·
        refine ⟨2005970634226131134485979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1337313756150754089657319 2005970634226131134485979)
        ·
          refine ⟨3008955951339196701728969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2005970634226131134485979 3008955951339196701728969)
          ·
            refine ⟨2256716963504397526296727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3008955951339196701728969 2256716963504397526296727)
            ·
              refine ⟨3385075445256596289445091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2256716963504397526296727 3385075445256596289445091)
              ·
                refine ⟨5077613167884894434167637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3385075445256596289445091 5077613167884894434167637)
                ·
                  refine ⟨29751639655575553325201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5077613167884894434167637 29751639655575553325201)
                  ·
                    rfl

theorem cell23_521470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_521470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521470 prefixEnd_521470 := by exact prefixLift 521470
  have htrace : WordTrace (prefixWord ++ tailWord_521470) baseStart_521470 baseEnd_521470 := by
    simpa [prefixWord, tailWord_521470, baseEnd_521470] using wordTrace_append hprefix tailTrace_521470
  have hstable : (prefixWord ++ tailWord_521470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521470).length < 2 ^ (prefixWord ++ tailWord_521470).sum := by decide
  have hdescent : baseEnd_521470 < baseStart_521470 := by decide
  rcases family_descends (prefixWord ++ tailWord_521470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521500 : List Nat := [2, 2, 3, 1, 1, 1, 2, 4, 2, 5]
def baseStart_521500 : Nat := 118140960795 + 521500 * 2 ^ 59
def prefixEnd_521500 : Nat := 4983230072969 + 3 ^ 40 * 521500 * 2
def baseEnd_521500 : Nat := 89260053773271620850557

theorem tailTrace_521500 : CollatzResearch.WordTrace tailWord_521500 prefixEnd_521500 89260053773271620850557 := by
  unfold tailWord_521500
  simp only [CollatzResearch.WordTrace]
  refine ⟨9510333805351019977136977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12680445073801359969515969 9510333805351019977136977)
  ·
    refine ⟨7132750354013264982852733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9510333805351019977136977 7132750354013264982852733)
    ·
      refine ⟨2674781382754974368569775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7132750354013264982852733 2674781382754974368569775)
      ·
        refine ⟨4012172074132461552854663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2674781382754974368569775 4012172074132461552854663)
        ·
          refine ⟨6018258111198692329281995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012172074132461552854663 6018258111198692329281995)
          ·
            refine ⟨9027387166798038493922993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6018258111198692329281995 9027387166798038493922993)
            ·
              refine ⟨6770540375098528870442245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9027387166798038493922993 6770540375098528870442245)
              ·
                refine ⟨1269476320330974163207921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6770540375098528870442245 1269476320330974163207921)
                ·
                  refine ⟨952107240248230622405941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1269476320330974163207921 952107240248230622405941)
                  ·
                    refine ⟨89260053773271620850557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 952107240248230622405941 89260053773271620850557)
                    ·
                      rfl

theorem cell23_521500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_521500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521500 prefixEnd_521500 := by exact prefixLift 521500
  have htrace : WordTrace (prefixWord ++ tailWord_521500) baseStart_521500 baseEnd_521500 := by
    simpa [prefixWord, tailWord_521500, baseEnd_521500] using wordTrace_append hprefix tailTrace_521500
  have hstable : (prefixWord ++ tailWord_521500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521500).length < 2 ^ (prefixWord ++ tailWord_521500).sum := by decide
  have hdescent : baseEnd_521500 < baseStart_521500 := by decide
  rcases family_descends (prefixWord ++ tailWord_521500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521517 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_521517 : Nat := 118140960795 + 521517 * 2 ^ 59
def prefixEnd_521517 : Nat := 4983230072969 + 3 ^ 40 * 521517 * 2
def baseEnd_521517 : Nat := 89262963496980432013031

theorem tailTrace_521517 : CollatzResearch.WordTrace tailWord_521517 prefixEnd_521517 89262963496980432013031 := by
  unfold tailWord_521517
  simp only [CollatzResearch.WordTrace]
  refine ⟨19021287651640451857642805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12680858434426967905095203 19021287651640451857642805)
  ·
    refine ⟨1783245717341292361654013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19021287651640451857642805 1783245717341292361654013)
    ·
      refine ⟨668717144002984635620255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1783245717341292361654013 668717144002984635620255)
      ·
        refine ⟨1003075716004476953430383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668717144002984635620255 1003075716004476953430383)
        ·
          refine ⟨1504613574006715430145575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003075716004476953430383 1504613574006715430145575)
          ·
            refine ⟨2256920361010073145218363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504613574006715430145575 2256920361010073145218363)
            ·
              refine ⟨3385380541515109717827545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2256920361010073145218363 3385380541515109717827545)
              ·
                refine ⟨2539035406136332288370659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3385380541515109717827545 2539035406136332288370659)
                ·
                  refine ⟨3808553109204498432555989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2539035406136332288370659 3808553109204498432555989)
                  ·
                    refine ⟨89262963496980432013031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3808553109204498432555989 89262963496980432013031)
                    ·
                      rfl

theorem cell23_521517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_521517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521517 prefixEnd_521517 := by exact prefixLift 521517
  have htrace : WordTrace (prefixWord ++ tailWord_521517) baseStart_521517 baseEnd_521517 := by
    simpa [prefixWord, tailWord_521517, baseEnd_521517] using wordTrace_append hprefix tailTrace_521517
  have hstable : (prefixWord ++ tailWord_521517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521517).length < 2 ^ (prefixWord ++ tailWord_521517).sum := by decide
  have hdescent : baseEnd_521517 < baseStart_521517 := by decide
  rcases family_descends (prefixWord ++ tailWord_521517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521537 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_521537 : Nat := 118140960795 + 521537 * 2 ^ 59
def prefixEnd_521537 : Nat := 4983230072969 + 3 ^ 40 * 521537 * 2
def baseEnd_521537 : Nat := 267799160104031217789001

theorem tailTrace_521537 : CollatzResearch.WordTrace tailWord_521537 prefixEnd_521537 267799160104031217789001 := by
  unfold tailWord_521537
  simp only [CollatzResearch.WordTrace]
  refine ⟨19022017111567995273370865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12681344741045330182247243 19022017111567995273370865)
  ·
    refine ⟨14266512833675996455028149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19022017111567995273370865 14266512833675996455028149)
    ·
      refine ⟨1337485578157124667658889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14266512833675996455028149 1337485578157124667658889)
      ·
        refine ⟨1003114183617843500744167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1337485578157124667658889 1003114183617843500744167)
        ·
          refine ⟨1504671275426765251116251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003114183617843500744167 1504671275426765251116251)
          ·
            refine ⟨2257006913140147876674377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504671275426765251116251 2257006913140147876674377)
            ·
              refine ⟨1692755184855110907505783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2257006913140147876674377 1692755184855110907505783)
              ·
                refine ⟨2539132777282666361258675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692755184855110907505783 2539132777282666361258675)
                ·
                  refine ⟨3808699165923999541888013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2539132777282666361258675 3808699165923999541888013)
                  ·
                    refine ⟨1428262187221499828208005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3808699165923999541888013 1428262187221499828208005)
                    ·
                      refine ⟨267799160104031217789001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1428262187221499828208005 267799160104031217789001)
                      ·
                        rfl

theorem cell23_521537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_521537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521537 prefixEnd_521537 := by exact prefixLift 521537
  have htrace : WordTrace (prefixWord ++ tailWord_521537) baseStart_521537 baseEnd_521537 := by
    simpa [prefixWord, tailWord_521537, baseEnd_521537] using wordTrace_append hprefix tailTrace_521537
  have hstable : (prefixWord ++ tailWord_521537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521537).length < 2 ^ (prefixWord ++ tailWord_521537).sum := by decide
  have hdescent : baseEnd_521537 < baseStart_521537 := by decide
  rcases family_descends (prefixWord ++ tailWord_521537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521557 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 4, 2, 3]
def baseStart_521557 : Nat := 118140960795 + 521557 * 2 ^ 59
def prefixEnd_521557 : Nat := 4983230072969 + 3 ^ 40 * 521557 * 2
def baseEnd_521557 : Nat := 267809429717121139538909

theorem tailTrace_521557 : CollatzResearch.WordTrace tailWord_521557 prefixEnd_521557 267809429717121139538909 := by
  unfold tailWord_521557
  simp only [CollatzResearch.WordTrace]
  refine ⟨19022746571495538689098925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12681831047663692459399283 19022746571495538689098925)
  ·
    refine ⟨7133529964310827008412097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19022746571495538689098925 7133529964310827008412097)
    ·
      refine ⟨5350147473233120256309073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7133529964310827008412097 5350147473233120256309073)
      ·
        refine ⟨4012610604924840192231805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5350147473233120256309073 4012610604924840192231805)
        ·
          refine ⟨1504728976846815072086927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4012610604924840192231805 1504728976846815072086927)
          ·
            refine ⟨2257093465270222608130391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504728976846815072086927 2257093465270222608130391)
            ·
              refine ⟨3385640197905333912195587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2257093465270222608130391 3385640197905333912195587)
              ·
                refine ⟨5078460296858000868293381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3385640197905333912195587 5078460296858000868293381)
                ·
                  refine ⟨952211305660875162805009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5078460296858000868293381 952211305660875162805009)
                  ·
                    refine ⟨714158479245656372103757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 952211305660875162805009 714158479245656372103757)
                    ·
                      refine ⟨267809429717121139538909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 714158479245656372103757 267809429717121139538909)
                      ·
                        rfl

theorem cell23_521557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_521557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521557 prefixEnd_521557 := by exact prefixLift 521557
  have htrace : WordTrace (prefixWord ++ tailWord_521557) baseStart_521557 baseEnd_521557 := by
    simpa [prefixWord, tailWord_521557, baseEnd_521557] using wordTrace_append hprefix tailTrace_521557
  have hstable : (prefixWord ++ tailWord_521557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521557).length < 2 ^ (prefixWord ++ tailWord_521557).sum := by decide
  have hdescent : baseEnd_521557 < baseStart_521557 := by decide
  rcases family_descends (prefixWord ++ tailWord_521557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521560 : List Nat := [2, 1, 2, 2, 1, 1, 4, 4, 6]
def baseStart_521560 : Nat := 118140960795 + 521560 * 2 ^ 59
def prefixEnd_521560 : Nat := 4983230072969 + 3 ^ 40 * 521560 * 2
def baseEnd_521560 : Nat := 29756774462120514200155

theorem tailTrace_521560 : CollatzResearch.WordTrace tailWord_521560 prefixEnd_521560 29756774462120514200155 := by
  unfold tailWord_521560
  simp only [CollatzResearch.WordTrace]
  refine ⟨9511427995242335100729067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12681903993656446800972089 9511427995242335100729067)
  ·
    refine ⟨14267141992863502651093601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9511427995242335100729067 14267141992863502651093601)
    ·
      refine ⟨10700356494647626988320201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14267141992863502651093601 10700356494647626988320201)
      ·
        refine ⟨8025267370985720241240151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10700356494647626988320201 8025267370985720241240151)
        ·
          refine ⟨12037901056478580361860227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8025267370985720241240151 12037901056478580361860227)
          ·
            refine ⟨18056851584717870542790341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12037901056478580361860227 18056851584717870542790341)
            ·
              refine ⟨3385659672134600726773189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18056851584717870542790341 3385659672134600726773189)
              ·
                refine ⟨634811188525237636269973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3385659672134600726773189 634811188525237636269973)
                ·
                  refine ⟨29756774462120514200155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 634811188525237636269973 29756774462120514200155)
                  ·
                    rfl

theorem cell23_521560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 6].length) (baseStart_521560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521560 prefixEnd_521560 := by exact prefixLift 521560
  have htrace : WordTrace (prefixWord ++ tailWord_521560) baseStart_521560 baseEnd_521560 := by
    simpa [prefixWord, tailWord_521560, baseEnd_521560] using wordTrace_append hprefix tailTrace_521560
  have hstable : (prefixWord ++ tailWord_521560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521560).length < 2 ^ (prefixWord ++ tailWord_521560).sum := by decide
  have hdescent : baseEnd_521560 < baseStart_521560 := by decide
  rcases family_descends (prefixWord ++ tailWord_521560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521644 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 5, 2, 2]
def baseStart_521644 : Nat := 118140960795 + 521644 * 2 ^ 59
def prefixEnd_521644 : Nat := 4983230072969 + 3 ^ 40 * 521644 * 2
def baseEnd_521644 : Nat := 267854102534062299151009

theorem tailTrace_521644 : CollatzResearch.WordTrace tailWord_521644 prefixEnd_521644 267854102534062299151009 := by
  unfold tailWord_521644
  simp only [CollatzResearch.WordTrace]
  refine ⟨9512959861090176273757993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12683946481453568365010657 9512959861090176273757993)
  ·
    refine ⟨7134719895817632205318495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9512959861090176273757993 7134719895817632205318495)
    ·
      refine ⟨10702079843726448307977743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7134719895817632205318495 10702079843726448307977743)
      ·
        refine ⟨16053119765589672461966615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10702079843726448307977743 16053119765589672461966615)
        ·
          refine ⟨24079679648384508692949923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16053119765589672461966615 24079679648384508692949923)
          ·
            refine ⟨36119519472576763039424885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24079679648384508692949923 36119519472576763039424885)
            ·
              refine ⟨3386204950554071534946083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36119519472576763039424885 3386204950554071534946083)
              ·
                refine ⟨5079307425831107302419125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386204950554071534946083 5079307425831107302419125)
                ·
                  refine ⟨476185071171666309601793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5079307425831107302419125 476185071171666309601793)
                  ·
                    refine ⟨357138803378749732201345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 476185071171666309601793 357138803378749732201345)
                    ·
                      refine ⟨267854102534062299151009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 357138803378749732201345 267854102534062299151009)
                      ·
                        rfl

theorem cell23_521644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 2, 2].length) (baseStart_521644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521644 prefixEnd_521644 := by exact prefixLift 521644
  have htrace : WordTrace (prefixWord ++ tailWord_521644) baseStart_521644 baseEnd_521644 := by
    simpa [prefixWord, tailWord_521644, baseEnd_521644] using wordTrace_append hprefix tailTrace_521644
  have hstable : (prefixWord ++ tailWord_521644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521644).length < 2 ^ (prefixWord ++ tailWord_521644).sum := by decide
  have hdescent : baseEnd_521644 < baseStart_521644 := by decide
  rcases family_descends (prefixWord ++ tailWord_521644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521678 : List Nat := [4, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2]
def baseStart_521678 : Nat := 118140960795 + 521678 * 2 ^ 59
def prefixEnd_521678 : Nat := 4983230072969 + 3 ^ 40 * 521678 * 2
def baseEnd_521678 : Nat := 267871560876315166125853

theorem tailTrace_521678 : CollatzResearch.WordTrace tailWord_521678 prefixEnd_521678 267871560876315166125853 := by
  unfold tailWord_521678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2378394975507147044281711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12684773202704784236169125 2378394975507147044281711)
  ·
    refine ⟨3567592463260720566422567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2378394975507147044281711 3567592463260720566422567)
    ·
      refine ⟨5351388694891080849633851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3567592463260720566422567 5351388694891080849633851)
      ·
        refine ⟨8027083042336621274450777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5351388694891080849633851 8027083042336621274450777)
        ·
          refine ⟨6020312281752465955838083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8027083042336621274450777 6020312281752465955838083)
          ·
            refine ⟨9030468422628698933757125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6020312281752465955838083 9030468422628698933757125)
            ·
              refine ⟨1693212829242881050079461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9030468422628698933757125 1693212829242881050079461)
              ·
                refine ⟨317477405483040196889899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1693212829242881050079461 317477405483040196889899)
                ·
                  refine ⟨476216108224560295334849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317477405483040196889899 476216108224560295334849)
                  ·
                    refine ⟨357162081168420221501137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 476216108224560295334849 357162081168420221501137)
                    ·
                      refine ⟨267871560876315166125853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 357162081168420221501137 267871560876315166125853)
                      ·
                        rfl

theorem cell23_521678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2].length) (baseStart_521678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521678 prefixEnd_521678 := by exact prefixLift 521678
  have htrace : WordTrace (prefixWord ++ tailWord_521678) baseStart_521678 baseEnd_521678 := by
    simpa [prefixWord, tailWord_521678, baseEnd_521678] using wordTrace_append hprefix tailTrace_521678
  have hstable : (prefixWord ++ tailWord_521678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521678).length < 2 ^ (prefixWord ++ tailWord_521678).sum := by decide
  have hdescent : baseEnd_521678 < baseStart_521678 := by decide
  rcases family_descends (prefixWord ++ tailWord_521678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521737 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 2, 4, 3]
def baseStart_521737 : Nat := 118140960795 + 521737 * 2 ^ 59
def prefixEnd_521737 : Nat := 4983230072969 + 3 ^ 40 * 521737 * 2
def baseEnd_521737 : Nat := 267901856234930435288081

theorem tailTrace_521737 : CollatzResearch.WordTrace tailWord_521737 prefixEnd_521737 267901856234930435288081 := by
  unfold tailWord_521737
  simp only [CollatzResearch.WordTrace]
  refine ⟨19029311710843429430651465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12686207807228952953767643 19029311710843429430651465)
  ·
    refine ⟨14271983783132572072988599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19029311710843429430651465 14271983783132572072988599)
    ·
      refine ⟨21407975674698858109482899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14271983783132572072988599 21407975674698858109482899)
      ·
        refine ⟨32111963512048287164224349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21407975674698858109482899 32111963512048287164224349)
        ·
          refine ⟨12041986317018107686584131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32111963512048287164224349 12041986317018107686584131)
          ·
            refine ⟨18062979475527161529876197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12041986317018107686584131 18062979475527161529876197)
            ·
              refine ⟨3386808651661342786851787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18062979475527161529876197 3386808651661342786851787)
              ·
                refine ⟨5080212977492014180277681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386808651661342786851787 5080212977492014180277681)
                ·
                  refine ⟨3810159733119010635208261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5080212977492014180277681 3810159733119010635208261)
                  ·
                    refine ⟨714404949959814494101549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3810159733119010635208261 714404949959814494101549)
                    ·
                      refine ⟨267901856234930435288081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 714404949959814494101549 267901856234930435288081)
                      ·
                        rfl

theorem cell23_521737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 4, 3].length) (baseStart_521737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521737 prefixEnd_521737 := by exact prefixLift 521737
  have htrace : WordTrace (prefixWord ++ tailWord_521737) baseStart_521737 baseEnd_521737 := by
    simpa [prefixWord, tailWord_521737, baseEnd_521737] using wordTrace_append hprefix tailTrace_521737
  have hstable : (prefixWord ++ tailWord_521737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521737).length < 2 ^ (prefixWord ++ tailWord_521737).sum := by decide
  have hdescent : baseEnd_521737 < baseStart_521737 := by decide
  rcases family_descends (prefixWord ++ tailWord_521737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521757 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 9]
def baseStart_521757 : Nat := 118140960795 + 521757 * 2 ^ 59
def prefixEnd_521757 : Nat := 4983230072969 + 3 ^ 40 * 521757 * 2
def baseEnd_521757 : Nat := 29768013983113373004221

theorem tailTrace_521757 : CollatzResearch.WordTrace tailWord_521757 prefixEnd_521757 29768013983113373004221 := by
  unfold tailWord_521757
  simp only [CollatzResearch.WordTrace]
  refine ⟨19030041170770972846379525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12686694113847315230919683 19030041170770972846379525)
  ·
    refine ⟨3568132719519557408696161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19030041170770972846379525 3568132719519557408696161)
    ·
      refine ⟨2676099539639668056522121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3568132719519557408696161 2676099539639668056522121)
      ·
        refine ⟨2007074654729751042391591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2676099539639668056522121 2007074654729751042391591)
        ·
          refine ⟨3010611982094626563587387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2007074654729751042391591 3010611982094626563587387)
          ·
            refine ⟨4515917973141939845381081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3010611982094626563587387 4515917973141939845381081)
            ·
              refine ⟨3386938479856454884035811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4515917973141939845381081 3386938479856454884035811)
              ·
                refine ⟨5080407719784682326053717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386938479856454884035811 5080407719784682326053717)
                ·
                  refine ⟨29768013983113373004221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5080407719784682326053717 29768013983113373004221)
                  ·
                    rfl

theorem cell23_521757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_521757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521757 prefixEnd_521757 := by exact prefixLift 521757
  have htrace : WordTrace (prefixWord ++ tailWord_521757) baseStart_521757 baseEnd_521757 := by
    simpa [prefixWord, tailWord_521757, baseEnd_521757] using wordTrace_append hprefix tailTrace_521757
  have hstable : (prefixWord ++ tailWord_521757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521757).length < 2 ^ (prefixWord ++ tailWord_521757).sum := by decide
  have hdescent : baseEnd_521757 < baseStart_521757 := by decide
  rcases family_descends (prefixWord ++ tailWord_521757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521768 : List Nat := [2, 1, 5, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_521768 : Nat := 118140960795 + 521768 * 2 ^ 59
def prefixEnd_521768 : Nat := 4983230072969 + 3 ^ 40 * 521768 * 2
def baseEnd_521768 : Nat := 267917774135219814000439

theorem tailTrace_521768 : CollatzResearch.WordTrace tailWord_521768 prefixEnd_521768 267917774135219814000439 := by
  unfold tailWord_521768
  simp only [CollatzResearch.WordTrace]
  refine ⟨9515221186865560862514979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12686961582487414483353305 9515221186865560862514979)
  ·
    refine ⟨14272831780298341293772469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9515221186865560862514979 14272831780298341293772469)
    ·
      refine ⟨1338077979402969496291169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14272831780298341293772469 1338077979402969496291169)
      ·
        refine ⟨1003558484552227122218377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1338077979402969496291169 1003558484552227122218377)
        ·
          refine ⟨752668863414170341663783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1003558484552227122218377 752668863414170341663783)
          ·
            refine ⟨1129003295121255512495675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752668863414170341663783 1129003295121255512495675)
            ·
              refine ⟨1693504942681883268743513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129003295121255512495675 1693504942681883268743513)
              ·
                refine ⟨1270128707011412451557635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1693504942681883268743513 1270128707011412451557635)
                ·
                  refine ⟨1905193060517118677336453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1270128707011412451557635 1905193060517118677336453)
                  ·
                    refine ⟨357223698846959752000585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1905193060517118677336453 357223698846959752000585)
                    ·
                      refine ⟨267917774135219814000439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 357223698846959752000585 267917774135219814000439)
                      ·
                        rfl

theorem cell23_521768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_521768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521768 prefixEnd_521768 := by exact prefixLift 521768
  have htrace : WordTrace (prefixWord ++ tailWord_521768) baseStart_521768 baseEnd_521768 := by
    simpa [prefixWord, tailWord_521768, baseEnd_521768] using wordTrace_append hprefix tailTrace_521768
  have hstable : (prefixWord ++ tailWord_521768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521768).length < 2 ^ (prefixWord ++ tailWord_521768).sum := by decide
  have hdescent : baseEnd_521768 < baseStart_521768 := by decide
  rcases family_descends (prefixWord ++ tailWord_521768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521791 : List Nat := [1, 1, 2, 2, 3, 3, 4, 2, 5]
def baseStart_521791 : Nat := 118140960795 + 521791 * 2 ^ 59
def prefixEnd_521791 : Nat := 4983230072969 + 3 ^ 40 * 521791 * 2
def baseEnd_521791 : Nat := 29769953798919247112537

theorem tailTrace_521791 : CollatzResearch.WordTrace tailWord_521791 prefixEnd_521791 29769953798919247112537 := by
  unfold tailWord_521791
  simp only [CollatzResearch.WordTrace]
  refine ⟨19031281252647796653117227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12687520835098531102078151 19031281252647796653117227)
  ·
    refine ⟨28546921878971694979675841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19031281252647796653117227 28546921878971694979675841)
    ·
      refine ⟨21410191409228771234756881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28546921878971694979675841 21410191409228771234756881)
      ·
        refine ⟨16057643556921578426067661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21410191409228771234756881 16057643556921578426067661)
        ·
          refine ⟨6021616333845591909775373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16057643556921578426067661 6021616333845591909775373)
          ·
            refine ⟨2258106125192096966165765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6021616333845591909775373 2258106125192096966165765)
            ·
              refine ⟨423394898473518181156081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2258106125192096966165765 423394898473518181156081)
              ·
                refine ⟨317546173855138635867061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423394898473518181156081 317546173855138635867061)
                ·
                  refine ⟨29769953798919247112537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 317546173855138635867061 29769953798919247112537)
                  ·
                    rfl

theorem cell23_521791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 5].length) (baseStart_521791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521791 prefixEnd_521791 := by exact prefixLift 521791
  have htrace : WordTrace (prefixWord ++ tailWord_521791) baseStart_521791 baseEnd_521791 := by
    simpa [prefixWord, tailWord_521791, baseEnd_521791] using wordTrace_append hprefix tailTrace_521791
  have hstable : (prefixWord ++ tailWord_521791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521791).length < 2 ^ (prefixWord ++ tailWord_521791).sum := by decide
  have hdescent : baseEnd_521791 < baseStart_521791 := by decide
  rcases family_descends (prefixWord ++ tailWord_521791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521797 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 1, 2, 5]
def baseStart_521797 : Nat := 118140960795 + 521797 * 2 ^ 59
def prefixEnd_521797 : Nat := 4983230072969 + 3 ^ 40 * 521797 * 2
def baseEnd_521797 : Nat := 267932665074200200537805

theorem tailTrace_521797 : CollatzResearch.WordTrace tailWord_521797 prefixEnd_521797 267932665074200200537805 := by
  unfold tailWord_521797
  simp only [CollatzResearch.WordTrace]
  refine ⟨19031500090626059677835645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12687666727084039785223763 19031500090626059677835645)
  ·
    refine ⟨7136812533984772379188367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19031500090626059677835645 7136812533984772379188367)
    ·
      refine ⟨10705218800977158568782551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7136812533984772379188367 10705218800977158568782551)
      ·
        refine ⟨16057828201465737853173827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10705218800977158568782551 16057828201465737853173827)
        ·
          refine ⟨24086742302198606779760741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16057828201465737853173827 24086742302198606779760741)
          ·
            refine ⟨4516264181662238771205139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24086742302198606779760741 4516264181662238771205139)
            ·
              refine ⟨6774396272493358156807709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4516264181662238771205139 6774396272493358156807709)
              ·
                refine ⟨2540398602185009308802891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6774396272493358156807709 2540398602185009308802891)
                ·
                  refine ⟨3810597903277513963204337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2540398602185009308802891 3810597903277513963204337)
                  ·
                    refine ⟨2857948427458135472403253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3810597903277513963204337 2857948427458135472403253)
                    ·
                      refine ⟨267932665074200200537805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2857948427458135472403253 267932665074200200537805)
                      ·
                        rfl

theorem cell23_521797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_521797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521797 prefixEnd_521797 := by exact prefixLift 521797
  have htrace : WordTrace (prefixWord ++ tailWord_521797) baseStart_521797 baseEnd_521797 := by
    simpa [prefixWord, tailWord_521797, baseEnd_521797] using wordTrace_append hprefix tailTrace_521797
  have hstable : (prefixWord ++ tailWord_521797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521797).length < 2 ^ (prefixWord ++ tailWord_521797).sum := by decide
  have hdescent : baseEnd_521797 < baseStart_521797 := by decide
  rcases family_descends (prefixWord ++ tailWord_521797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521798 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_521798 : Nat := 118140960795 + 521798 * 2 ^ 59
def prefixEnd_521798 : Nat := 4983230072969 + 3 ^ 40 * 521798 * 2
def baseEnd_521798 : Nat := 267933178554854696625301

theorem tailTrace_521798 : CollatzResearch.WordTrace tailWord_521798 prefixEnd_521798 267933178554854696625301 := by
  unfold tailWord_521798
  simp only [CollatzResearch.WordTrace]
  refine ⟨594735517613201151519439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12687691042414957899081365 594735517613201151519439)
  ·
    refine ⟨892103276419801727279159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 594735517613201151519439 892103276419801727279159)
    ·
      refine ⟨1338154914629702590918739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 892103276419801727279159 1338154914629702590918739)
      ·
        refine ⟨2007232371944553886378109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1338154914629702590918739 2007232371944553886378109)
        ·
          refine ⟨752712139479207707391791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2007232371944553886378109 752712139479207707391791)
          ·
            refine ⟨1129068209218811561087687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752712139479207707391791 1129068209218811561087687)
            ·
              refine ⟨1693602313828217341631531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129068209218811561087687 1693602313828217341631531)
              ·
                refine ⟨2540403470742326012447297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1693602313828217341631531 2540403470742326012447297)
                ·
                  refine ⟨1905302603056744509335473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2540403470742326012447297 1905302603056744509335473)
                  ·
                    refine ⟨1428976952292558382001605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1905302603056744509335473 1428976952292558382001605)
                    ·
                      refine ⟨267933178554854696625301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1428976952292558382001605 267933178554854696625301)
                      ·
                        rfl

theorem cell23_521798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_521798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521798 prefixEnd_521798 := by exact prefixLift 521798
  have htrace : WordTrace (prefixWord ++ tailWord_521798) baseStart_521798 baseEnd_521798 := by
    simpa [prefixWord, tailWord_521798, baseEnd_521798] using wordTrace_append hprefix tailTrace_521798
  have hstable : (prefixWord ++ tailWord_521798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521798).length < 2 ^ (prefixWord ++ tailWord_521798).sum := by decide
  have hdescent : baseEnd_521798 < baseStart_521798 := by decide
  rcases family_descends (prefixWord ++ tailWord_521798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521807 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 4]
def baseStart_521807 : Nat := 118140960795 + 521807 * 2 ^ 59
def prefixEnd_521807 : Nat := 4983230072969 + 3 ^ 40 * 521807 * 2
def baseEnd_521807 : Nat := 267937799880745161412759

theorem tailTrace_521807 : CollatzResearch.WordTrace tailWord_521807 prefixEnd_521807 267937799880745161412759 := by
  unfold tailWord_521807
  simp only [CollatzResearch.WordTrace]
  refine ⟨19031864820589831385699675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12687909880393220923799783 19031864820589831385699675)
  ·
    refine ⟨28547797230884747078549513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19031864820589831385699675 28547797230884747078549513)
    ·
      refine ⟨21410847923163560308912135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28547797230884747078549513 21410847923163560308912135)
      ·
        refine ⟨32116271884745340463368203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21410847923163560308912135 32116271884745340463368203)
        ·
          refine ⟨48174407827118010695052305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32116271884745340463368203 48174407827118010695052305)
          ·
            refine ⟨36130805870338508021289229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48174407827118010695052305 36130805870338508021289229)
            ·
              refine ⟨13549052201376940507983461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36130805870338508021289229 13549052201376940507983461)
              ·
                refine ⟨2540447287758176345246899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13549052201376940507983461 2540447287758176345246899)
                ·
                  refine ⟨3810670931637264517870349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2540447287758176345246899 3810670931637264517870349)
                  ·
                    refine ⟨1429001599363974194201381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3810670931637264517870349 1429001599363974194201381)
                    ·
                      refine ⟨267937799880745161412759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1429001599363974194201381 267937799880745161412759)
                      ·
                        rfl

theorem cell23_521807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_521807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521807 prefixEnd_521807 := by exact prefixLift 521807
  have htrace : WordTrace (prefixWord ++ tailWord_521807) baseStart_521807 baseEnd_521807 := by
    simpa [prefixWord, tailWord_521807, baseEnd_521807] using wordTrace_append hprefix tailTrace_521807
  have hstable : (prefixWord ++ tailWord_521807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521807).length < 2 ^ (prefixWord ++ tailWord_521807).sum := by decide
  have hdescent : baseEnd_521807 < baseStart_521807 := by decide
  rcases family_descends (prefixWord ++ tailWord_521807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521824 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 3, 6, 2]
def baseStart_521824 : Nat := 118140960795 + 521824 * 2 ^ 59
def prefixEnd_521824 : Nat := 4983230072969 + 3 ^ 40 * 521824 * 2
def baseEnd_521824 : Nat := 267946529051871594900181

theorem tailTrace_521824 : CollatzResearch.WordTrace tailWord_521824 prefixEnd_521824 267946529051871594900181 := by
  unfold tailWord_521824
  simp only [CollatzResearch.WordTrace]
  refine ⟨9516242430764121644534263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12688323241018828859379017 9516242430764121644534263)
  ·
    refine ⟨14274363646146182466801395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9516242430764121644534263 14274363646146182466801395)
    ·
      refine ⟨21411545469219273700202093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14274363646146182466801395 21411545469219273700202093)
      ·
        refine ⟨8029329550957227637575785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21411545469219273700202093 8029329550957227637575785)
        ·
          refine ⟨6021997163217920728181839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8029329550957227637575785 6021997163217920728181839)
          ·
            refine ⟨9032995744826881092272759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6021997163217920728181839 9032995744826881092272759)
            ·
              refine ⟨13549493617240321638409139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9032995744826881092272759 13549493617240321638409139)
              ·
                refine ⟨20324240425860482457613709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13549493617240321638409139 20324240425860482457613709)
                ·
                  refine ⟨7621590159697680921605141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20324240425860482457613709 7621590159697680921605141)
                  ·
                    refine ⟨357262038735828793200241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7621590159697680921605141 357262038735828793200241)
                    ·
                      refine ⟨267946529051871594900181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 357262038735828793200241 267946529051871594900181)
                      ·
                        rfl

theorem cell23_521824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_521824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521824 prefixEnd_521824 := by exact prefixLift 521824
  have htrace : WordTrace (prefixWord ++ tailWord_521824) baseStart_521824 baseEnd_521824 := by
    simpa [prefixWord, tailWord_521824, baseEnd_521824] using wordTrace_append hprefix tailTrace_521824
  have hstable : (prefixWord ++ tailWord_521824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521824).length < 2 ^ (prefixWord ++ tailWord_521824).sum := by decide
  have hdescent : baseEnd_521824 < baseStart_521824 := by decide
  rcases family_descends (prefixWord ++ tailWord_521824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521851 : List Nat := [1, 1, 1, 1, 1, 4, 3, 6, 1, 4]
def baseStart_521851 : Nat := 118140960795 + 521851 * 2 ^ 59
def prefixEnd_521851 : Nat := 4983230072969 + 3 ^ 40 * 521851 * 2
def baseEnd_521851 : Nat := 89320131009847663087519

theorem tailTrace_521851 : CollatzResearch.WordTrace tailWord_521851 prefixEnd_521851 89320131009847663087519 := by
  unfold tailWord_521851
  simp only [CollatzResearch.WordTrace]
  refine ⟨19033469632430426900301407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12688979754953617933534271 19033469632430426900301407)
  ·
    refine ⟨28550204448645640350452111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19033469632430426900301407 28550204448645640350452111)
    ·
      refine ⟨42825306672968460525678167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28550204448645640350452111 42825306672968460525678167)
      ·
        refine ⟨64237960009452690788517251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42825306672968460525678167 64237960009452690788517251)
        ·
          refine ⟨96356940014179036182775877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64237960009452690788517251 96356940014179036182775877)
          ·
            refine ⟨18066926252658569284270477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96356940014179036182775877 18066926252658569284270477)
            ·
              refine ⟨6775097344746963481601429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18066926252658569284270477 6775097344746963481601429)
              ·
                refine ⟨317582688035013913200067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6775097344746963481601429 317582688035013913200067)
                ·
                  refine ⟨476374032052520869800101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317582688035013913200067 476374032052520869800101)
                  ·
                    refine ⟨89320131009847663087519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 476374032052520869800101 89320131009847663087519)
                    ·
                      rfl

theorem cell23_521851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 1, 4].length) (baseStart_521851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521851 prefixEnd_521851 := by exact prefixLift 521851
  have htrace : WordTrace (prefixWord ++ tailWord_521851) baseStart_521851 baseEnd_521851 := by
    simpa [prefixWord, tailWord_521851, baseEnd_521851] using wordTrace_append hprefix tailTrace_521851
  have hstable : (prefixWord ++ tailWord_521851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521851).length < 2 ^ (prefixWord ++ tailWord_521851).sum := by decide
  have hdescent : baseEnd_521851 < baseStart_521851 := by decide
  rcases family_descends (prefixWord ++ tailWord_521851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521867 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 6]
def baseStart_521867 : Nat := 118140960795 + 521867 * 2 ^ 59
def prefixEnd_521867 : Nat := 4983230072969 + 3 ^ 40 * 521867 * 2
def baseEnd_521867 : Nat := 267968608720014926662483

theorem tailTrace_521867 : CollatzResearch.WordTrace tailWord_521867 prefixEnd_521867 267968608720014926662483 := by
  unfold tailWord_521867
  simp only [CollatzResearch.WordTrace]
  refine ⟨19034053200372461632883855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12689368800248307755255903 19034053200372461632883855)
  ·
    refine ⟨28551079800558692449325783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19034053200372461632883855 28551079800558692449325783)
    ·
      refine ⟨42826619700838038673988675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28551079800558692449325783 42826619700838038673988675)
      ·
        refine ⟨64239929551257058010983013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42826619700838038673988675 64239929551257058010983013)
        ·
          refine ⟨12044986790860698377059315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64239929551257058010983013 12044986790860698377059315)
          ·
            refine ⟨18067480186291047565588973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12044986790860698377059315 18067480186291047565588973)
            ·
              refine ⟨6775305069859142837095865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18067480186291047565588973 6775305069859142837095865)
              ·
                refine ⟨5081478802394357127821899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6775305069859142837095865 5081478802394357127821899)
                ·
                  refine ⟨7622218203591535691732849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5081478802394357127821899 7622218203591535691732849)
                  ·
                    refine ⟨5716663652693651768799637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7622218203591535691732849 5716663652693651768799637)
                    ·
                      refine ⟨267968608720014926662483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5716663652693651768799637 267968608720014926662483)
                      ·
                        rfl

theorem cell23_521867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 6].length) (baseStart_521867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521867 prefixEnd_521867 := by exact prefixLift 521867
  have htrace : WordTrace (prefixWord ++ tailWord_521867) baseStart_521867 baseEnd_521867 := by
    simpa [prefixWord, tailWord_521867, baseEnd_521867] using wordTrace_append hprefix tailTrace_521867
  have hstable : (prefixWord ++ tailWord_521867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521867).length < 2 ^ (prefixWord ++ tailWord_521867).sum := by decide
  have hdescent : baseEnd_521867 < baseStart_521867 := by decide
  rcases family_descends (prefixWord ++ tailWord_521867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521877 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 2, 9]
def baseStart_521877 : Nat := 118140960795 + 521877 * 2 ^ 59
def prefixEnd_521877 : Nat := 4983230072969 + 3 ^ 40 * 521877 * 2
def baseEnd_521877 : Nat := 89324581175519962512479

theorem tailTrace_521877 : CollatzResearch.WordTrace tailWord_521877 prefixEnd_521877 89324581175519962512479 := by
  unfold tailWord_521877
  simp only [CollatzResearch.WordTrace]
  refine ⟨19034417930336233340747885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12689611953557488893831923 19034417930336233340747885)
  ·
    refine ⟨7137906723876087502780457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19034417930336233340747885 7137906723876087502780457)
    ·
      refine ⟨5353430042907065627085343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7137906723876087502780457 5353430042907065627085343)
      ·
        refine ⟨8030145064360598440628015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5353430042907065627085343 8030145064360598440628015)
        ·
          refine ⟨12045217596540897660942023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8030145064360598440628015 12045217596540897660942023)
          ·
            refine ⟨18067826394811346491413035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12045217596540897660942023 18067826394811346491413035)
            ·
              refine ⟨27101739592217019737119553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18067826394811346491413035 27101739592217019737119553)
              ·
                refine ⟨20326304694162764802839665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27101739592217019737119553 20326304694162764802839665)
                ·
                  refine ⟨15244728520622073602129749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20326304694162764802839665 15244728520622073602129749)
                  ·
                    refine ⟨89324581175519962512479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 15244728520622073602129749 89324581175519962512479)
                    ·
                      rfl

theorem cell23_521877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_521877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521877 prefixEnd_521877 := by exact prefixLift 521877
  have htrace : WordTrace (prefixWord ++ tailWord_521877) baseStart_521877 baseEnd_521877 := by
    simpa [prefixWord, tailWord_521877, baseEnd_521877] using wordTrace_append hprefix tailTrace_521877
  have hstable : (prefixWord ++ tailWord_521877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521877).length < 2 ^ (prefixWord ++ tailWord_521877).sum := by decide
  have hdescent : baseEnd_521877 < baseStart_521877 := by decide
  rcases family_descends (prefixWord ++ tailWord_521877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521902 : List Nat := [4, 1, 4, 1, 3, 1, 1, 1, 3, 4]
def baseStart_521902 : Nat := 118140960795 + 521902 * 2 ^ 59
def prefixEnd_521902 : Nat := 4983230072969 + 3 ^ 40 * 521902 * 2
def baseEnd_521902 : Nat := 89328860180974096574941

theorem tailTrace_521902 : CollatzResearch.WordTrace tailWord_521902 prefixEnd_521902 89328860180974096574941 := by
  unfold tailWord_521902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2379416219405707826300995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12690219836830441740271973 2379416219405707826300995)
  ·
    refine ⟨3569124329108561739451493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2379416219405707826300995 3569124329108561739451493)
    ·
      refine ⟨669210811707855326147155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3569124329108561739451493 669210811707855326147155)
      ·
        refine ⟨1003816217561782989220733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669210811707855326147155 1003816217561782989220733)
        ·
          refine ⟨376431081585668620957775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1003816217561782989220733 376431081585668620957775)
          ·
            refine ⟨564646622378502931436663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376431081585668620957775 564646622378502931436663)
            ·
              refine ⟨846969933567754397154995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564646622378502931436663 846969933567754397154995)
              ·
                refine ⟨1270454900351631595732493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846969933567754397154995 1270454900351631595732493)
                ·
                  refine ⟨476420587631861848399685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1270454900351631595732493 476420587631861848399685)
                  ·
                    refine ⟨89328860180974096574941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 476420587631861848399685 89328860180974096574941)
                    ·
                      rfl

theorem cell23_521902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_521902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521902 prefixEnd_521902 := by exact prefixLift 521902
  have htrace : WordTrace (prefixWord ++ tailWord_521902) baseStart_521902 baseEnd_521902 := by
    simpa [prefixWord, tailWord_521902, baseEnd_521902] using wordTrace_append hprefix tailTrace_521902
  have hstable : (prefixWord ++ tailWord_521902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521902).length < 2 ^ (prefixWord ++ tailWord_521902).sum := by decide
  have hdescent : baseEnd_521902 < baseStart_521902 := by decide
  rcases family_descends (prefixWord ++ tailWord_521902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521982 : List Nat := [4, 2, 2, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_521982 : Nat := 118140960795 + 521982 * 2 ^ 59
def prefixEnd_521982 : Nat := 4983230072969 + 3 ^ 40 * 521982 * 2
def baseEnd_521982 : Nat := 268027658995281976724455

theorem tailTrace_521982 : CollatzResearch.WordTrace tailWord_521982 prefixEnd_521982 268027658995281976724455 := by
  unfold tailWord_521982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2379780949369479534165025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12692165063303890848880133 2379780949369479534165025)
  ·
    refine ⟨1784835712027109650623769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2379780949369479534165025 1784835712027109650623769)
    ·
      refine ⟨1338626784020332237967827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1784835712027109650623769 1338626784020332237967827)
      ·
        refine ⟨2007940176030498356951741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1338626784020332237967827 2007940176030498356951741)
        ·
          refine ⟨752977566011436883856903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2007940176030498356951741 752977566011436883856903)
          ·
            refine ⟨1129466349017155325785355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752977566011436883856903 1129466349017155325785355)
            ·
              refine ⟨1694199523525732988678033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129466349017155325785355 1694199523525732988678033)
              ·
                refine ⟨1270649642644299741508525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1694199523525732988678033 1270649642644299741508525)
                ·
                  refine ⟨476493615991612403065697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1270649642644299741508525 476493615991612403065697)
                  ·
                    refine ⟨357370211993709302299273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 476493615991612403065697 357370211993709302299273)
                    ·
                      refine ⟨268027658995281976724455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 357370211993709302299273 268027658995281976724455)
                      ·
                        rfl

theorem cell23_521982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_521982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_521982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_521982 prefixEnd_521982 := by exact prefixLift 521982
  have htrace : WordTrace (prefixWord ++ tailWord_521982) baseStart_521982 baseEnd_521982 := by
    simpa [prefixWord, tailWord_521982, baseEnd_521982] using wordTrace_append hprefix tailTrace_521982
  have hstable : (prefixWord ++ tailWord_521982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521982).length < 2 ^ (prefixWord ++ tailWord_521982).sum := by decide
  have hdescent : baseEnd_521982 < baseStart_521982 := by decide
  rcases family_descends (prefixWord ++ tailWord_521982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522002 : List Nat := [3, 2, 4, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_522002 : Nat := 118140960795 + 522002 * 2 ^ 59
def prefixEnd_522002 : Nat := 4983230072969 + 3 ^ 40 * 522002 * 2
def baseEnd_522002 : Nat := 268037928608371898474363

theorem tailTrace_522002 : CollatzResearch.WordTrace tailWord_522002 prefixEnd_522002 268037928608371898474363 := by
  unfold tailWord_522002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4759744263720844922262065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12692651369922253126032173 4759744263720844922262065)
  ·
    refine ⟨3569808197790633691696549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4759744263720844922262065 3569808197790633691696549)
    ·
      refine ⟨669339037085743817193103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3569808197790633691696549 669339037085743817193103)
      ·
        refine ⟨1004008555628615725789655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669339037085743817193103 1004008555628615725789655)
        ·
          refine ⟨1506012833442923588684483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004008555628615725789655 1506012833442923588684483)
          ·
            refine ⟨2259019250164385383026725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506012833442923588684483 2259019250164385383026725)
            ·
              refine ⟨423566109405822259317511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2259019250164385383026725 423566109405822259317511)
              ·
                refine ⟨635349164108733388976267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423566109405822259317511 635349164108733388976267)
                ·
                  refine ⟨953023746163100083464401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 635349164108733388976267 953023746163100083464401)
                  ·
                    refine ⟨714767809622325062598301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 953023746163100083464401 714767809622325062598301)
                    ·
                      refine ⟨268037928608371898474363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 714767809622325062598301 268037928608371898474363)
                      ·
                        rfl

theorem cell23_522002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_522002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522002 prefixEnd_522002 := by exact prefixLift 522002
  have htrace : WordTrace (prefixWord ++ tailWord_522002) baseStart_522002 baseEnd_522002 := by
    simpa [prefixWord, tailWord_522002, baseEnd_522002] using wordTrace_append hprefix tailTrace_522002
  have hstable : (prefixWord ++ tailWord_522002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522002).length < 2 ^ (prefixWord ++ tailWord_522002).sum := by decide
  have hdescent : baseEnd_522002 < baseStart_522002 := by decide
  rcases family_descends (prefixWord ++ tailWord_522002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522101 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_522101 : Nat := 118140960795 + 522101 * 2 ^ 59
def prefixEnd_522101 : Nat := 4983230072969 + 3 ^ 40 * 522101 * 2
def baseEnd_522101 : Nat := 268088763193167011136407

theorem tailTrace_522101 : CollatzResearch.WordTrace tailWord_522101 prefixEnd_522101 268088763193167011136407 := by
  unfold tailWord_522101
  simp only [CollatzResearch.WordTrace]
  refine ⟨19042587881524719596902157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12695058587683146397934771 19042587881524719596902157)
  ·
    refine ⟨7140970455571769848838309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19042587881524719596902157 7140970455571769848838309)
    ·
      refine ⟨1338931960419706846657183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7140970455571769848838309 1338931960419706846657183)
      ·
        refine ⟨2008397940629560269985775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1338931960419706846657183 2008397940629560269985775)
        ·
          refine ⟨3012596910944340404978663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2008397940629560269985775 3012596910944340404978663)
          ·
            refine ⟨4518895366416510607467995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3012596910944340404978663 4518895366416510607467995)
            ·
              refine ⟨6778343049624765911201993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4518895366416510607467995 6778343049624765911201993)
              ·
                refine ⟨5083757287218574433401495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6778343049624765911201993 5083757287218574433401495)
                ·
                  refine ⟨7625635930827861650102243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5083757287218574433401495 7625635930827861650102243)
                  ·
                    refine ⟨11438453896241792475153365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7625635930827861650102243 11438453896241792475153365)
                    ·
                      refine ⟨268088763193167011136407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11438453896241792475153365 268088763193167011136407)
                      ·
                        rfl

theorem cell23_522101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_522101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522101 prefixEnd_522101 := by exact prefixLift 522101
  have htrace : WordTrace (prefixWord ++ tailWord_522101) baseStart_522101 baseEnd_522101 := by
    simpa [prefixWord, tailWord_522101, baseEnd_522101] using wordTrace_append hprefix tailTrace_522101
  have hstable : (prefixWord ++ tailWord_522101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522101).length < 2 ^ (prefixWord ++ tailWord_522101).sum := by decide
  have hdescent : baseEnd_522101 < baseStart_522101 := by decide
  rcases family_descends (prefixWord ++ tailWord_522101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522165 : List Nat := [1, 3, 3, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_522165 : Nat := 118140960795 + 522165 * 2 ^ 59
def prefixEnd_522165 : Nat := 4983230072969 + 3 ^ 40 * 522165 * 2
def baseEnd_522165 : Nat := 268121625955054760736113

theorem tailTrace_522165 : CollatzResearch.WordTrace tailWord_522165 prefixEnd_522165 268121625955054760736113 := by
  unfold tailWord_522165
  simp only [CollatzResearch.WordTrace]
  refine ⟨19044922153292858527231949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12696614768861905684821299 19044922153292858527231949)
  ·
    refine ⟨7141845807484821947711981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19044922153292858527231949 7141845807484821947711981)
    ·
      refine ⟨2678192177806808230391993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7141845807484821947711981 2678192177806808230391993)
      ·
        refine ⟨2008644133355106172793995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2678192177806808230391993 2008644133355106172793995)
        ·
          refine ⟨3012966200032659259190993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2008644133355106172793995 3012966200032659259190993)
          ·
            refine ⟨2259724650024494444393245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3012966200032659259190993 2259724650024494444393245)
            ·
              refine ⟨847396743759185416647467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2259724650024494444393245 847396743759185416647467)
              ·
                refine ⟨1271095115638778124971201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847396743759185416647467 1271095115638778124971201)
                ·
                  refine ⟨953321336729083593728401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1271095115638778124971201 953321336729083593728401)
                  ·
                    refine ⟨714991002546812695296301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 953321336729083593728401 714991002546812695296301)
                    ·
                      refine ⟨268121625955054760736113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 714991002546812695296301 268121625955054760736113)
                      ·
                        rfl

theorem cell23_522165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_522165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522165 prefixEnd_522165 := by exact prefixLift 522165
  have htrace : WordTrace (prefixWord ++ tailWord_522165) baseStart_522165 baseEnd_522165 := by
    simpa [prefixWord, tailWord_522165, baseEnd_522165] using wordTrace_append hprefix tailTrace_522165
  have hstable : (prefixWord ++ tailWord_522165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522165).length < 2 ^ (prefixWord ++ tailWord_522165).sum := by decide
  have hdescent : baseEnd_522165 < baseStart_522165 := by decide
  rcases family_descends (prefixWord ++ tailWord_522165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522181 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 5, 5]
def baseStart_522181 : Nat := 118140960795 + 522181 * 2 ^ 59
def prefixEnd_522181 : Nat := 4983230072969 + 3 ^ 40 * 522181 * 2
def baseEnd_522181 : Nat := 89376613881842232712013

theorem tailTrace_522181 : CollatzResearch.WordTrace tailWord_522181 prefixEnd_522181 89376613881842232712013 := by
  unfold tailWord_522181
  simp only [CollatzResearch.WordTrace]
  refine ⟨19045505721234893259814397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12697003814156595506542931 19045505721234893259814397)
  ·
    refine ⟨7142064645463084972430399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19045505721234893259814397 7142064645463084972430399)
    ·
      refine ⟨10713096968194627458645599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7142064645463084972430399 10713096968194627458645599)
      ·
        refine ⟨16069645452291941187968399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10713096968194627458645599 16069645452291941187968399)
        ·
          refine ⟨24104468178437911781952599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16069645452291941187968399 24104468178437911781952599)
          ·
            refine ⟨36156702267656867672928899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24104468178437911781952599 36156702267656867672928899)
            ·
              refine ⟨54235053401485301509393349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36156702267656867672928899 54235053401485301509393349)
              ·
                refine ⟨10169072512778494033011253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54235053401485301509393349 10169072512778494033011253)
                ·
                  refine ⟨953350548072983815594805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10169072512778494033011253 953350548072983815594805)
                  ·
                    refine ⟨89376613881842232712013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 953350548072983815594805 89376613881842232712013)
                    ·
                      rfl

theorem cell23_522181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_522181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522181 prefixEnd_522181 := by exact prefixLift 522181
  have htrace : WordTrace (prefixWord ++ tailWord_522181) baseStart_522181 baseEnd_522181 := by
    simpa [prefixWord, tailWord_522181, baseEnd_522181] using wordTrace_append hprefix tailTrace_522181
  have hstable : (prefixWord ++ tailWord_522181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522181).length < 2 ^ (prefixWord ++ tailWord_522181).sum := by decide
  have hdescent : baseEnd_522181 < baseStart_522181 := by decide
  rcases family_descends (prefixWord ++ tailWord_522181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522235 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 5, 2, 2]
def baseStart_522235 : Nat := 118140960795 + 522235 * 2 ^ 59
def prefixEnd_522235 : Nat := 4983230072969 + 3 ^ 40 * 522235 * 2
def baseEnd_522235 : Nat := 268157569600869486860791

theorem tailTrace_522235 : CollatzResearch.WordTrace tailWord_522235 prefixEnd_522235 268157569600869486860791 := by
  unfold tailWord_522235
  simp only [CollatzResearch.WordTrace]
  refine ⟨19047475263039260482280159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12698316842026173654853439 19047475263039260482280159)
  ·
    refine ⟨28571212894558890723420239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19047475263039260482280159 28571212894558890723420239)
    ·
      refine ⟨42856819341838336085130359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28571212894558890723420239 42856819341838336085130359)
      ·
        refine ⟨64285229012757504127695539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42856819341838336085130359 64285229012757504127695539)
        ·
          refine ⟨96427843519136256191543309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64285229012757504127695539 96427843519136256191543309)
          ·
            refine ⟨36160441319676096071828741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96427843519136256191543309 36160441319676096071828741)
            ·
              refine ⟨6780082747439268013467889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36160441319676096071828741 6780082747439268013467889)
              ·
                refine ⟨5085062060579451010100917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6780082747439268013467889 5085062060579451010100917)
                ·
                  refine ⟨476724568179323532196961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5085062060579451010100917 476724568179323532196961)
                  ·
                    refine ⟨357543426134492649147721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 476724568179323532196961 357543426134492649147721)
                    ·
                      refine ⟨268157569600869486860791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 357543426134492649147721 268157569600869486860791)
                      ·
                        rfl

theorem cell23_522235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 2, 2].length) (baseStart_522235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522235 prefixEnd_522235 := by exact prefixLift 522235
  have htrace : WordTrace (prefixWord ++ tailWord_522235) baseStart_522235 baseEnd_522235 := by
    simpa [prefixWord, tailWord_522235, baseEnd_522235] using wordTrace_append hprefix tailTrace_522235
  have hstable : (prefixWord ++ tailWord_522235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522235).length < 2 ^ (prefixWord ++ tailWord_522235).sum := by decide
  have hdescent : baseEnd_522235 < baseStart_522235 := by decide
  rcases family_descends (prefixWord ++ tailWord_522235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522253 : List Nat := [1, 7, 1, 2, 2, 1, 2, 1, 6]
def baseStart_522253 : Nat := 118140960795 + 522253 * 2 ^ 59
def prefixEnd_522253 : Nat := 4983230072969 + 3 ^ 40 * 522253 * 2
def baseEnd_522253 : Nat := 29796312472516712937301

theorem tailTrace_522253 : CollatzResearch.WordTrace tailWord_522253 prefixEnd_522253 29796312472516712937301 := by
  unfold tailWord_522253
  simp only [CollatzResearch.WordTrace]
  refine ⟨19048131776974049556435413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12698754517982699704290275 19048131776974049556435413)
  ·
    refine ⟨446440588522829286478955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 19048131776974049556435413 446440588522829286478955)
    ·
      refine ⟨669660882784243929718433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446440588522829286478955 669660882784243929718433)
      ·
        refine ⟨502245662088182947288825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 669660882784243929718433 502245662088182947288825)
        ·
          refine ⟨376684246566137210466619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502245662088182947288825 376684246566137210466619)
          ·
            refine ⟨565026369849205815699929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376684246566137210466619 565026369849205815699929)
            ·
              refine ⟨423769777386904361774947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565026369849205815699929 423769777386904361774947)
              ·
                refine ⟨635654666080356542662421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423769777386904361774947 635654666080356542662421)
                ·
                  refine ⟨29796312472516712937301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 635654666080356542662421 29796312472516712937301)
                  ·
                    rfl

theorem cell23_522253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_522253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522253 prefixEnd_522253 := by exact prefixLift 522253
  have htrace : WordTrace (prefixWord ++ tailWord_522253) baseStart_522253 baseEnd_522253 := by
    simpa [prefixWord, tailWord_522253, baseEnd_522253] using wordTrace_append hprefix tailTrace_522253
  have hstable : (prefixWord ++ tailWord_522253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522253).length < 2 ^ (prefixWord ++ tailWord_522253).sum := by decide
  have hdescent : baseEnd_522253 < baseStart_522253 := by decide
  rcases family_descends (prefixWord ++ tailWord_522253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522281 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 7]
def baseStart_522281 : Nat := 118140960795 + 522281 * 2 ^ 59
def prefixEnd_522281 : Nat := 4983230072969 + 3 ^ 40 * 522281 * 2
def baseEnd_522281 : Nat := 268181189710976306885579

theorem tailTrace_522281 : CollatzResearch.WordTrace tailWord_522281 prefixEnd_522281 268181189710976306885579 := by
  unfold tailWord_522281
  simp only [CollatzResearch.WordTrace]
  refine ⟨19049153020872610338454697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12699435347248406892303131 19049153020872610338454697)
  ·
    refine ⟨14286864765654457753841023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19049153020872610338454697 14286864765654457753841023)
    ·
      refine ⟨21430297148481686630761535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14286864765654457753841023 21430297148481686630761535)
      ·
        refine ⟨32145445722722529946142303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21430297148481686630761535 32145445722722529946142303)
        ·
          refine ⟨48218168584083794919213455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32145445722722529946142303 48218168584083794919213455)
          ·
            refine ⟨72327252876125692378820183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48218168584083794919213455 72327252876125692378820183)
            ·
              refine ⟨108490879314188538568230275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72327252876125692378820183 108490879314188538568230275)
              ·
                refine ⟨162736318971282807852345413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108490879314188538568230275 162736318971282807852345413)
                ·
                  refine ⟨30513059807115526472314765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162736318971282807852345413 30513059807115526472314765)
                  ·
                    refine ⟨11442397427668322427118037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30513059807115526472314765 11442397427668322427118037)
                    ·
                      refine ⟨268181189710976306885579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11442397427668322427118037 268181189710976306885579)
                      ·
                        rfl

theorem cell23_522281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_522281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522281 prefixEnd_522281 := by exact prefixLift 522281
  have htrace : WordTrace (prefixWord ++ tailWord_522281) baseStart_522281 baseEnd_522281 := by
    simpa [prefixWord, tailWord_522281, baseEnd_522281] using wordTrace_append hprefix tailTrace_522281
  have hstable : (prefixWord ++ tailWord_522281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522281).length < 2 ^ (prefixWord ++ tailWord_522281).sum := by decide
  have hdescent : baseEnd_522281 < baseStart_522281 := by decide
  rcases family_descends (prefixWord ++ tailWord_522281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522318 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 1, 8]
def baseStart_522318 : Nat := 118140960795 + 522318 * 2 ^ 59
def prefixEnd_522318 : Nat := 4983230072969 + 3 ^ 40 * 522318 * 2
def baseEnd_522318 : Nat := 89400062831730887374303

theorem tailTrace_522318 : CollatzResearch.WordTrace tailWord_522318 prefixEnd_522318 89400062831730887374303 := by
  unfold tailWord_522318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2381312815217320707193951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12700335014492377105034405 2381312815217320707193951)
  ·
    refine ⟨3571969222825981060790927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2381312815217320707193951 3571969222825981060790927)
    ·
      refine ⟨5357953834238971591186391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3571969222825981060790927 5357953834238971591186391)
      ·
        refine ⟨8036930751358457386779587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5357953834238971591186391 8036930751358457386779587)
        ·
          refine ⟨12055396127037686080169381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8036930751358457386779587 12055396127037686080169381)
          ·
            refine ⟨2260386773819566140031759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12055396127037686080169381 2260386773819566140031759)
            ·
              refine ⟨3390580160729349210047639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2260386773819566140031759 3390580160729349210047639)
              ·
                refine ⟨5085870241094023815071459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3390580160729349210047639 5085870241094023815071459)
                ·
                  refine ⟨7628805361641035722607189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5085870241094023815071459 7628805361641035722607189)
                  ·
                    refine ⟨89400062831730887374303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7628805361641035722607189 89400062831730887374303)
                    ·
                      rfl

theorem cell23_522318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_522318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522318 prefixEnd_522318 := by exact prefixLift 522318
  have htrace : WordTrace (prefixWord ++ tailWord_522318) baseStart_522318 baseEnd_522318 := by
    simpa [prefixWord, tailWord_522318, baseEnd_522318] using wordTrace_append hprefix tailTrace_522318
  have hstable : (prefixWord ++ tailWord_522318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522318).length < 2 ^ (prefixWord ++ tailWord_522318).sum := by decide
  have hdescent : baseEnd_522318 < baseStart_522318 := by decide
  rcases family_descends (prefixWord ++ tailWord_522318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522359 : List Nat := [1, 1, 3, 1, 1, 5, 3, 2, 2, 2, 2]
def baseStart_522359 : Nat := 118140960795 + 522359 * 2 ^ 59
def prefixEnd_522359 : Nat := 4983230072969 + 3 ^ 40 * 522359 * 2
def baseEnd_522359 : Nat := 268221241202027001710221

theorem tailTrace_522359 : CollatzResearch.WordTrace tailWord_522359 prefixEnd_522359 268221241202027001710221 := by
  unfold tailWord_522359
  simp only [CollatzResearch.WordTrace]
  refine ⟨19051997914590029659794131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12701331943060019773196087 19051997914590029659794131)
  ·
    refine ⟨28577996871885044489691197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19051997914590029659794131 28577996871885044489691197)
    ·
      refine ⟨10716748826956891683634199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28577996871885044489691197 10716748826956891683634199)
      ·
        refine ⟨16075123240435337525451299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10716748826956891683634199 16075123240435337525451299)
        ·
          refine ⟨24112684860653006288176949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16075123240435337525451299 24112684860653006288176949)
          ·
            refine ⟨2260564205686219339516589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24112684860653006288176949 2260564205686219339516589)
            ·
              refine ⟨847711577132332252318721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2260564205686219339516589 847711577132332252318721)
              ·
                refine ⟨635783682849249189239041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847711577132332252318721 635783682849249189239041)
                ·
                  refine ⟨476837762136936891929281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 635783682849249189239041 476837762136936891929281)
                  ·
                    refine ⟨357628321602702668946961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 476837762136936891929281 357628321602702668946961)
                    ·
                      refine ⟨268221241202027001710221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 357628321602702668946961 268221241202027001710221)
                      ·
                        rfl

theorem cell23_522359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 2, 2].length) (baseStart_522359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522359 prefixEnd_522359 := by exact prefixLift 522359
  have htrace : WordTrace (prefixWord ++ tailWord_522359) baseStart_522359 baseEnd_522359 := by
    simpa [prefixWord, tailWord_522359, baseEnd_522359] using wordTrace_append hprefix tailTrace_522359
  have hstable : (prefixWord ++ tailWord_522359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522359).length < 2 ^ (prefixWord ++ tailWord_522359).sum := by decide
  have hdescent : baseEnd_522359 < baseStart_522359 := by decide
  rcases family_descends (prefixWord ++ tailWord_522359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522365 : List Nat := [1, 4, 1, 1, 3, 3, 2, 1, 7]
def baseStart_522365 : Nat := 118140960795 + 522365 * 2 ^ 59
def prefixEnd_522365 : Nat := 4983230072969 + 3 ^ 40 * 522365 * 2
def baseEnd_522365 : Nat := 29802702453994886470577

theorem tailTrace_522365 : CollatzResearch.WordTrace tailWord_522365 prefixEnd_522365 29802702453994886470577 := by
  unfold tailWord_522365
  simp only [CollatzResearch.WordTrace]
  refine ⟨19052216752568292684512549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12701477835045528456341699 19052216752568292684512549)
  ·
    refine ⟨3572290641106554878346103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19052216752568292684512549 3572290641106554878346103)
    ·
      refine ⟨5358435961659832317519155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3572290641106554878346103 5358435961659832317519155)
      ·
        refine ⟨8037653942489748476278733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5358435961659832317519155 8037653942489748476278733)
        ·
          refine ⟨3014120228433655678604525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8037653942489748476278733 3014120228433655678604525)
          ·
            refine ⟨1130295085662620879476697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3014120228433655678604525 1130295085662620879476697)
            ·
              refine ⟨847721314246965659607523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1130295085662620879476697 847721314246965659607523)
              ·
                refine ⟨1271581971370448489411285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847721314246965659607523 1271581971370448489411285)
                ·
                  refine ⟨29802702453994886470577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1271581971370448489411285 29802702453994886470577)
                  ·
                    rfl

theorem cell23_522365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_522365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522365 prefixEnd_522365 := by exact prefixLift 522365
  have htrace : WordTrace (prefixWord ++ tailWord_522365) baseStart_522365 baseEnd_522365 := by
    simpa [prefixWord, tailWord_522365, baseEnd_522365] using wordTrace_append hprefix tailTrace_522365
  have hstable : (prefixWord ++ tailWord_522365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522365).length < 2 ^ (prefixWord ++ tailWord_522365).sum := by decide
  have hdescent : baseEnd_522365 < baseStart_522365 := by decide
  rcases family_descends (prefixWord ++ tailWord_522365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522375 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 3]
def baseStart_522375 : Nat := 118140960795 + 522375 * 2 ^ 59
def prefixEnd_522375 : Nat := 4983230072969 + 3 ^ 40 * 522375 * 2
def baseEnd_522375 : Nat := 268229456892498939110147

theorem tailTrace_522375 : CollatzResearch.WordTrace tailWord_522375 prefixEnd_522375 268229456892498939110147 := by
  unfold tailWord_522375
  simp only [CollatzResearch.WordTrace]
  refine ⟨19052581482532064392376579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12701720988354709594917719 19052581482532064392376579)
  ·
    refine ⟨28578872223798096588564869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19052581482532064392376579 28578872223798096588564869)
    ·
      refine ⟨5358538541962143110355913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28578872223798096588564869 5358538541962143110355913)
      ·
        refine ⟨4018903906471607332766935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5358538541962143110355913 4018903906471607332766935)
        ·
          refine ⟨6028355859707410999150403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4018903906471607332766935 6028355859707410999150403)
          ·
            refine ⟨9042533789561116498725605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6028355859707410999150403 9042533789561116498725605)
            ·
              refine ⟨1695475085542709343511051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9042533789561116498725605 1695475085542709343511051)
              ·
                refine ⟨2543212628314064015266577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695475085542709343511051 2543212628314064015266577)
                ·
                  refine ⟨1907409471235548011449933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2543212628314064015266577 1907409471235548011449933)
                  ·
                    refine ⟨715278551713330504293725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1907409471235548011449933 715278551713330504293725)
                    ·
                      refine ⟨268229456892498939110147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 715278551713330504293725 268229456892498939110147)
                      ·
                        rfl

theorem cell23_522375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_522375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522375 prefixEnd_522375 := by exact prefixLift 522375
  have htrace : WordTrace (prefixWord ++ tailWord_522375) baseStart_522375 baseEnd_522375 := by
    simpa [prefixWord, tailWord_522375, baseEnd_522375] using wordTrace_append hprefix tailTrace_522375
  have hstable : (prefixWord ++ tailWord_522375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522375).length < 2 ^ (prefixWord ++ tailWord_522375).sum := by decide
  have hdescent : baseEnd_522375 < baseStart_522375 := by decide
  rcases family_descends (prefixWord ++ tailWord_522375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522399 : List Nat := [1, 1, 2, 6, 1, 3, 1, 3, 5]
def baseStart_522399 : Nat := 118140960795 + 522399 * 2 ^ 59
def prefixEnd_522399 : Nat := 4983230072969 + 3 ^ 40 * 522399 * 2
def baseEnd_522399 : Nat := 29804642269800760578893

theorem tailTrace_522399 : CollatzResearch.WordTrace tailWord_522399 prefixEnd_522399 29804642269800760578893 := by
  unfold tailWord_522399
  simp only [CollatzResearch.WordTrace]
  refine ⟨19053456834445116491250251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12702304556296744327500167 19053456834445116491250251)
  ·
    refine ⟨28580185251667674736875377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19053456834445116491250251 28580185251667674736875377)
    ·
      refine ⟨21435138938750756052656533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28580185251667674736875377 21435138938750756052656533)
      ·
        refine ⟨1004772137753941689968275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21435138938750756052656533 1004772137753941689968275)
        ·
          refine ⟨1507158206630912534952413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004772137753941689968275 1507158206630912534952413)
          ·
            refine ⟨565184327486592200607155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1507158206630912534952413 565184327486592200607155)
            ·
              refine ⟨847776491229888300910733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565184327486592200607155 847776491229888300910733)
              ·
                refine ⟨317916184211208112841525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 847776491229888300910733 317916184211208112841525)
                ·
                  refine ⟨29804642269800760578893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 317916184211208112841525 29804642269800760578893)
                  ·
                    rfl

theorem cell23_522399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 5].length) (baseStart_522399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522399 prefixEnd_522399 := by exact prefixLift 522399
  have htrace : WordTrace (prefixWord ++ tailWord_522399) baseStart_522399 baseEnd_522399 := by
    simpa [prefixWord, tailWord_522399, baseEnd_522399] using wordTrace_append hprefix tailTrace_522399
  have hstable : (prefixWord ++ tailWord_522399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522399).length < 2 ^ (prefixWord ++ tailWord_522399).sum := by decide
  have hdescent : baseEnd_522399 < baseStart_522399 := by decide
  rcases family_descends (prefixWord ++ tailWord_522399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522472 : List Nat := [2, 1, 4, 1, 2, 3, 2, 2, 6]
def baseStart_522472 : Nat := 118140960795 + 522472 * 2 ^ 59
def prefixEnd_522472 : Nat := 4983230072969 + 3 ^ 40 * 522472 * 2
def baseEnd_522472 : Nat := 29808807168442784399689

theorem tailTrace_522472 : CollatzResearch.WordTrace tailWord_522472 prefixEnd_522472 29808807168442784399689 := by
  unfold tailWord_522472
  simp only [CollatzResearch.WordTrace]
  refine ⟨9528059681590324979328835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12704079575453766639105113 9528059681590324979328835)
  ·
    refine ⟨14292089522385487468993253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9528059681590324979328835 14292089522385487468993253)
    ·
      refine ⟨2679766785447278900436235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14292089522385487468993253 2679766785447278900436235)
      ·
        refine ⟨4019650178170918350654353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2679766785447278900436235 4019650178170918350654353)
        ·
          refine ⟨3014737633628188762990765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4019650178170918350654353 3014737633628188762990765)
          ·
            refine ⟨1130526612610570786121537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3014737633628188762990765 1130526612610570786121537)
            ·
              refine ⟨847894959457928089591153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1130526612610570786121537 847894959457928089591153)
              ·
                refine ⟨635921219593446067193365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847894959457928089591153 635921219593446067193365)
                ·
                  refine ⟨29808807168442784399689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 635921219593446067193365 29808807168442784399689)
                  ·
                    rfl

theorem cell23_522472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 6].length) (baseStart_522472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522472 prefixEnd_522472 := by exact prefixLift 522472
  have htrace : WordTrace (prefixWord ++ tailWord_522472) baseStart_522472 baseEnd_522472 := by
    simpa [prefixWord, tailWord_522472, baseEnd_522472] using wordTrace_append hprefix tailTrace_522472
  have hstable : (prefixWord ++ tailWord_522472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522472).length < 2 ^ (prefixWord ++ tailWord_522472).sum := by decide
  have hdescent : baseEnd_522472 < baseStart_522472 := by decide
  rcases family_descends (prefixWord ++ tailWord_522472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522503 : List Nat := [1, 1, 4, 5, 2, 1, 1, 1, 2, 2, 3]
def baseStart_522503 : Nat := 118140960795 + 522503 * 2 ^ 59
def prefixEnd_522503 : Nat := 4983230072969 + 3 ^ 40 * 522503 * 2
def baseEnd_522503 : Nat := 268295182416274438309559

theorem tailTrace_522503 : CollatzResearch.WordTrace tailWord_522503 prefixEnd_522503 268295182416274438309559 := by
  unfold tailWord_522503
  simp only [CollatzResearch.WordTrace]
  refine ⟨19057250026068342253036163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12704833350712228168690775 19057250026068342253036163)
  ·
    refine ⟨28585875039102513379554245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19057250026068342253036163 28585875039102513379554245)
    ·
      refine ⟨5359851569831721258666421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28585875039102513379554245 5359851569831721258666421)
      ·
        refine ⟨502486084671723867999977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5359851569831721258666421 502486084671723867999977)
        ·
          refine ⟨376864563503792900999983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502486084671723867999977 376864563503792900999983)
          ·
            refine ⟨565296845255689351499975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376864563503792900999983 565296845255689351499975)
            ·
              refine ⟨847945267883534027249963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565296845255689351499975 847945267883534027249963)
              ·
                refine ⟨1271917901825301040874945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847945267883534027249963 1271917901825301040874945)
                ·
                  refine ⟨953938426368975780656209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1271917901825301040874945 953938426368975780656209)
                  ·
                    refine ⟨715453819776731835492157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 953938426368975780656209 715453819776731835492157)
                    ·
                      refine ⟨268295182416274438309559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 715453819776731835492157 268295182416274438309559)
                      ·
                        rfl

theorem cell23_522503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_522503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522503 prefixEnd_522503 := by exact prefixLift 522503
  have htrace : WordTrace (prefixWord ++ tailWord_522503) baseStart_522503 baseEnd_522503 := by
    simpa [prefixWord, tailWord_522503, baseEnd_522503] using wordTrace_append hprefix tailTrace_522503
  have hstable : (prefixWord ++ tailWord_522503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522503).length < 2 ^ (prefixWord ++ tailWord_522503).sum := by decide
  have hdescent : baseEnd_522503 < baseStart_522503 := by decide
  rcases family_descends (prefixWord ++ tailWord_522503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522519 : List Nat := [1, 1, 3, 4, 1, 2, 4, 1, 1, 5]
def baseStart_522519 : Nat := 118140960795 + 522519 * 2 ^ 59
def prefixEnd_522519 : Nat := 4983230072969 + 3 ^ 40 * 522519 * 2
def baseEnd_522519 : Nat := 89434466035582125236495

theorem tailTrace_522519 : CollatzResearch.WordTrace tailWord_522519 prefixEnd_522519 89434466035582125236495 := by
  unfold tailWord_522519
  simp only [CollatzResearch.WordTrace]
  refine ⟨19057833594010376985618611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12705222396006917990412407 19057833594010376985618611)
  ·
    refine ⟨28586750391015565478427917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19057833594010376985618611 28586750391015565478427917)
    ·
      refine ⟨10720031396630837054410469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28586750391015565478427917 10720031396630837054410469)
      ·
        refine ⟨2010005886868281947701963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10720031396630837054410469 2010005886868281947701963)
        ·
          refine ⟨3015008830302422921552945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2010005886868281947701963 3015008830302422921552945)
          ·
            refine ⟨2261256622726817191164709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3015008830302422921552945 2261256622726817191164709)
            ·
              refine ⟨423985616761278223343383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2261256622726817191164709 423985616761278223343383)
              ·
                refine ⟨635978425141917335015075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423985616761278223343383 635978425141917335015075)
                ·
                  refine ⟨953967637712876002522613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 635978425141917335015075 953967637712876002522613)
                  ·
                    refine ⟨89434466035582125236495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 953967637712876002522613 89434466035582125236495)
                    ·
                      rfl

theorem cell23_522519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 1, 5].length) (baseStart_522519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522519 prefixEnd_522519 := by exact prefixLift 522519
  have htrace : WordTrace (prefixWord ++ tailWord_522519) baseStart_522519 baseEnd_522519 := by
    simpa [prefixWord, tailWord_522519, baseEnd_522519] using wordTrace_append hprefix tailTrace_522519
  have hstable : (prefixWord ++ tailWord_522519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522519).length < 2 ^ (prefixWord ++ tailWord_522519).sum := by decide
  have hdescent : baseEnd_522519 < baseStart_522519 := by decide
  rcases family_descends (prefixWord ++ tailWord_522519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522552 : List Nat := [2, 1, 2, 1, 3, 1, 5, 1, 1, 2, 4]
def baseStart_522552 : Nat := 118140960795 + 522552 * 2 ^ 59
def prefixEnd_522552 : Nat := 4983230072969 + 3 ^ 40 * 522552 * 2
def baseEnd_522552 : Nat := 268320342968344746596833

theorem tailTrace_522552 : CollatzResearch.WordTrace tailWord_522552 prefixEnd_522552 268320342968344746596833 := by
  unfold tailWord_522552
  simp only [CollatzResearch.WordTrace]
  refine ⟨9529518601445411810784955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12706024801927215747713273 9529518601445411810784955)
  ·
    refine ⟨14294277902168117716177433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9529518601445411810784955 14294277902168117716177433)
    ·
      refine ⟨10720708426626088287133075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14294277902168117716177433 10720708426626088287133075)
      ·
        refine ⟨16081062639939132430699613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10720708426626088287133075 16081062639939132430699613)
        ·
          refine ⟨6030398489977174661512355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16081062639939132430699613 6030398489977174661512355)
          ·
            refine ⟨9045597734965761992268533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6030398489977174661512355 9045597734965761992268533)
            ·
              refine ⟨848024787653040186775175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9045597734965761992268533 848024787653040186775175)
              ·
                refine ⟨1272037181479560280162763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848024787653040186775175 1272037181479560280162763)
                ·
                  refine ⟨1908055772219340420244145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1272037181479560280162763 1908055772219340420244145)
                  ·
                    refine ⟨1431041829164505315183109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1908055772219340420244145 1431041829164505315183109)
                    ·
                      refine ⟨268320342968344746596833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1431041829164505315183109 268320342968344746596833)
                      ·
                        rfl

theorem cell23_522552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_522552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522552 prefixEnd_522552 := by exact prefixLift 522552
  have htrace : WordTrace (prefixWord ++ tailWord_522552) baseStart_522552 baseEnd_522552 := by
    simpa [prefixWord, tailWord_522552, baseEnd_522552] using wordTrace_append hprefix tailTrace_522552
  have hstable : (prefixWord ++ tailWord_522552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522552).length < 2 ^ (prefixWord ++ tailWord_522552).sum := by decide
  have hdescent : baseEnd_522552 < baseStart_522552 := by decide
  rcases family_descends (prefixWord ++ tailWord_522552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522559 : List Nat := [1, 1, 2, 2, 4, 1, 4, 2, 1, 2, 3]
def baseStart_522559 : Nat := 118140960795 + 522559 * 2 ^ 59
def prefixEnd_522559 : Nat := 4983230072969 + 3 ^ 40 * 522559 * 2
def baseEnd_522559 : Nat := 268323937332926219209301

theorem tailTrace_522559 : CollatzResearch.WordTrace tailWord_522559 prefixEnd_522559 268323937332926219209301 := by
  unfold tailWord_522559
  simp only [CollatzResearch.WordTrace]
  refine ⟨19059292513865463817074731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12706195009243642544716487 19059292513865463817074731)
  ·
    refine ⟨28588938770798195725612097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19059292513865463817074731 28588938770798195725612097)
    ·
      refine ⟨21441704078098646794209073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28588938770798195725612097 21441704078098646794209073)
      ·
        refine ⟨16081278058573985095656805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21441704078098646794209073 16081278058573985095656805)
        ·
          refine ⟨3015239635982622205435651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16081278058573985095656805 3015239635982622205435651)
          ·
            refine ⟨4522859453973933308153477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3015239635982622205435651 4522859453973933308153477)
            ·
              refine ⟨848036147620112495278777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4522859453973933308153477 848036147620112495278777)
              ·
                refine ⟨636027110715084371459083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848036147620112495278777 636027110715084371459083)
                ·
                  refine ⟨954040666072626557188625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636027110715084371459083 954040666072626557188625)
                  ·
                    refine ⟨715530499554469917891469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 954040666072626557188625 715530499554469917891469)
                    ·
                      refine ⟨268323937332926219209301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 715530499554469917891469 268323937332926219209301)
                      ·
                        rfl

theorem cell23_522559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 2, 3].length) (baseStart_522559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522559 prefixEnd_522559 := by exact prefixLift 522559
  have htrace : WordTrace (prefixWord ++ tailWord_522559) baseStart_522559 baseEnd_522559 := by
    simpa [prefixWord, tailWord_522559, baseEnd_522559] using wordTrace_append hprefix tailTrace_522559
  have hstable : (prefixWord ++ tailWord_522559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522559).length < 2 ^ (prefixWord ++ tailWord_522559).sum := by decide
  have hdescent : baseEnd_522559 < baseStart_522559 := by decide
  rcases family_descends (prefixWord ++ tailWord_522559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522572 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 3, 3, 3]
def baseStart_522572 : Nat := 118140960795 + 522572 * 2 ^ 59
def prefixEnd_522572 : Nat := 4983230072969 + 3 ^ 40 * 522572 * 2
def baseEnd_522572 : Nat := 268330612581434668346741

theorem tailTrace_522572 : CollatzResearch.WordTrace tailWord_522572 prefixEnd_522572 268330612581434668346741 := by
  unfold tailWord_522572
  simp only [CollatzResearch.WordTrace]
  refine ⟨9529883331409183518648985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12706511108545578024865313 9529883331409183518648985)
  ·
    refine ⟨7147412498556887638986739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9529883331409183518648985 7147412498556887638986739)
    ·
      refine ⟨10721118747835331458480109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7147412498556887638986739 10721118747835331458480109)
      ·
        refine ⟨4020419530438249296930041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10721118747835331458480109 4020419530438249296930041)
        ·
          refine ⟨3015314647828686972697531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4020419530438249296930041 3015314647828686972697531)
          ·
            refine ⟨4522971971743030459046297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3015314647828686972697531 4522971971743030459046297)
            ·
              refine ⟨3392228978807272844284723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4522971971743030459046297 3392228978807272844284723)
              ·
                refine ⟨5088343468210909266427085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3392228978807272844284723 5088343468210909266427085)
                ·
                  refine ⟨1908128800579090974910157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5088343468210909266427085 1908128800579090974910157)
                  ·
                    refine ⟨715548300217159115591309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1908128800579090974910157 715548300217159115591309)
                    ·
                      refine ⟨268330612581434668346741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 715548300217159115591309 268330612581434668346741)
                      ·
                        rfl

theorem cell23_522572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_522572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522572 prefixEnd_522572 := by exact prefixLift 522572
  have htrace : WordTrace (prefixWord ++ tailWord_522572) baseStart_522572 baseEnd_522572 := by
    simpa [prefixWord, tailWord_522572, baseEnd_522572] using wordTrace_append hprefix tailTrace_522572
  have hstable : (prefixWord ++ tailWord_522572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522572).length < 2 ^ (prefixWord ++ tailWord_522572).sum := by decide
  have hdescent : baseEnd_522572 < baseStart_522572 := by decide
  rcases family_descends (prefixWord ++ tailWord_522572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522585 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 4, 2, 5]
def baseStart_522585 : Nat := 118140960795 + 522585 * 2 ^ 59
def prefixEnd_522585 : Nat := 4983230072969 + 3 ^ 40 * 522585 * 2
def baseEnd_522585 : Nat := 268337287829943117484181

theorem tailTrace_522585 : CollatzResearch.WordTrace tailWord_522585 prefixEnd_522585 268337287829943117484181 := by
  unfold tailWord_522585
  simp only [CollatzResearch.WordTrace]
  refine ⟨19060240811771270257521209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12706827207847513505014139 19060240811771270257521209)
  ·
    refine ⟨14295180608828452693140907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19060240811771270257521209 14295180608828452693140907)
    ·
      refine ⟨21442770913242679039711361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14295180608828452693140907 21442770913242679039711361)
      ·
        refine ⟨16082078184932009279783521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21442770913242679039711361 16082078184932009279783521)
        ·
          refine ⟨12061558638699006959837641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16082078184932009279783521 12061558638699006959837641)
          ·
            refine ⟨9046168979024255219878231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12061558638699006959837641 9046168979024255219878231)
            ·
              refine ⟨13569253468536382829817347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9046168979024255219878231 13569253468536382829817347)
              ·
                refine ⟨20353880202804574244726021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13569253468536382829817347 20353880202804574244726021)
                ·
                  refine ⟨3816352538025857670886129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20353880202804574244726021 3816352538025857670886129)
                  ·
                    refine ⟨2862264403519393253164597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3816352538025857670886129 2862264403519393253164597)
                    ·
                      refine ⟨268337287829943117484181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2862264403519393253164597 268337287829943117484181)
                      ·
                        rfl

theorem cell23_522585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_522585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522585 prefixEnd_522585 := by exact prefixLift 522585
  have htrace : WordTrace (prefixWord ++ tailWord_522585) baseStart_522585 baseEnd_522585 := by
    simpa [prefixWord, tailWord_522585, baseEnd_522585] using wordTrace_append hprefix tailTrace_522585
  have hstable : (prefixWord ++ tailWord_522585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522585).length < 2 ^ (prefixWord ++ tailWord_522585).sum := by decide
  have hdescent : baseEnd_522585 < baseStart_522585 := by decide
  rcases family_descends (prefixWord ++ tailWord_522585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522632 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_522632 : Nat := 118140960795 + 522632 * 2 ^ 59
def prefixEnd_522632 : Nat := 4983230072969 + 3 ^ 40 * 522632 * 2
def baseEnd_522632 : Nat := 268361421420704433596465

theorem tailTrace_522632 : CollatzResearch.WordTrace tailWord_522632 prefixEnd_522632 268361421420704433596465 := by
  unfold tailWord_522632
  simp only [CollatzResearch.WordTrace]
  refine ⟨9530977521300498642241075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12707970028400664856321433 9530977521300498642241075)
  ·
    refine ⟨14296466281950747963361613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9530977521300498642241075 14296466281950747963361613)
    ·
      refine ⟨5361174855731530486260605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14296466281950747963361613 5361174855731530486260605)
      ·
        refine ⟨2010440570899323932347727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5361174855731530486260605 2010440570899323932347727)
        ·
          refine ⟨3015660856348985898521591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2010440570899323932347727 3015660856348985898521591)
          ·
            refine ⟨4523491284523478847782387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3015660856348985898521591 4523491284523478847782387)
            ·
              refine ⟨6785236926785218271673581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4523491284523478847782387 6785236926785218271673581)
              ·
                refine ⟨2544463847544456851877593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6785236926785218271673581 2544463847544456851877593)
                ·
                  refine ⟨1908347885658342638908195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2544463847544456851877593 1908347885658342638908195)
                  ·
                    refine ⟨2862521828487513958362293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1908347885658342638908195 2862521828487513958362293)
                    ·
                      refine ⟨268361421420704433596465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2862521828487513958362293 268361421420704433596465)
                      ·
                        rfl

theorem cell23_522632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_522632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522632 prefixEnd_522632 := by exact prefixLift 522632
  have htrace : WordTrace (prefixWord ++ tailWord_522632) baseStart_522632 baseEnd_522632 := by
    simpa [prefixWord, tailWord_522632, baseEnd_522632] using wordTrace_append hprefix tailTrace_522632
  have hstable : (prefixWord ++ tailWord_522632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522632).length < 2 ^ (prefixWord ++ tailWord_522632).sum := by decide
  have hdescent : baseEnd_522632 < baseStart_522632 := by decide
  rcases family_descends (prefixWord ++ tailWord_522632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522633 : List Nat := [1, 2, 1, 1, 6, 2, 3, 1, 1, 3, 2]
def baseStart_522633 : Nat := 118140960795 + 522633 * 2 ^ 59
def prefixEnd_522633 : Nat := 4983230072969 + 3 ^ 40 * 522633 * 2
def baseEnd_522633 : Nat := 268361934901358929683961

theorem tailTrace_522633 : CollatzResearch.WordTrace tailWord_522633 prefixEnd_522633 268361934901358929683961 := by
  unfold tailWord_522633
  simp only [CollatzResearch.WordTrace]
  refine ⟨19061991515597374455268553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12707994343731582970179035 19061991515597374455268553)
  ·
    refine ⟨14296493636698030841451415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19061991515597374455268553 14296493636698030841451415)
    ·
      refine ⟨21444740455047046262177123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14296493636698030841451415 21444740455047046262177123)
      ·
        refine ⟨32167110682570569393265685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21444740455047046262177123 32167110682570569393265685)
        ·
          refine ⟨1507833313245495440309329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32167110682570569393265685 1507833313245495440309329)
          ·
            refine ⟨1130874984934121580231997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1507833313245495440309329 1130874984934121580231997)
            ·
              refine ⟨424078119350295592586999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1130874984934121580231997 424078119350295592586999)
              ·
                refine ⟨636117179025443388880499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424078119350295592586999 636117179025443388880499)
                ·
                  refine ⟨954175768538165083320749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636117179025443388880499 954175768538165083320749)
                  ·
                    refine ⟨357815913201811906245281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 954175768538165083320749 357815913201811906245281)
                    ·
                      refine ⟨268361934901358929683961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 357815913201811906245281 268361934901358929683961)
                      ·
                        rfl

theorem cell23_522633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 1, 3, 2].length) (baseStart_522633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522633 prefixEnd_522633 := by exact prefixLift 522633
  have htrace : WordTrace (prefixWord ++ tailWord_522633) baseStart_522633 baseEnd_522633 := by
    simpa [prefixWord, tailWord_522633, baseEnd_522633] using wordTrace_append hprefix tailTrace_522633
  have hstable : (prefixWord ++ tailWord_522633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522633).length < 2 ^ (prefixWord ++ tailWord_522633).sum := by decide
  have hdescent : baseEnd_522633 < baseStart_522633 := by decide
  rcases family_descends (prefixWord ++ tailWord_522633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522663 : List Nat := [1, 1, 6, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_522663 : Nat := 118140960795 + 522663 * 2 ^ 59
def prefixEnd_522663 : Nat := 4983230072969 + 3 ^ 40 * 522663 * 2
def baseEnd_522663 : Nat := 268377339320993812308823

theorem tailTrace_522663 : CollatzResearch.WordTrace tailWord_522663 prefixEnd_522663 268377339320993812308823 := by
  unfold tailWord_522663
  simp only [CollatzResearch.WordTrace]
  refine ⟨19063085705488689578860643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12708723803659126385907095 19063085705488689578860643)
  ·
    refine ⟨28594628558233034368290965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19063085705488689578860643 28594628558233034368290965)
    ·
      refine ⟨1340373213667173486013639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28594628558233034368290965 1340373213667173486013639)
      ·
        refine ⟨2010559820500760229020459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1340373213667173486013639 2010559820500760229020459)
        ·
          refine ⟨3015839730751140343530689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2010559820500760229020459 3015839730751140343530689)
          ·
            refine ⟨2261879798063355257648017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3015839730751140343530689 2261879798063355257648017)
            ·
              refine ⟨1696409848547516443236013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2261879798063355257648017 1696409848547516443236013)
              ·
                refine ⟨636153693205318666213505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1696409848547516443236013 636153693205318666213505)
                ·
                  refine ⟨477115269903988999660129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636153693205318666213505 477115269903988999660129)
                  ·
                    refine ⟨357836452427991749745097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 477115269903988999660129 357836452427991749745097)
                    ·
                      refine ⟨268377339320993812308823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 357836452427991749745097 268377339320993812308823)
                      ·
                        rfl

theorem cell23_522663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_522663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522663 prefixEnd_522663 := by exact prefixLift 522663
  have htrace : WordTrace (prefixWord ++ tailWord_522663) baseStart_522663 baseEnd_522663 := by
    simpa [prefixWord, tailWord_522663, baseEnd_522663] using wordTrace_append hprefix tailTrace_522663
  have hstable : (prefixWord ++ tailWord_522663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522663).length < 2 ^ (prefixWord ++ tailWord_522663).sum := by decide
  have hdescent : baseEnd_522663 < baseStart_522663 := by decide
  rcases family_descends (prefixWord ++ tailWord_522663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522732 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 4]
def baseStart_522732 : Nat := 118140960795 + 522732 * 2 ^ 59
def prefixEnd_522732 : Nat := 4983230072969 + 3 ^ 40 * 522732 * 2
def baseEnd_522732 : Nat := 268412769486154042346005

theorem tailTrace_522732 : CollatzResearch.WordTrace tailWord_522732 prefixEnd_522732 268412769486154042346005 := by
  unfold tailWord_522732
  simp only [CollatzResearch.WordTrace]
  refine ⟨9532801171119357181561225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12710401561492476242081633 9532801171119357181561225)
  ·
    refine ⟨7149600878339517886170919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9532801171119357181561225 7149600878339517886170919)
    ·
      refine ⟨10724401317509276829256379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7149600878339517886170919 10724401317509276829256379)
      ·
        refine ⟨16086601976263915243884569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10724401317509276829256379 16086601976263915243884569)
        ·
          refine ⟨12064951482197936432913427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16086601976263915243884569 12064951482197936432913427)
          ·
            refine ⟨18097427223296904649370141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12064951482197936432913427 18097427223296904649370141)
            ·
              refine ⟨6786535208736339243513803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18097427223296904649370141 6786535208736339243513803)
              ·
                refine ⟨10179802813104508865270705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6786535208736339243513803 10179802813104508865270705)
                ·
                  refine ⟨7634852109828381648953029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10179802813104508865270705 7634852109828381648953029)
                  ·
                    refine ⟨1431534770592821559178693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7634852109828381648953029 1431534770592821559178693)
                    ·
                      refine ⟨268412769486154042346005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1431534770592821559178693 268412769486154042346005)
                      ·
                        rfl

theorem cell23_522732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_522732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522732 prefixEnd_522732 := by exact prefixLift 522732
  have htrace : WordTrace (prefixWord ++ tailWord_522732) baseStart_522732 baseEnd_522732 := by
    simpa [prefixWord, tailWord_522732, baseEnd_522732] using wordTrace_append hprefix tailTrace_522732
  have hstable : (prefixWord ++ tailWord_522732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522732).length < 2 ^ (prefixWord ++ tailWord_522732).sum := by decide
  have hdescent : baseEnd_522732 < baseStart_522732 := by decide
  rcases family_descends (prefixWord ++ tailWord_522732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522739 : List Nat := [1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 3]
def baseStart_522739 : Nat := 118140960795 + 522739 * 2 ^ 59
def prefixEnd_522739 : Nat := 4983230072969 + 3 ^ 40 * 522739 * 2
def baseEnd_522739 : Nat := 268416363850735514958473

theorem tailTrace_522739 : CollatzResearch.WordTrace tailWord_522739 prefixEnd_522739 268416363850735514958473 := by
  unfold tailWord_522739
  simp only [CollatzResearch.WordTrace]
  refine ⟨19065857653213354558627271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12710571768808903039084847 19065857653213354558627271)
  ·
    refine ⟨28598786479820031837940907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19065857653213354558627271 28598786479820031837940907)
    ·
      refine ⟨42898179719730047756911361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28598786479820031837940907 42898179719730047756911361)
      ·
        refine ⟨32173634789797535817683521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42898179719730047756911361 32173634789797535817683521)
        ·
          refine ⟨24130226092348151863262641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32173634789797535817683521 24130226092348151863262641)
          ·
            refine ⟨18097669569261113897446981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24130226092348151863262641 18097669569261113897446981)
            ·
              refine ⟨3393313044236458855771309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18097669569261113897446981 3393313044236458855771309)
              ·
                refine ⟨1272492391588672070914241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3393313044236458855771309 1272492391588672070914241)
                ·
                  refine ⟨954369293691504053185681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1272492391588672070914241 954369293691504053185681)
                  ·
                    refine ⟨715776970268628039889261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 954369293691504053185681 715776970268628039889261)
                    ·
                      refine ⟨268416363850735514958473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 715776970268628039889261 268416363850735514958473)
                      ·
                        rfl

theorem cell23_522739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 3].length) (baseStart_522739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522739 prefixEnd_522739 := by exact prefixLift 522739
  have htrace : WordTrace (prefixWord ++ tailWord_522739) baseStart_522739 baseEnd_522739 := by
    simpa [prefixWord, tailWord_522739, baseEnd_522739] using wordTrace_append hprefix tailTrace_522739
  have hstable : (prefixWord ++ tailWord_522739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522739).length < 2 ^ (prefixWord ++ tailWord_522739).sum := by decide
  have hdescent : baseEnd_522739 < baseStart_522739 := by decide
  rcases family_descends (prefixWord ++ tailWord_522739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522746 : List Nat := [3, 1, 1, 1, 1, 2, 2, 7, 1, 4]
def baseStart_522746 : Nat := 118140960795 + 522746 * 2 ^ 59
def prefixEnd_522746 : Nat := 4983230072969 + 3 ^ 40 * 522746 * 2
def baseEnd_522746 : Nat := 89473319405105662523647

theorem tailTrace_522746 : CollatzResearch.WordTrace tailWord_522746 prefixEnd_522746 89473319405105662523647 := by
  unfold tailWord_522746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4766528241046998688533023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12710741976125329836088061 4766528241046998688533023)
  ·
    refine ⟨7149792361570498032799535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4766528241046998688533023 7149792361570498032799535)
    ·
      refine ⟨10724688542355747049199303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7149792361570498032799535 10724688542355747049199303)
      ·
        refine ⟨16087032813533620573798955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10724688542355747049199303 16087032813533620573798955)
        ·
          refine ⟨24130549220300430860698433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16087032813533620573798955 24130549220300430860698433)
          ·
            refine ⟨18097911915225323145523825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24130549220300430860698433 18097911915225323145523825)
            ·
              refine ⟨13573433936418992359142869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18097911915225323145523825 13573433936418992359142869)
              ·
                refine ⟨318127357884820133417411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13573433936418992359142869 318127357884820133417411)
                ·
                  refine ⟨477191036827230200126117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318127357884820133417411 477191036827230200126117)
                  ·
                    refine ⟨89473319405105662523647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 477191036827230200126117 89473319405105662523647)
                    ·
                      rfl

theorem cell23_522746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 1, 4].length) (baseStart_522746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522746 prefixEnd_522746 := by exact prefixLift 522746
  have htrace : WordTrace (prefixWord ++ tailWord_522746) baseStart_522746 baseEnd_522746 := by
    simpa [prefixWord, tailWord_522746, baseEnd_522746] using wordTrace_append hprefix tailTrace_522746
  have hstable : (prefixWord ++ tailWord_522746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522746).length < 2 ^ (prefixWord ++ tailWord_522746).sum := by decide
  have hdescent : baseEnd_522746 < baseStart_522746 := by decide
  rcases family_descends (prefixWord ++ tailWord_522746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522756 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_522756 : Nat := 118140960795 + 522756 * 2 ^ 59
def prefixEnd_522756 : Nat := 4983230072969 + 3 ^ 40 * 522756 * 2
def baseEnd_522756 : Nat := 268425093021861948445895

theorem tailTrace_522756 : CollatzResearch.WordTrace tailWord_522756 prefixEnd_522756 268425093021861948445895 := by
  unfold tailWord_522756
  simp only [CollatzResearch.WordTrace]
  refine ⟨9533238847075883230998061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12710985129434510974664081 9533238847075883230998061)
  ·
    refine ⟨3574964567653456211624273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9533238847075883230998061 3574964567653456211624273)
    ·
      refine ⟨2681223425740092158718205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3574964567653456211624273 2681223425740092158718205)
      ·
        refine ⟨1005458784652534559519327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2681223425740092158718205 1005458784652534559519327)
        ·
          refine ⟨1508188176978801839278991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005458784652534559519327 1508188176978801839278991)
          ·
            refine ⟨2262282265468202758918487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1508188176978801839278991 2262282265468202758918487)
            ·
              refine ⟨3393423398202304138377731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2262282265468202758918487 3393423398202304138377731)
              ·
                refine ⟨5090135097303456207566597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3393423398202304138377731 5090135097303456207566597)
                ·
                  refine ⟨954400330744398038918737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5090135097303456207566597 954400330744398038918737)
                  ·
                    refine ⟨715800248058298529189053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 954400330744398038918737 715800248058298529189053)
                    ·
                      refine ⟨268425093021861948445895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 715800248058298529189053 268425093021861948445895)
                      ·
                        rfl

theorem cell23_522756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_522756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522756 prefixEnd_522756 := by exact prefixLift 522756
  have htrace : WordTrace (prefixWord ++ tailWord_522756) baseStart_522756 baseEnd_522756 := by
    simpa [prefixWord, tailWord_522756, baseEnd_522756] using wordTrace_append hprefix tailTrace_522756
  have hstable : (prefixWord ++ tailWord_522756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522756).length < 2 ^ (prefixWord ++ tailWord_522756).sum := by decide
  have hdescent : baseEnd_522756 < baseStart_522756 := by decide
  rcases family_descends (prefixWord ++ tailWord_522756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522776 : List Nat := [2, 1, 2, 3, 3, 1, 4, 1, 6]
def baseStart_522776 : Nat := 118140960795 + 522776 * 2 ^ 59
def prefixEnd_522776 : Nat := 4983230072969 + 3 ^ 40 * 522776 * 2
def baseEnd_522776 : Nat := 29826151403883541132867

theorem tailTrace_522776 : CollatzResearch.WordTrace tailWord_522776 prefixEnd_522776 29826151403883541132867 := by
  unfold tailWord_522776
  simp only [CollatzResearch.WordTrace]
  refine ⟨9533603577039654938862091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12711471436052873251816121 9533603577039654938862091)
  ·
    refine ⟨14300405365559482408293137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9533603577039654938862091 14300405365559482408293137)
    ·
      refine ⟨10725304024169611806219853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14300405365559482408293137 10725304024169611806219853)
      ·
        refine ⟨4021989009063604427332445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10725304024169611806219853 4021989009063604427332445)
        ·
          refine ⟨1508245878398851660249667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4021989009063604427332445 1508245878398851660249667)
          ·
            refine ⟨2262368817598277490374501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1508245878398851660249667 2262368817598277490374501)
            ·
              refine ⟨424194153299677029445219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2262368817598277490374501 424194153299677029445219)
              ·
                refine ⟨636291229949515544167829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424194153299677029445219 636291229949515544167829)
                ·
                  refine ⟨29826151403883541132867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 636291229949515544167829 29826151403883541132867)
                  ·
                    rfl

theorem cell23_522776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 6].length) (baseStart_522776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522776 prefixEnd_522776 := by exact prefixLift 522776
  have htrace : WordTrace (prefixWord ++ tailWord_522776) baseStart_522776 baseEnd_522776 := by
    simpa [prefixWord, tailWord_522776, baseEnd_522776] using wordTrace_append hprefix tailTrace_522776
  have hstable : (prefixWord ++ tailWord_522776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522776).length < 2 ^ (prefixWord ++ tailWord_522776).sum := by decide
  have hdescent : baseEnd_522776 < baseStart_522776 := by decide
  rcases family_descends (prefixWord ++ tailWord_522776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522786 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_522786 : Nat := 118140960795 + 522786 * 2 ^ 59
def prefixEnd_522786 : Nat := 4983230072969 + 3 ^ 40 * 522786 * 2
def baseEnd_522786 : Nat := 268440497441496831070757

theorem tailTrace_522786 : CollatzResearch.WordTrace tailWord_522786 prefixEnd_522786 268440497441496831070757 := by
  unfold tailWord_522786
  simp only [CollatzResearch.WordTrace]
  refine ⟨4766892971010770396397053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12711714589362054390392141 4766892971010770396397053)
  ·
    refine ⟨1787584864129038898648895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4766892971010770396397053 1787584864129038898648895)
    ·
      refine ⟨2681377296193558347973343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1787584864129038898648895 2681377296193558347973343)
      ·
        refine ⟨4022065944290337521960015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2681377296193558347973343 4022065944290337521960015)
        ·
          refine ⟨6033098916435506282940023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4022065944290337521960015 6033098916435506282940023)
          ·
            refine ⟨9049648374653259424410035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6033098916435506282940023 9049648374653259424410035)
            ·
              refine ⟨13574472561979889136615053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9049648374653259424410035 13574472561979889136615053)
              ·
                refine ⟨5090427210742458426230645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13574472561979889136615053 5090427210742458426230645)
                ·
                  refine ⟨477227551007105477459123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5090427210742458426230645 477227551007105477459123)
                  ·
                    refine ⟨715841326510658216188685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 477227551007105477459123 715841326510658216188685)
                    ·
                      refine ⟨268440497441496831070757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 715841326510658216188685 268440497441496831070757)
                      ·
                        rfl

theorem cell23_522786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_522786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522786 prefixEnd_522786 := by exact prefixLift 522786
  have htrace : WordTrace (prefixWord ++ tailWord_522786) baseStart_522786 baseEnd_522786 := by
    simpa [prefixWord, tailWord_522786, baseEnd_522786] using wordTrace_append hprefix tailTrace_522786
  have hstable : (prefixWord ++ tailWord_522786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522786).length < 2 ^ (prefixWord ++ tailWord_522786).sum := by decide
  have hdescent : baseEnd_522786 < baseStart_522786 := by decide
  rcases family_descends (prefixWord ++ tailWord_522786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522803 : List Nat := [1, 1, 1, 2, 4, 2, 2, 5, 1, 1, 3]
def baseStart_522803 : Nat := 118140960795 + 522803 * 2 ^ 59
def prefixEnd_522803 : Nat := 4983230072969 + 3 ^ 40 * 522803 * 2
def baseEnd_522803 : Nat := 268449226612623264558179

theorem tailTrace_522803 : CollatzResearch.WordTrace tailWord_522803 prefixEnd_522803 268449226612623264558179 := by
  unfold tailWord_522803
  simp only [CollatzResearch.WordTrace]
  refine ⟨19068191924981493488957063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12712127949987662325971375 19068191924981493488957063)
  ·
    refine ⟨28602287887472240233435595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19068191924981493488957063 28602287887472240233435595)
    ·
      refine ⟨42903431831208360350153393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28602287887472240233435595 42903431831208360350153393)
      ·
        refine ⟨32177573873406270262615045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42903431831208360350153393 32177573873406270262615045)
        ·
          refine ⟨6033295101263675674240321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32177573873406270262615045 6033295101263675674240321)
          ·
            refine ⟨4524971325947756755680241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6033295101263675674240321 4524971325947756755680241)
            ·
              refine ⟨3393728494460817566760181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4524971325947756755680241 3393728494460817566760181)
              ·
                refine ⟨318162046355701646883767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3393728494460817566760181 318162046355701646883767)
                ·
                  refine ⟨477243069533552470325651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318162046355701646883767 477243069533552470325651)
                  ·
                    refine ⟨715864604300328705488477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 477243069533552470325651 715864604300328705488477)
                    ·
                      refine ⟨268449226612623264558179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 715864604300328705488477 268449226612623264558179)
                      ·
                        rfl

theorem cell23_522803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 1, 1, 3].length) (baseStart_522803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522803 prefixEnd_522803 := by exact prefixLift 522803
  have htrace : WordTrace (prefixWord ++ tailWord_522803) baseStart_522803 baseEnd_522803 := by
    simpa [prefixWord, tailWord_522803, baseEnd_522803] using wordTrace_append hprefix tailTrace_522803
  have hstable : (prefixWord ++ tailWord_522803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522803).length < 2 ^ (prefixWord ++ tailWord_522803).sum := by decide
  have hdescent : baseEnd_522803 < baseStart_522803 := by decide
  rcases family_descends (prefixWord ++ tailWord_522803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522813 : List Nat := [1, 4, 1, 3, 2, 1, 2, 2, 2, 3, 2]
def baseStart_522813 : Nat := 118140960795 + 522813 * 2 ^ 59
def prefixEnd_522813 : Nat := 4983230072969 + 3 ^ 40 * 522813 * 2
def baseEnd_522813 : Nat := 268454361419168225433133

theorem tailTrace_522813 : CollatzResearch.WordTrace tailWord_522813 prefixEnd_522813 268454361419168225433133 := by
  unfold tailWord_522813
  simp only [CollatzResearch.WordTrace]
  refine ⟨19068556654945265196821093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12712371103296843464547395 19068556654945265196821093)
  ·
    refine ⟨3575354372802237224403955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19068556654945265196821093 3575354372802237224403955)
    ·
      refine ⟨5363031559203355836605933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3575354372802237224403955 5363031559203355836605933)
      ·
        refine ⟨2011136834701258438727225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5363031559203355836605933 2011136834701258438727225)
        ·
          refine ⟨1508352626025943829045419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2011136834701258438727225 1508352626025943829045419)
          ·
            refine ⟨2262528939038915743568129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1508352626025943829045419 2262528939038915743568129)
            ·
              refine ⟨1696896704279186807676097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2262528939038915743568129 1696896704279186807676097)
              ·
                refine ⟨1272672528209390105757073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1696896704279186807676097 1272672528209390105757073)
                ·
                  refine ⟨954504396157042579317805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1272672528209390105757073 954504396157042579317805)
                  ·
                    refine ⟨357939148558890967244177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 954504396157042579317805 357939148558890967244177)
                    ·
                      refine ⟨268454361419168225433133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 357939148558890967244177 268454361419168225433133)
                      ·
                        rfl

theorem cell23_522813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_522813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522813 prefixEnd_522813 := by exact prefixLift 522813
  have htrace : WordTrace (prefixWord ++ tailWord_522813) baseStart_522813 baseEnd_522813 := by
    simpa [prefixWord, tailWord_522813, baseEnd_522813] using wordTrace_append hprefix tailTrace_522813
  have hstable : (prefixWord ++ tailWord_522813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522813).length < 2 ^ (prefixWord ++ tailWord_522813).sum := by decide
  have hdescent : baseEnd_522813 < baseStart_522813 := by decide
  rcases family_descends (prefixWord ++ tailWord_522813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522814 : List Nat := [4, 2, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_522814 : Nat := 118140960795 + 522814 * 2 ^ 59
def prefixEnd_522814 : Nat := 4983230072969 + 3 ^ 40 * 522814 * 2
def baseEnd_522814 : Nat := 89484958299940907173543

theorem tailTrace_522814 : CollatzResearch.WordTrace tailWord_522814 prefixEnd_522814 89484958299940907173543 := by
  unfold tailWord_522814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2383574140992705295950937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12712395418627761578404997 2383574140992705295950937)
  ·
    refine ⟨1787680605744528971963203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2383574140992705295950937 1787680605744528971963203)
    ·
      refine ⟨2681520908616793457944805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1787680605744528971963203 2681520908616793457944805)
      ·
        refine ⟨502785170365648773364651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2681520908616793457944805 502785170365648773364651)
        ·
          refine ⟨754177755548473160046977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502785170365648773364651 754177755548473160046977)
          ·
            refine ⟨565633316661354870035233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 754177755548473160046977 565633316661354870035233)
            ·
              refine ⟨424224987496016152526425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565633316661354870035233 424224987496016152526425)
              ·
                refine ⟨318168740622012114394819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424224987496016152526425 318168740622012114394819)
                ·
                  refine ⟨477253110933018171592229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318168740622012114394819 477253110933018171592229)
                  ·
                    refine ⟨89484958299940907173543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 477253110933018171592229 89484958299940907173543)
                    ·
                      rfl

theorem cell23_522814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_522814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_522814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_522814 prefixEnd_522814 := by exact prefixLift 522814
  have htrace : WordTrace (prefixWord ++ tailWord_522814) baseStart_522814 baseEnd_522814 := by
    simpa [prefixWord, tailWord_522814, baseEnd_522814] using wordTrace_append hprefix tailTrace_522814
  have hstable : (prefixWord ++ tailWord_522814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522814).length < 2 ^ (prefixWord ++ tailWord_522814).sum := by decide
  have hdescent : baseEnd_522814 < baseStart_522814 := by decide
  rcases family_descends (prefixWord ++ tailWord_522814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
