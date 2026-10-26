import V185TrunkScan22Chunk415

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3709092 : List Nat := [2, 3, 1, 2, 4, 2, 2, 6]
def baseStart_3709092 : Nat := 118140960795 + 3709092 * 2 ^ 59
def prefixEnd_3709092 : Nat := 4983230072969 + 3 ^ 40 * 3709092 * 2
def baseEnd_3709092 : Nat := 141077554647874621792015

theorem tailTrace_3709092 : CollatzResearch.WordTrace tailWord_3709092 prefixEnd_3709092 141077554647874621792015 := by
  unfold tailWord_3709092
  simp only [CollatzResearch.WordTrace]
  refine ⟨67640849539300310663092765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90187799385733747550790353 67640849539300310663092765)
  ·
    refine ⟨25365318577237616498659787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67640849539300310663092765 25365318577237616498659787)
    ·
      refine ⟨38047977865856424747989681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25365318577237616498659787 38047977865856424747989681)
      ·
        refine ⟨28535983399392318560992261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38047977865856424747989681 28535983399392318560992261)
        ·
          refine ⟨5350496887386059730186049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28535983399392318560992261 5350496887386059730186049)
          ·
            refine ⟨4012872665539544797639537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5350496887386059730186049 4012872665539544797639537)
            ·
              refine ⟨3009654499154658598229653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4012872665539544797639537 3009654499154658598229653)
              ·
                refine ⟨141077554647874621792015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3009654499154658598229653 141077554647874621792015)
                ·
                  rfl

theorem cell22_3709092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 6].length) (baseStart_3709092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709092 prefixEnd_3709092 := by exact prefixLift 3709092
  have htrace : WordTrace (prefixWord ++ tailWord_3709092) baseStart_3709092 baseEnd_3709092 := by
    simpa [prefixWord, tailWord_3709092, baseEnd_3709092] using wordTrace_append hprefix tailTrace_3709092
  have hstable : (prefixWord ++ tailWord_3709092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709092).length < 2 ^ (prefixWord ++ tailWord_3709092).sum := by decide
  have hdescent : baseEnd_3709092 < baseStart_3709092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709124 : List Nat := [2, 3, 3, 1, 2, 3, 1, 1, 3, 3]
def baseStart_3709124 : Nat := 118140960795 + 3709124 * 2 ^ 59
def prefixEnd_3709124 : Nat := 4983230072969 + 3 ^ 40 * 3709124 * 2
def baseEnd_3709124 : Nat := 1269708946084834179328037

theorem tailTrace_3709124 : CollatzResearch.WordTrace tailWord_3709124 prefixEnd_3709124 1269708946084834179328037 := by
  unfold tailWord_3709124
  simp only [CollatzResearch.WordTrace]
  refine ⟨67641433107242345395675213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90188577476323127194233617 67641433107242345395675213)
  ·
    refine ⟨25365537415215879523378205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67641433107242345395675213 25365537415215879523378205)
    ·
      refine ⟨9512076530705954821266827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25365537415215879523378205 9512076530705954821266827)
      ·
        refine ⟨14268114796058932231900241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9512076530705954821266827 14268114796058932231900241)
        ·
          refine ⟨10701086097044199173925181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14268114796058932231900241 10701086097044199173925181)
          ·
            refine ⟨4012907286391574690221943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10701086097044199173925181 4012907286391574690221943)
            ·
              refine ⟨6019360929587362035332915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012907286391574690221943 6019360929587362035332915)
              ·
                refine ⟨9029041394381043052999373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6019360929587362035332915 9029041394381043052999373)
                ·
                  refine ⟨3385890522892891144874765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9029041394381043052999373 3385890522892891144874765)
                  ·
                    refine ⟨1269708946084834179328037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3385890522892891144874765 1269708946084834179328037)
                    ·
                      rfl

theorem cell22_3709124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_3709124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709124 prefixEnd_3709124 := by exact prefixLift 3709124
  have htrace : WordTrace (prefixWord ++ tailWord_3709124) baseStart_3709124 baseEnd_3709124 := by
    simpa [prefixWord, tailWord_3709124, baseEnd_3709124] using wordTrace_append hprefix tailTrace_3709124
  have hstable : (prefixWord ++ tailWord_3709124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709124).length < 2 ^ (prefixWord ++ tailWord_3709124).sum := by decide
  have hdescent : baseEnd_3709124 < baseStart_3709124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709214 : List Nat := [4, 3, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3709214 : Nat := 118140960795 + 3709214 * 2 ^ 59
def prefixEnd_3709214 : Nat := 4983230072969 + 3 ^ 40 * 3709214 * 2
def baseEnd_3709214 : Nat := 1269739754924103944577761

theorem tailTrace_3709214 : CollatzResearch.WordTrace tailWord_3709214 prefixEnd_3709214 1269739754924103944577761 := by
  unfold tailWord_3709214
  simp only [CollatzResearch.WordTrace]
  refine ⟨16910768598019829520265837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90190765856105757441417797 16910768598019829520265837)
  ·
    refine ⟨6341538224257436070099689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16910768598019829520265837 6341538224257436070099689)
    ·
      refine ⟨4756153668193077052574767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6341538224257436070099689 4756153668193077052574767)
      ·
        refine ⟨7134230502289615578862151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4756153668193077052574767 7134230502289615578862151)
        ·
          refine ⟨10701345753434423368293227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7134230502289615578862151 10701345753434423368293227)
          ·
            refine ⟨16052018630151635052439841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10701345753434423368293227 16052018630151635052439841)
            ·
              refine ⟨12039013972613726289329881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16052018630151635052439841 12039013972613726289329881)
              ·
                refine ⟨9029260479460294716997411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12039013972613726289329881 9029260479460294716997411)
                ·
                  refine ⟨13543890719190442075496117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9029260479460294716997411 13543890719190442075496117)
                  ·
                    refine ⟨1269739754924103944577761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13543890719190442075496117 1269739754924103944577761)
                    ·
                      rfl

theorem cell22_3709214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3709214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709214 prefixEnd_3709214 := by exact prefixLift 3709214
  have htrace : WordTrace (prefixWord ++ tailWord_3709214) baseStart_3709214 baseEnd_3709214 := by
    simpa [prefixWord, tailWord_3709214, baseEnd_3709214] using wordTrace_append hprefix tailTrace_3709214
  have hstable : (prefixWord ++ tailWord_3709214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709214).length < 2 ^ (prefixWord ++ tailWord_3709214).sum := by decide
  have hdescent : baseEnd_3709214 < baseStart_3709214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709242 : List Nat := [3, 1, 1, 1, 4, 2, 1, 3, 3, 3]
def baseStart_3709242 : Nat := 118140960795 + 3709242 * 2 ^ 59
def prefixEnd_3709242 : Nat := 4983230072969 + 3 ^ 40 * 3709242 * 2
def baseEnd_3709242 : Nat := 1269749339896321204877675

theorem tailTrace_3709242 : CollatzResearch.WordTrace tailWord_3709242 prefixEnd_3709242 1269749339896321204877675 := by
  unfold tailWord_3709242
  simp only [CollatzResearch.WordTrace]
  refine ⟨33821792507014299236036495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90191446685371464629430653 33821792507014299236036495)
  ·
    refine ⟨50732688760521448854054743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33821792507014299236036495 50732688760521448854054743)
    ·
      refine ⟨76099033140782173281082115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50732688760521448854054743 76099033140782173281082115)
      ·
        refine ⟨114148549711173259921623173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76099033140782173281082115 114148549711173259921623173)
        ·
          refine ⟨21402853070844986235304345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114148549711173259921623173 21402853070844986235304345)
          ·
            refine ⟨16052139803133739676478259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21402853070844986235304345 16052139803133739676478259)
            ·
              refine ⟨24078209704700609514717389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16052139803133739676478259 24078209704700609514717389)
              ·
                refine ⟨9029328639262728568019021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24078209704700609514717389 9029328639262728568019021)
                ·
                  refine ⟨3385998239723523213007133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9029328639262728568019021 3385998239723523213007133)
                  ·
                    refine ⟨1269749339896321204877675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3385998239723523213007133 1269749339896321204877675)
                    ·
                      rfl

theorem cell22_3709242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_3709242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709242 prefixEnd_3709242 := by exact prefixLift 3709242
  have htrace : WordTrace (prefixWord ++ tailWord_3709242) baseStart_3709242 baseEnd_3709242 := by
    simpa [prefixWord, tailWord_3709242, baseEnd_3709242] using wordTrace_append hprefix tailTrace_3709242
  have hstable : (prefixWord ++ tailWord_3709242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709242).length < 2 ^ (prefixWord ++ tailWord_3709242).sum := by decide
  have hdescent : baseEnd_3709242 < baseStart_3709242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709278 : List Nat := [4, 4, 2, 1, 1, 2, 8]
def baseStart_3709278 : Nat := 118140960795 + 3709278 * 2 ^ 59
def prefixEnd_3709278 : Nat := 4983230072969 + 3 ^ 40 * 3709278 * 2
def baseEnd_3709278 : Nat := 47028209756741818925095

theorem tailTrace_3709278 : CollatzResearch.WordTrace tailWord_3709278 prefixEnd_3709278 47028209756741818925095 := by
  unfold tailWord_3709278
  simp only [CollatzResearch.WordTrace]
  refine ⟨16911060381990846886557061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90192322037284516728304325 16911060381990846886557061)
  ·
    refine ⟨3170823821623283791229449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16911060381990846886557061 3170823821623283791229449)
    ·
      refine ⟨2378117866217462843422087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3170823821623283791229449 2378117866217462843422087)
      ·
        refine ⟨3567176799326194265133131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2378117866217462843422087 3567176799326194265133131)
        ·
          refine ⟨5350765198989291397699697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3567176799326194265133131 5350765198989291397699697)
          ·
            refine ⟨4013073899241968548274773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5350765198989291397699697 4013073899241968548274773)
            ·
              refine ⟨47028209756741818925095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4013073899241968548274773 47028209756741818925095)
              ·
                rfl

theorem cell22_3709278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 8].length) (baseStart_3709278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709278 prefixEnd_3709278 := by exact prefixLift 3709278
  have htrace : WordTrace (prefixWord ++ tailWord_3709278) baseStart_3709278 baseEnd_3709278 := by
    simpa [prefixWord, tailWord_3709278, baseEnd_3709278] using wordTrace_append hprefix tailTrace_3709278
  have hstable : (prefixWord ++ tailWord_3709278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709278).length < 2 ^ (prefixWord ++ tailWord_3709278).sum := by decide
  have hdescent : baseEnd_3709278 < baseStart_3709278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709336 : List Nat := [2, 1, 2, 5, 1, 2, 3, 1, 1, 4]
def baseStart_3709336 : Nat := 118140960795 + 3709336 * 2 ^ 59
def prefixEnd_3709336 : Nat := 4983230072969 + 3 ^ 40 * 3709336 * 2
def baseEnd_3709336 : Nat := 1269781518017336293027387

theorem tailTrace_3709336 : CollatzResearch.WordTrace tailWord_3709336 prefixEnd_3709336 1269781518017336293027387 := by
  unfold tailWord_3709336
  simp only [CollatzResearch.WordTrace]
  refine ⟨67645299244858325499033931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90193732326477767332045241 67645299244858325499033931)
  ·
    refine ⟨101467948867287488248550897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67645299244858325499033931 101467948867287488248550897)
    ·
      refine ⟨76100961650465616186413173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101467948867287488248550897 76100961650465616186413173)
      ·
        refine ⟨7134465154731151517476235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76100961650465616186413173 7134465154731151517476235)
        ·
          refine ⟨10701697732096727276214353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7134465154731151517476235 10701697732096727276214353)
          ·
            refine ⟨8026273299072545457160765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10701697732096727276214353 8026273299072545457160765)
            ·
              refine ⟨3009852487152204546435287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8026273299072545457160765 3009852487152204546435287)
              ·
                refine ⟨4514778730728306819652931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3009852487152204546435287 4514778730728306819652931)
                ·
                  refine ⟨6772168096092460229479397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4514778730728306819652931 6772168096092460229479397)
                  ·
                    refine ⟨1269781518017336293027387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6772168096092460229479397 1269781518017336293027387)
                    ·
                      rfl

theorem cell22_3709336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 1, 4].length) (baseStart_3709336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709336 prefixEnd_3709336 := by exact prefixLift 3709336
  have htrace : WordTrace (prefixWord ++ tailWord_3709336) baseStart_3709336 baseEnd_3709336 := by
    simpa [prefixWord, tailWord_3709336, baseEnd_3709336] using wordTrace_append hprefix tailTrace_3709336
  have hstable : (prefixWord ++ tailWord_3709336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709336).length < 2 ^ (prefixWord ++ tailWord_3709336).sum := by decide
  have hdescent : baseEnd_3709336 < baseStart_3709336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709347 : List Nat := [1, 1, 1, 4, 1, 4, 2, 2, 2, 4]
def baseStart_3709347 : Nat := 118140960795 + 3709347 * 2 ^ 59
def prefixEnd_3709347 : Nat := 4983230072969 + 3 ^ 40 * 3709347 * 2
def baseEnd_3709347 : Nat := 1269785283542135931002353

theorem tailTrace_3709347 : CollatzResearch.WordTrace tailWord_3709347 prefixEnd_3709347 1269785283542135931002353 := by
  unfold tailWord_3709347
  simp only [CollatzResearch.WordTrace]
  refine ⟨135290999692676799876718295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90193999795117866584478863 135290999692676799876718295)
  ·
    refine ⟨202936499539015199815077443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135290999692676799876718295 202936499539015199815077443)
    ·
      refine ⟨304404749308522799722616165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202936499539015199815077443 304404749308522799722616165)
      ·
        refine ⟨57075890495348024947990531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304404749308522799722616165 57075890495348024947990531)
        ·
          refine ⟨85613835743022037421985797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57075890495348024947990531 85613835743022037421985797)
          ·
            refine ⟨16052594201816632016622337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85613835743022037421985797 16052594201816632016622337)
            ·
              refine ⟨12039445651362474012466753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16052594201816632016622337 12039445651362474012466753)
              ·
                refine ⟨9029584238521855509350065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12039445651362474012466753 9029584238521855509350065)
                ·
                  refine ⟨6772188178891391632012549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9029584238521855509350065 6772188178891391632012549)
                  ·
                    refine ⟨1269785283542135931002353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6772188178891391632012549 1269785283542135931002353)
                    ·
                      rfl

theorem cell22_3709347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 4].length) (baseStart_3709347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709347 prefixEnd_3709347 := by exact prefixLift 3709347
  have htrace : WordTrace (prefixWord ++ tailWord_3709347) baseStart_3709347 baseEnd_3709347 := by
    simpa [prefixWord, tailWord_3709347, baseEnd_3709347] using wordTrace_append hprefix tailTrace_3709347
  have hstable : (prefixWord ++ tailWord_3709347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709347).length < 2 ^ (prefixWord ++ tailWord_3709347).sum := by decide
  have hdescent : baseEnd_3709347 < baseStart_3709347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709349 : List Nat := [1, 3, 1, 2, 1, 1, 6, 2, 2, 3]
def baseStart_3709349 : Nat := 118140960795 + 3709349 * 2 ^ 59
def prefixEnd_3709349 : Nat := 4983230072969 + 3 ^ 40 * 3709349 * 2
def baseEnd_3709349 : Nat := 1269785968183008592452347

theorem tailTrace_3709349 : CollatzResearch.WordTrace tailWord_3709349 prefixEnd_3709349 1269785968183008592452347 := by
  unfold tailWord_3709349
  simp only [CollatzResearch.WordTrace]
  refine ⟨135291072638669554218291101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90194048425779702812194067 135291072638669554218291101)
  ·
    refine ⟨50734152239501082831859163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135291072638669554218291101 50734152239501082831859163)
    ·
      refine ⟨76101228359251624247788745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50734152239501082831859163 76101228359251624247788745)
      ·
        refine ⟨57075921269438718185841559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76101228359251624247788745 57075921269438718185841559)
        ·
          refine ⟨85613881904158077278762339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57075921269438718185841559 85613881904158077278762339)
          ·
            refine ⟨128420822856237115918143509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85613881904158077278762339 128420822856237115918143509)
            ·
              refine ⟨6019726071386114808662977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128420822856237115918143509 6019726071386114808662977)
              ·
                refine ⟨4514794553539586106497233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6019726071386114808662977 4514794553539586106497233)
                ·
                  refine ⟨3386095915154689579872925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4514794553539586106497233 3386095915154689579872925)
                  ·
                    refine ⟨1269785968183008592452347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3386095915154689579872925 1269785968183008592452347)
                    ·
                      rfl

theorem cell22_3709349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_3709349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709349 prefixEnd_3709349 := by exact prefixLift 3709349
  have htrace : WordTrace (prefixWord ++ tailWord_3709349) baseStart_3709349 baseEnd_3709349 := by
    simpa [prefixWord, tailWord_3709349, baseEnd_3709349] using wordTrace_append hprefix tailTrace_3709349
  have hstable : (prefixWord ++ tailWord_3709349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709349).length < 2 ^ (prefixWord ++ tailWord_3709349).sum := by decide
  have hdescent : baseEnd_3709349 < baseStart_3709349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709351 : List Nat := [1, 1, 6, 1, 1, 2, 4, 2, 4]
def baseStart_3709351 : Nat := 118140960795 + 3709351 * 2 ^ 59
def prefixEnd_3709351 : Nat := 4983230072969 + 3 ^ 40 * 3709351 * 2
def baseEnd_3709351 : Nat := 423262217607960417967447

theorem tailTrace_3709351 : CollatzResearch.WordTrace tailWord_3709351 prefixEnd_3709351 423262217607960417967447 := by
  unfold tailWord_3709351
  simp only [CollatzResearch.WordTrace]
  refine ⟨135291145584662308559863907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90194097056441539039909271 135291145584662308559863907)
  ·
    refine ⟨202936718376993462839795861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135291145584662308559863907 202936718376993462839795861)
    ·
      refine ⟨9512658673921568570615431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 202936718376993462839795861 9512658673921568570615431)
      ·
        refine ⟨14268988010882352855923147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9512658673921568570615431 14268988010882352855923147)
        ·
          refine ⟨21403482016323529283884721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14268988010882352855923147 21403482016323529283884721)
          ·
            refine ⟨16052611512242646962913541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21403482016323529283884721 16052611512242646962913541)
            ·
              refine ⟨3009864658545496305546289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16052611512242646962913541 3009864658545496305546289)
              ·
                refine ⟨2257398493909122229159717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3009864658545496305546289 2257398493909122229159717)
                ·
                  refine ⟨423262217607960417967447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2257398493909122229159717 423262217607960417967447)
                  ·
                    rfl

theorem cell22_3709351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 4].length) (baseStart_3709351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709351 prefixEnd_3709351 := by exact prefixLift 3709351
  have htrace : WordTrace (prefixWord ++ tailWord_3709351) baseStart_3709351 baseEnd_3709351 := by
    simpa [prefixWord, tailWord_3709351, baseEnd_3709351] using wordTrace_append hprefix tailTrace_3709351
  have hstable : (prefixWord ++ tailWord_3709351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709351).length < 2 ^ (prefixWord ++ tailWord_3709351).sum := by decide
  have hdescent : baseEnd_3709351 < baseStart_3709351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709407 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 7]
def baseStart_3709407 : Nat := 118140960795 + 3709407 * 2 ^ 59
def prefixEnd_3709407 : Nat := 4983230072969 + 3 ^ 40 * 3709407 * 2
def baseEnd_3709407 : Nat := 423268607589438591500723

theorem tailTrace_3709407 : CollatzResearch.WordTrace tailWord_3709407 prefixEnd_3709407 423268607589438591500723 := by
  unfold tailWord_3709407
  simp only [CollatzResearch.WordTrace]
  refine ⟨135293188072459430123902475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90195458714972953415934983 135293188072459430123902475)
  ·
    refine ⟨202939782108689145185853713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135293188072459430123902475 202939782108689145185853713)
    ·
      refine ⟨152204836581516858889390285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202939782108689145185853713 152204836581516858889390285)
      ·
        refine ⟨57076813718068822083521357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152204836581516858889390285 57076813718068822083521357)
        ·
          refine ⟨21403805144275808281320509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57076813718068822083521357 21403805144275808281320509)
          ·
            refine ⟨8026426929103428105495191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21403805144275808281320509 8026426929103428105495191)
            ·
              refine ⟨12039640393655142158242787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8026426929103428105495191 12039640393655142158242787)
              ·
                refine ⟨18059460590482713237364181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12039640393655142158242787 18059460590482713237364181)
                ·
                  refine ⟨423268607589438591500723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18059460590482713237364181 423268607589438591500723)
                  ·
                    rfl

theorem cell22_3709407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 7].length) (baseStart_3709407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709407 prefixEnd_3709407 := by exact prefixLift 3709407
  have htrace : WordTrace (prefixWord ++ tailWord_3709407) baseStart_3709407 baseEnd_3709407 := by
    simpa [prefixWord, tailWord_3709407, baseEnd_3709407] using wordTrace_append hprefix tailTrace_3709407
  have hstable : (prefixWord ++ tailWord_3709407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709407).length < 2 ^ (prefixWord ++ tailWord_3709407).sum := by decide
  have hdescent : baseEnd_3709407 < baseStart_3709407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709411 : List Nat := [1, 1, 1, 6, 3, 1, 2, 1, 3, 3]
def baseStart_3709411 : Nat := 118140960795 + 3709411 * 2 ^ 59
def prefixEnd_3709411 : Nat := 4983230072969 + 3 ^ 40 * 3709411 * 2
def baseEnd_3709411 : Nat := 1269807192050061097402157

theorem tailTrace_3709411 : CollatzResearch.WordTrace tailWord_3709411 prefixEnd_3709411 1269807192050061097402157 := by
  unfold tailWord_3709411
  simp only [CollatzResearch.WordTrace]
  refine ⟨135293333964444938807048087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90195555976296625871365391 135293333964444938807048087)
  ·
    refine ⟨202940000946667408210572131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135293333964444938807048087 202940000946667408210572131)
    ·
      refine ⟨304410001420001112315858197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202940000946667408210572131 304410001420001112315858197)
      ·
        refine ⟨14269218816562552139805853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 304410001420001112315858197 14269218816562552139805853)
        ·
          refine ⟨5350957056210957052427195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14269218816562552139805853 5350957056210957052427195)
          ·
            refine ⟨8026435584316435578640793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5350957056210957052427195 8026435584316435578640793)
            ·
              refine ⟨6019826688237326683980595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8026435584316435578640793 6019826688237326683980595)
              ·
                refine ⟨9029740032355990025970893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6019826688237326683980595 9029740032355990025970893)
                ·
                  refine ⟨3386152512133496259739085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9029740032355990025970893 3386152512133496259739085)
                  ·
                    refine ⟨1269807192050061097402157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3386152512133496259739085 1269807192050061097402157)
                    ·
                      rfl

theorem cell22_3709411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 3].length) (baseStart_3709411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709411 prefixEnd_3709411 := by exact prefixLift 3709411
  have htrace : WordTrace (prefixWord ++ tailWord_3709411) baseStart_3709411 baseEnd_3709411 := by
    simpa [prefixWord, tailWord_3709411, baseEnd_3709411] using wordTrace_append hprefix tailTrace_3709411
  have hstable : (prefixWord ++ tailWord_3709411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709411).length < 2 ^ (prefixWord ++ tailWord_3709411).sum := by decide
  have hdescent : baseEnd_3709411 < baseStart_3709411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709424 : List Nat := [2, 1, 1, 1, 3, 3, 5, 1, 5]
def baseStart_3709424 : Nat := 118140960795 + 3709424 * 2 ^ 59
def prefixEnd_3709424 : Nat := 4983230072969 + 3 ^ 40 * 3709424 * 2
def baseEnd_3709424 : Nat := 423270547405244465609039

theorem tailTrace_3709424 : CollatzResearch.WordTrace tailWord_3709424 prefixEnd_3709424 423270547405244465609039 := by
  unfold tailWord_3709424
  simp only [CollatzResearch.WordTrace]
  refine ⟨67646904056698921013635663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90195872075598561351514217 67646904056698921013635663)
  ·
    refine ⟨101470356085048381520453495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67646904056698921013635663 101470356085048381520453495)
    ·
      refine ⟨152205534127572572280680243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101470356085048381520453495 152205534127572572280680243)
      ·
        refine ⟨228308301191358858421020365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152205534127572572280680243 228308301191358858421020365)
        ·
          refine ⟨85615612946759571907882637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228308301191358858421020365 85615612946759571907882637)
          ·
            refine ⟨32105854855034839465455989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85615612946759571907882637 32105854855034839465455989)
            ·
              refine ⟨3009923892659516199886499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32105854855034839465455989 3009923892659516199886499)
              ·
                refine ⟨4514885838989274299829749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3009923892659516199886499 4514885838989274299829749)
                ·
                  refine ⟨423270547405244465609039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4514885838989274299829749 423270547405244465609039)
                  ·
                    rfl

theorem cell22_3709424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 5].length) (baseStart_3709424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709424 prefixEnd_3709424 := by exact prefixLift 3709424
  have htrace : WordTrace (prefixWord ++ tailWord_3709424) baseStart_3709424 baseEnd_3709424 := by
    simpa [prefixWord, tailWord_3709424, baseEnd_3709424] using wordTrace_append hprefix tailTrace_3709424
  have hstable : (prefixWord ++ tailWord_3709424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709424).length < 2 ^ (prefixWord ++ tailWord_3709424).sum := by decide
  have hdescent : baseEnd_3709424 < baseStart_3709424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709469 : List Nat := [1, 4, 2, 2, 1, 2, 3, 1, 6]
def baseStart_3709469 : Nat := 118140960795 + 3709469 * 2 ^ 59
def prefixEnd_3709469 : Nat := 4983230072969 + 3 ^ 40 * 3709469 * 2
def baseEnd_3709469 : Nat := 423275682211789426483993

theorem tailTrace_3709469 : CollatzResearch.WordTrace tailWord_3709469 prefixEnd_3709469 423275682211789426483993 := by
  unfold tailWord_3709469
  simp only [CollatzResearch.WordTrace]
  refine ⟨135295449398234814712659461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90196966265489876475106307 135295449398234814712659461)
  ·
    refine ⟨25367896762169027758623649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135295449398234814712659461 25367896762169027758623649)
    ·
      refine ⟨19025922571626770818967737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25367896762169027758623649 19025922571626770818967737)
      ·
        refine ⟨14269441928720078114225803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19025922571626770818967737 14269441928720078114225803)
        ·
          refine ⟨21404162893080117171338705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14269441928720078114225803 21404162893080117171338705)
          ·
            refine ⟨16053122169810087878504029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21404162893080117171338705 16053122169810087878504029)
            ·
              refine ⟨6019920813678782954439011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16053122169810087878504029 6019920813678782954439011)
              ·
                refine ⟨9029881220518174431658517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6019920813678782954439011 9029881220518174431658517)
                ·
                  refine ⟨423275682211789426483993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9029881220518174431658517 423275682211789426483993)
                  ·
                    rfl

theorem cell22_3709469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_3709469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709469 prefixEnd_3709469 := by exact prefixLift 3709469
  have htrace : WordTrace (prefixWord ++ tailWord_3709469) baseStart_3709469 baseEnd_3709469 := by
    simpa [prefixWord, tailWord_3709469, baseEnd_3709469] using wordTrace_append hprefix tailTrace_3709469
  have hstable : (prefixWord ++ tailWord_3709469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709469).length < 2 ^ (prefixWord ++ tailWord_3709469).sum := by decide
  have hdescent : baseEnd_3709469 < baseStart_3709469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709497 : List Nat := [1, 2, 1, 5, 1, 1, 1, 10]
def baseStart_3709497 : Nat := 118140960795 + 3709497 * 2 ^ 59
def prefixEnd_3709497 : Nat := 4983230072969 + 3 ^ 40 * 3709497 * 2
def baseEnd_3709497 : Nat := 141092959067509504416877

theorem tailTrace_3709497 : CollatzResearch.WordTrace tailWord_3709497 prefixEnd_3709497 141092959067509504416877 := by
  unfold tailWord_3709497
  simp only [CollatzResearch.WordTrace]
  refine ⟨135296470642133375494678745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90197647094755583663119163 135296470642133375494678745)
  ·
    refine ⟨101472352981600031621009059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135296470642133375494678745 101472352981600031621009059)
    ·
      refine ⟨152208529472400047431513589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101472352981600031621009059 152208529472400047431513589)
      ·
        refine ⟨14269549638037504446704399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152208529472400047431513589 14269549638037504446704399)
        ·
          refine ⟨21404324457056256670056599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14269549638037504446704399 21404324457056256670056599)
          ·
            refine ⟨32106486685584385005084899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21404324457056256670056599 32106486685584385005084899)
            ·
              refine ⟨48159730028376577507627349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32106486685584385005084899 48159730028376577507627349)
              ·
                refine ⟨141092959067509504416877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48159730028376577507627349 141092959067509504416877)
                ·
                  rfl

theorem cell22_3709497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 10].length) (baseStart_3709497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709497 prefixEnd_3709497 := by exact prefixLift 3709497
  have htrace : WordTrace (prefixWord ++ tailWord_3709497) baseStart_3709497 baseEnd_3709497 := by
    simpa [prefixWord, tailWord_3709497, baseEnd_3709497] using wordTrace_append hprefix tailTrace_3709497
  have hstable : (prefixWord ++ tailWord_3709497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709497).length < 2 ^ (prefixWord ++ tailWord_3709497).sum := by decide
  have hdescent : baseEnd_3709497 < baseStart_3709497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709527 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 1, 8]
def baseStart_3709527 : Nat := 118140960795 + 3709527 * 2 ^ 59
def prefixEnd_3709527 : Nat := 4983230072969 + 3 ^ 40 * 3709527 * 2
def baseEnd_3709527 : Nat := 1269846901220675461501801

theorem tailTrace_3709527 : CollatzResearch.WordTrace tailWord_3709527 prefixEnd_3709527 1269846901220675461501801 := by
  unfold tailWord_3709527
  simp only [CollatzResearch.WordTrace]
  refine ⟨135297564832024690618270835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90198376554683127078847223 135297564832024690618270835)
  ·
    refine ⟨202946347248037035927406253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135297564832024690618270835 202946347248037035927406253)
    ·
      refine ⟨76104880218013888472777345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202946347248037035927406253 76104880218013888472777345)
      ·
        refine ⟨57078660163510416354583009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76104880218013888472777345 57078660163510416354583009)
        ·
          refine ⟨42808995122632812265937257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57078660163510416354583009 42808995122632812265937257)
          ·
            refine ⟨32106746341974609199452943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42808995122632812265937257 32106746341974609199452943)
            ·
              refine ⟨48160119512961913799179415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32106746341974609199452943 48160119512961913799179415)
              ·
                refine ⟨72240179269442870698769123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48160119512961913799179415 72240179269442870698769123)
                ·
                  refine ⟨108360268904164306048153685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72240179269442870698769123 108360268904164306048153685)
                  ·
                    refine ⟨1269846901220675461501801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108360268904164306048153685 1269846901220675461501801)
                    ·
                      rfl

theorem cell22_3709527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_3709527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709527 prefixEnd_3709527 := by exact prefixLift 3709527
  have htrace : WordTrace (prefixWord ++ tailWord_3709527) baseStart_3709527 baseEnd_3709527 := by
    simpa [prefixWord, tailWord_3709527, baseEnd_3709527] using wordTrace_append hprefix tailTrace_3709527
  have hstable : (prefixWord ++ tailWord_3709527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709527).length < 2 ^ (prefixWord ++ tailWord_3709527).sum := by decide
  have hdescent : baseEnd_3709527 < baseStart_3709527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709546 : List Nat := [3, 1, 3, 2, 1, 1, 3, 2, 3, 3]
def baseStart_3709546 : Nat := 118140960795 + 3709546 * 2 ^ 59
def prefixEnd_3709546 : Nat := 4983230072969 + 3 ^ 40 * 3709546 * 2
def baseEnd_3709546 : Nat := 1269853405308965745276743

theorem tailTrace_3709546 : CollatzResearch.WordTrace tailWord_3709546 prefixEnd_3709546 1269853405308965745276743 := by
  unfold tailWord_3709546
  simp only [CollatzResearch.WordTrace]
  refine ⟨33824564454738964215803123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90198838545970571242141661 33824564454738964215803123)
  ·
    refine ⟨50736846682108446323704685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33824564454738964215803123 50736846682108446323704685)
    ·
      refine ⟨19026317505790667371389257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50736846682108446323704685 19026317505790667371389257)
      ·
        refine ⟨14269738129343000528541943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19026317505790667371389257 14269738129343000528541943)
        ·
          refine ⟨21404607194014500792812915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14269738129343000528541943 21404607194014500792812915)
          ·
            refine ⟨32106910791021751189219373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21404607194014500792812915 32106910791021751189219373)
            ·
              refine ⟨12040091546633156695957265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32106910791021751189219373 12040091546633156695957265)
              ·
                refine ⟨9030068659974867521967949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12040091546633156695957265 9030068659974867521967949)
                ·
                  refine ⟨3386275747490575320737981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9030068659974867521967949 3386275747490575320737981)
                  ·
                    refine ⟨1269853405308965745276743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3386275747490575320737981 1269853405308965745276743)
                    ·
                      rfl

theorem cell22_3709546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_3709546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709546 prefixEnd_3709546 := by exact prefixLift 3709546
  have htrace : WordTrace (prefixWord ++ tailWord_3709546) baseStart_3709546 baseEnd_3709546 := by
    simpa [prefixWord, tailWord_3709546, baseEnd_3709546] using wordTrace_append hprefix tailTrace_3709546
  have hstable : (prefixWord ++ tailWord_3709546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709546).length < 2 ^ (prefixWord ++ tailWord_3709546).sum := by decide
  have hdescent : baseEnd_3709546 < baseStart_3709546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709587 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 10]
def baseStart_3709587 : Nat := 118140960795 + 3709587 * 2 ^ 59
def prefixEnd_3709587 : Nat := 4983230072969 + 3 ^ 40 * 3709587 * 2
def baseEnd_3709587 : Nat := 423289146815618435000539

theorem tailTrace_3709587 : CollatzResearch.WordTrace tailWord_3709587 prefixEnd_3709587 423289146815618435000539 := by
  unfold tailWord_3709587
  simp only [CollatzResearch.WordTrace]
  refine ⟨135299753211807320865455015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90199835474538213910303343 135299753211807320865455015)
  ·
    refine ⟨202949629817710981298182523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135299753211807320865455015 202949629817710981298182523)
    ·
      refine ⟨304424444726566471947273785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202949629817710981298182523 304424444726566471947273785)
      ·
        refine ⟨228318333544924853960455339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304424444726566471947273785 228318333544924853960455339)
        ·
          refine ⟨342477500317387280940683009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228318333544924853960455339 342477500317387280940683009)
          ·
            refine ⟨256858125238040460705512257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342477500317387280940683009 256858125238040460705512257)
            ·
              refine ⟨192643593928530345529134193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256858125238040460705512257 192643593928530345529134193)
              ·
                refine ⟨144482695446397759146850645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192643593928530345529134193 144482695446397759146850645)
                ·
                  refine ⟨423289146815618435000539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 144482695446397759146850645 423289146815618435000539)
                  ·
                    rfl

theorem cell22_3709587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 10].length) (baseStart_3709587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709587 prefixEnd_3709587 := by exact prefixLift 3709587
  have htrace : WordTrace (prefixWord ++ tailWord_3709587) baseStart_3709587 baseEnd_3709587 := by
    simpa [prefixWord, tailWord_3709587, baseEnd_3709587] using wordTrace_append hprefix tailTrace_3709587
  have hstable : (prefixWord ++ tailWord_3709587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709587).length < 2 ^ (prefixWord ++ tailWord_3709587).sum := by decide
  have hdescent : baseEnd_3709587 < baseStart_3709587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709604 : List Nat := [2, 3, 1, 2, 2, 1, 1, 4, 6]
def baseStart_3709604 : Nat := 118140960795 + 3709604 * 2 ^ 59
def prefixEnd_3709604 : Nat := 4983230072969 + 3 ^ 40 * 3709604 * 2
def baseEnd_3709604 : Nat := 423291086631424309108855

theorem tailTrace_3709604 : CollatzResearch.WordTrace tailWord_3709604 prefixEnd_3709604 423291086631424309108855 := by
  unfold tailWord_3709604
  simp only [CollatzResearch.WordTrace]
  refine ⟨67650186626372866384411933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90200248835163821845882577 67650186626372866384411933)
  ·
    refine ⟨25368819984889824894154475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67650186626372866384411933 25368819984889824894154475)
    ·
      refine ⟨38053229977334737341231713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25368819984889824894154475 38053229977334737341231713)
      ·
        refine ⟨28539922483001053005923785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38053229977334737341231713 28539922483001053005923785)
        ·
          refine ⟨21404941862250789754442839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28539922483001053005923785 21404941862250789754442839)
          ·
            refine ⟨32107412793376184631664259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21404941862250789754442839 32107412793376184631664259)
            ·
              refine ⟨48161119190064276947496389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32107412793376184631664259 48161119190064276947496389)
              ·
                refine ⟨9030209848137051927655573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48161119190064276947496389 9030209848137051927655573)
                ·
                  refine ⟨423291086631424309108855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9030209848137051927655573 423291086631424309108855)
                  ·
                    rfl

theorem cell22_3709604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_3709604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709604 prefixEnd_3709604 := by exact prefixLift 3709604
  have htrace : WordTrace (prefixWord ++ tailWord_3709604) baseStart_3709604 baseEnd_3709604 := by
    simpa [prefixWord, tailWord_3709604, baseEnd_3709604] using wordTrace_append hprefix tailTrace_3709604
  have hstable : (prefixWord ++ tailWord_3709604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709604).length < 2 ^ (prefixWord ++ tailWord_3709604).sum := by decide
  have hdescent : baseEnd_3709604 < baseStart_3709604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709649 : List Nat := [1, 2, 2, 1, 2, 3, 4, 7]
def baseStart_3709649 : Nat := 118140960795 + 3709649 * 2 ^ 59
def prefixEnd_3709649 : Nat := 4983230072969 + 3 ^ 40 * 3709649 * 2
def baseEnd_3709649 : Nat := 141098740479323089994603

theorem tailTrace_3709649 : CollatzResearch.WordTrace tailWord_3709649 prefixEnd_3709649 141098740479323089994603 := by
  unfold tailWord_3709649
  simp only [CollatzResearch.WordTrace]
  refine ⟨135302014537582705454212001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90201343025055136969474667 135302014537582705454212001)
  ·
    refine ⟨101476510903187029090659001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135302014537582705454212001 101476510903187029090659001)
    ·
      refine ⟨76107383177390271817994251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101476510903187029090659001 76107383177390271817994251)
      ·
        refine ⟨114161074766085407726991377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76107383177390271817994251 114161074766085407726991377)
        ·
          refine ⟨85620806074564055795243533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114161074766085407726991377 85620806074564055795243533)
          ·
            refine ⟨32107802277961520923216325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85620806074564055795243533 32107802277961520923216325)
            ·
              refine ⟨6020212927117785173103061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32107802277961520923216325 6020212927117785173103061)
              ·
                refine ⟨141098740479323089994603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6020212927117785173103061 141098740479323089994603)
                ·
                  rfl

theorem cell22_3709649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 7].length) (baseStart_3709649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709649 prefixEnd_3709649 := by exact prefixLift 3709649
  have htrace : WordTrace (prefixWord ++ tailWord_3709649) baseStart_3709649 baseEnd_3709649 := by
    simpa [prefixWord, tailWord_3709649, baseEnd_3709649] using wordTrace_append hprefix tailTrace_3709649
  have hstable : (prefixWord ++ tailWord_3709649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709649).length < 2 ^ (prefixWord ++ tailWord_3709649).sum := by decide
  have hdescent : baseEnd_3709649 < baseStart_3709649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709732 : List Nat := [2, 3, 1, 3, 3, 1, 2, 3, 1, 3]
def baseStart_3709732 : Nat := 118140960795 + 3709732 * 2 ^ 59
def prefixEnd_3709732 : Nat := 4983230072969 + 3 ^ 40 * 3709732 * 2
def baseEnd_3709732 : Nat := 1269917076910123260126173

theorem tailTrace_3709732 : CollatzResearch.WordTrace tailWord_3709732 prefixEnd_3709732 1269917076910123260126173 := by
  unfold tailWord_3709732
  simp only [CollatzResearch.WordTrace]
  refine ⟨67652520898141005314741725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90203361197521340419655633 67652520898141005314741725)
  ·
    refine ⟨25369695336802876993028147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67652520898141005314741725 25369695336802876993028147)
    ·
      refine ⟨38054543005204315489542221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25369695336802876993028147 38054543005204315489542221)
      ·
        refine ⟨14270453626951618308578333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38054543005204315489542221 14270453626951618308578333)
        ·
          refine ⟨5351420110106856865716875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14270453626951618308578333 5351420110106856865716875)
          ·
            refine ⟨8027130165160285298575313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5351420110106856865716875 8027130165160285298575313)
            ·
              refine ⟨6020347623870213973931485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8027130165160285298575313 6020347623870213973931485)
              ·
                refine ⟨2257630358951330240224307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6020347623870213973931485 2257630358951330240224307)
                ·
                  refine ⟨3386445538426995360336461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2257630358951330240224307 3386445538426995360336461)
                  ·
                    refine ⟨1269917076910123260126173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3386445538426995360336461 1269917076910123260126173)
                    ·
                      rfl

theorem cell22_3709732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_3709732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709732 prefixEnd_3709732 := by exact prefixLift 3709732
  have htrace : WordTrace (prefixWord ++ tailWord_3709732) baseStart_3709732 baseEnd_3709732 := by
    simpa [prefixWord, tailWord_3709732, baseEnd_3709732] using wordTrace_append hprefix tailTrace_3709732
  have hstable : (prefixWord ++ tailWord_3709732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709732).length < 2 ^ (prefixWord ++ tailWord_3709732).sum := by decide
  have hdescent : baseEnd_3709732 < baseStart_3709732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709786 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 1, 6]
def baseStart_3709786 : Nat := 118140960795 + 3709786 * 2 ^ 59
def prefixEnd_3709786 : Nat := 4983230072969 + 3 ^ 40 * 3709786 * 2
def baseEnd_3709786 : Nat := 1269935562213685119276007

theorem tailTrace_3709786 : CollatzResearch.WordTrace tailWord_3709786 prefixEnd_3709786 1269935562213685119276007 := by
  unfold tailWord_3709786
  simp only [CollatzResearch.WordTrace]
  refine ⟨33826752834521594462987303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90204674225390918567966141 33826752834521594462987303)
  ·
    refine ⟨50740129251782391694480955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33826752834521594462987303 50740129251782391694480955)
    ·
      refine ⟨76110193877673587541721433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50740129251782391694480955 76110193877673587541721433)
      ·
        refine ⟨57082645408255190656291075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76110193877673587541721433 57082645408255190656291075)
        ·
          refine ⟨85623968112382785984436613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57082645408255190656291075 85623968112382785984436613)
          ·
            refine ⟨16054494021071772372081865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85623968112382785984436613 16054494021071772372081865)
            ·
              refine ⟨12040870515803829279061399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16054494021071772372081865 12040870515803829279061399)
              ·
                refine ⟨18061305773705743918592099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12040870515803829279061399 18061305773705743918592099)
                ·
                  refine ⟨27091958660558615877888149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18061305773705743918592099 27091958660558615877888149)
                  ·
                    refine ⟨1269935562213685119276007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27091958660558615877888149 1269935562213685119276007)
                    ·
                      rfl

theorem cell22_3709786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_3709786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709786 prefixEnd_3709786 := by exact prefixLift 3709786
  have htrace : WordTrace (prefixWord ++ tailWord_3709786) baseStart_3709786 baseEnd_3709786 := by
    simpa [prefixWord, tailWord_3709786, baseEnd_3709786] using wordTrace_append hprefix tailTrace_3709786
  have hstable : (prefixWord ++ tailWord_3709786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709786).length < 2 ^ (prefixWord ++ tailWord_3709786).sum := by decide
  have hdescent : baseEnd_3709786 < baseStart_3709786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709826 : List Nat := [3, 4, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_3709826 : Nat := 118140960795 + 3709826 * 2 ^ 59
def prefixEnd_3709826 : Nat := 4983230072969 + 3 ^ 40 * 3709826 * 2
def baseEnd_3709826 : Nat := 1269949255031138348275885

theorem tailTrace_3709826 : CollatzResearch.WordTrace tailWord_3709826 prefixEnd_3709826 1269949255031138348275885 := by
  unfold tailWord_3709826
  simp only [CollatzResearch.WordTrace]
  refine ⟨33827117564485366170851333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90205646838627643122270221 33827117564485366170851333)
  ·
    refine ⟨6342584543341006157034625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33827117564485366170851333 6342584543341006157034625)
    ·
      refine ⟨4756938407505754617775969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6342584543341006157034625 4756938407505754617775969)
      ·
        refine ⟨3567703805629315963331977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4756938407505754617775969 3567703805629315963331977)
        ·
          refine ⟨2675777854221986972498983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3567703805629315963331977 2675777854221986972498983)
          ·
            refine ⟨4013666781332980458748475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675777854221986972498983 4013666781332980458748475)
            ·
              refine ⟨6020500171999470688122713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4013666781332980458748475 6020500171999470688122713)
              ·
                refine ⟨4515375128999603016092035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6020500171999470688122713 4515375128999603016092035)
                ·
                  refine ⟨6773062693499404524138053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4515375128999603016092035 6773062693499404524138053)
                  ·
                    refine ⟨1269949255031138348275885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6773062693499404524138053 1269949255031138348275885)
                    ·
                      rfl

theorem cell22_3709826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_3709826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709826 prefixEnd_3709826 := by exact prefixLift 3709826
  have htrace : WordTrace (prefixWord ++ tailWord_3709826) baseStart_3709826 baseEnd_3709826 := by
    simpa [prefixWord, tailWord_3709826, baseEnd_3709826] using wordTrace_append hprefix tailTrace_3709826
  have hstable : (prefixWord ++ tailWord_3709826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709826).length < 2 ^ (prefixWord ++ tailWord_3709826).sum := by decide
  have hdescent : baseEnd_3709826 < baseStart_3709826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709891 : List Nat := [1, 1, 1, 3, 1, 1, 2, 6, 6]
def baseStart_3709891 : Nat := 118140960795 + 3709891 * 2 ^ 59
def prefixEnd_3709891 : Nat := 4983230072969 + 3 ^ 40 * 3709891 * 2
def baseEnd_3709891 : Nat := 423323835286499948466895

theorem tailTrace_3709891 : CollatzResearch.WordTrace tailWord_3709891 prefixEnd_3709891 423323835286499948466895 := by
  unfold tailWord_3709891
  simp only [CollatzResearch.WordTrace]
  refine ⟨135310841002705980784521527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90207227335137320523014351 135310841002705980784521527)
  ·
    refine ⟨202966261504058971176782291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135310841002705980784521527 202966261504058971176782291)
    ·
      refine ⟨304449392256088456765173437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202966261504058971176782291 304449392256088456765173437)
      ·
        refine ⟨114168522096033171286940039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304449392256088456765173437 114168522096033171286940039)
        ·
          refine ⟨171252783144049756930410059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114168522096033171286940039 171252783144049756930410059)
          ·
            refine ⟨256879174716074635395615089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171252783144049756930410059 256879174716074635395615089)
            ·
              refine ⟨192659381037055976546711317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256879174716074635395615089 192659381037055976546711317)
              ·
                refine ⟨9030908486111998900627093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 192659381037055976546711317 9030908486111998900627093)
                ·
                  refine ⟨423323835286499948466895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9030908486111998900627093 423323835286499948466895)
                  ·
                    rfl

theorem cell22_3709891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 6].length) (baseStart_3709891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709891 prefixEnd_3709891 := by exact prefixLift 3709891
  have htrace : WordTrace (prefixWord ++ tailWord_3709891) baseStart_3709891 baseEnd_3709891 := by
    simpa [prefixWord, tailWord_3709891, baseEnd_3709891] using wordTrace_append hprefix tailTrace_3709891
  have hstable : (prefixWord ++ tailWord_3709891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709891).length < 2 ^ (prefixWord ++ tailWord_3709891).sum := by decide
  have hdescent : baseEnd_3709891 < baseStart_3709891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709936 : List Nat := [2, 1, 1, 1, 3, 2, 1, 11]
def baseStart_3709936 : Nat := 118140960795 + 3709936 * 2 ^ 59
def prefixEnd_3709936 : Nat := 4983230072969 + 3 ^ 40 * 3709936 * 2
def baseEnd_3709936 : Nat := 141109656697681636447283

theorem tailTrace_3709936 : CollatzResearch.WordTrace tailWord_3709936 prefixEnd_3709936 141109656697681636447283 := by
  unfold tailWord_3709936
  simp only [CollatzResearch.WordTrace]
  refine ⟨67656241143771476734954831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90208321525028635646606441 67656241143771476734954831)
  ·
    refine ⟨101484361715657215102432247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67656241143771476734954831 101484361715657215102432247)
    ·
      refine ⟨152226542573485822653648371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101484361715657215102432247 152226542573485822653648371)
      ·
        refine ⟨228339813860228733980472557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152226542573485822653648371 228339813860228733980472557)
        ·
          refine ⟨85627430197585775242677209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228339813860228733980472557 85627430197585775242677209)
          ·
            refine ⟨64220572648189331432007907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85627430197585775242677209 64220572648189331432007907)
            ·
              refine ⟨96330858972283997148011861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64220572648189331432007907 96330858972283997148011861)
              ·
                refine ⟨141109656697681636447283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 96330858972283997148011861 141109656697681636447283)
                ·
                  rfl

theorem cell22_3709936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 11].length) (baseStart_3709936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709936 prefixEnd_3709936 := by exact prefixLift 3709936
  have htrace : WordTrace (prefixWord ++ tailWord_3709936) baseStart_3709936 baseEnd_3709936 := by
    simpa [prefixWord, tailWord_3709936, baseEnd_3709936] using wordTrace_append hprefix tailTrace_3709936
  have hstable : (prefixWord ++ tailWord_3709936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709936).length < 2 ^ (prefixWord ++ tailWord_3709936).sum := by decide
  have hdescent : baseEnd_3709936 < baseStart_3709936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709953 : List Nat := [1, 2, 4, 1, 2, 3, 1, 8]
def baseStart_3709953 : Nat := 118140960795 + 3709953 * 2 ^ 59
def prefixEnd_3709953 : Nat := 4983230072969 + 3 ^ 40 * 3709953 * 2
def baseEnd_3709953 : Nat := 141110303302950261150055

theorem tailTrace_3709953 : CollatzResearch.WordTrace tailWord_3709953 prefixEnd_3709953 141110303302950261150055 := by
  unfold tailWord_3709953
  simp only [CollatzResearch.WordTrace]
  refine ⟨135313102328481365373278513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90208734885654243582185675 135313102328481365373278513)
  ·
    refine ⟨101484826746361024029958885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135313102328481365373278513 101484826746361024029958885)
    ·
      refine ⟨19028405014942692005617291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101484826746361024029958885 19028405014942692005617291)
      ·
        refine ⟨28542607522414038008425937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19028405014942692005617291 28542607522414038008425937)
        ·
          refine ⟨21406955641810528506319453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28542607522414038008425937 21406955641810528506319453)
          ·
            refine ⟨8027608365678948189869795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21406955641810528506319453 8027608365678948189869795)
            ·
              refine ⟨12041412548518422284804693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8027608365678948189869795 12041412548518422284804693)
              ·
                refine ⟨141110303302950261150055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12041412548518422284804693 141110303302950261150055)
                ·
                  rfl

theorem cell22_3709953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 8].length) (baseStart_3709953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709953 prefixEnd_3709953 := by exact prefixLift 3709953
  have htrace : WordTrace (prefixWord ++ tailWord_3709953) baseStart_3709953 baseEnd_3709953 := by
    simpa [prefixWord, tailWord_3709953, baseEnd_3709953] using wordTrace_append hprefix tailTrace_3709953
  have hstable : (prefixWord ++ tailWord_3709953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709953).length < 2 ^ (prefixWord ++ tailWord_3709953).sum := by decide
  have hdescent : baseEnd_3709953 < baseStart_3709953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709991 : List Nat := [1, 1, 7, 1, 1, 3, 2, 1, 2, 3]
def baseStart_3709991 : Nat := 118140960795 + 3709991 * 2 ^ 59
def prefixEnd_3709991 : Nat := 4983230072969 + 3 ^ 40 * 3709991 * 2
def baseEnd_3709991 : Nat := 1270005737903132917900379

theorem tailTrace_3709991 : CollatzResearch.WordTrace tailWord_3709991 prefixEnd_3709991 1270005737903132917900379 := by
  unfold tailWord_3709991
  simp only [CollatzResearch.WordTrace]
  refine ⟨135314488302343697863161827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90209658868229131908774551 135314488302343697863161827)
  ·
    refine ⟨202971732453515546794742741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135314488302343697863161827 202971732453515546794742741)
    ·
      refine ⟨4757149979379270628001783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 202971732453515546794742741 4757149979379270628001783)
      ·
        refine ⟨7135724969068905942002675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4757149979379270628001783 7135724969068905942002675)
        ·
          refine ⟨10703587453603358913004013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7135724969068905942002675 10703587453603358913004013)
          ·
            refine ⟨4013845295101259592376505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10703587453603358913004013 4013845295101259592376505)
            ·
              refine ⟨3010383971325944694282379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4013845295101259592376505 3010383971325944694282379)
              ·
                refine ⟨4515575956988917041423569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3010383971325944694282379 4515575956988917041423569)
                ·
                  refine ⟨3386681967741687781067677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4515575956988917041423569 3386681967741687781067677)
                  ·
                    refine ⟨1270005737903132917900379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3386681967741687781067677 1270005737903132917900379)
                    ·
                      rfl

theorem cell22_3709991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_3709991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709991 prefixEnd_3709991 := by exact prefixLift 3709991
  have htrace : WordTrace (prefixWord ++ tailWord_3709991) baseStart_3709991 baseEnd_3709991 := by
    simpa [prefixWord, tailWord_3709991, baseEnd_3709991] using wordTrace_append hprefix tailTrace_3709991
  have hstable : (prefixWord ++ tailWord_3709991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709991).length < 2 ^ (prefixWord ++ tailWord_3709991).sum := by decide
  have hdescent : baseEnd_3709991 < baseStart_3709991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710077 : List Nat := [1, 4, 1, 1, 3, 1, 4, 3, 4]
def baseStart_3710077 : Nat := 118140960795 + 3710077 * 2 ^ 59
def prefixEnd_3710077 : Nat := 4983230072969 + 3 ^ 40 * 3710077 * 2
def baseEnd_3710077 : Nat := 423345059153552453416705

theorem tailTrace_3710077 : CollatzResearch.WordTrace tailWord_3710077 prefixEnd_3710077 423345059153552453416705 := by
  unfold tailWord_3710077
  simp only [CollatzResearch.WordTrace]
  refine ⟨135317624980032134550792485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90211749986688089700528323 135317624980032134550792485)
  ·
    refine ⟨25372054683756025228273591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135317624980032134550792485 25372054683756025228273591)
    ·
      refine ⟨38058082025634037842410387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25372054683756025228273591 38058082025634037842410387)
      ·
        refine ⟨57087123038451056763615581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38058082025634037842410387 57087123038451056763615581)
        ·
          refine ⟨21407671139419146286355843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57087123038451056763615581 21407671139419146286355843)
          ·
            refine ⟨32111506709128719429533765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21407671139419146286355843 32111506709128719429533765)
            ·
              refine ⟨6020907507961634893037581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32111506709128719429533765 6020907507961634893037581)
              ·
                refine ⟨2257840315485613084889093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6020907507961634893037581 2257840315485613084889093)
                ·
                  refine ⟨423345059153552453416705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2257840315485613084889093 423345059153552453416705)
                  ·
                    rfl

theorem cell22_3710077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_3710077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710077 prefixEnd_3710077 := by exact prefixLift 3710077
  have htrace : WordTrace (prefixWord ++ tailWord_3710077) baseStart_3710077 baseEnd_3710077 := by
    simpa [prefixWord, tailWord_3710077, baseEnd_3710077] using wordTrace_append hprefix tailTrace_3710077
  have hstable : (prefixWord ++ tailWord_3710077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710077).length < 2 ^ (prefixWord ++ tailWord_3710077).sum := by decide
  have hdescent : baseEnd_3710077 < baseStart_3710077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710090 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 4, 4]
def baseStart_3710090 : Nat := 118140960795 + 3710090 * 2 ^ 59
def prefixEnd_3710090 : Nat := 4983230072969 + 3 ^ 40 * 3710090 * 2
def baseEnd_3710090 : Nat := 1270039627626329659675075

theorem tailTrace_3710090 : CollatzResearch.WordTrace tailWord_3710090 prefixEnd_3710090 1270039627626329659675075 := by
  unfold tailWord_3710090
  simp only [CollatzResearch.WordTrace]
  refine ⟨33829524782246259442753931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90212066085990025180677149 33829524782246259442753931)
  ·
    refine ⟨50744287173369389164130897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33829524782246259442753931 50744287173369389164130897)
    ·
      refine ⟨38058215380027041873098173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50744287173369389164130897 38058215380027041873098173)
      ·
        refine ⟨14271830767510140702411815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38058215380027041873098173 14271830767510140702411815)
        ·
          refine ⟨21407746151265211053617723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14271830767510140702411815 21407746151265211053617723)
          ·
            refine ⟨32111619226897816580426585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21407746151265211053617723 32111619226897816580426585)
            ·
              refine ⟨24083714420173362435319939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32111619226897816580426585 24083714420173362435319939)
              ·
                refine ⟨36125571630260043652979909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24083714420173362435319939 36125571630260043652979909)
                ·
                  refine ⟨6773544680673758184933733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36125571630260043652979909 6773544680673758184933733)
                  ·
                    refine ⟨1270039627626329659675075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6773544680673758184933733 1270039627626329659675075)
                    ·
                      rfl

theorem cell22_3710090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_3710090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710090 prefixEnd_3710090 := by exact prefixLift 3710090
  have htrace : WordTrace (prefixWord ++ tailWord_3710090) baseStart_3710090 baseEnd_3710090 := by
    simpa [prefixWord, tailWord_3710090, baseEnd_3710090] using wordTrace_append hprefix tailTrace_3710090
  have hstable : (prefixWord ++ tailWord_3710090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710090).length < 2 ^ (prefixWord ++ tailWord_3710090).sum := by decide
  have hdescent : baseEnd_3710090 < baseStart_3710090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710109 : List Nat := [1, 4, 2, 1, 1, 2, 5, 1, 2, 3]
def baseStart_3710109 : Nat := 118140960795 + 3710109 * 2 ^ 59
def prefixEnd_3710109 : Nat := 4983230072969 + 3 ^ 40 * 3710109 * 2
def baseEnd_3710109 : Nat := 1270046131714619943450017

theorem tailTrace_3710109 : CollatzResearch.WordTrace tailWord_3710109 prefixEnd_3710109 1270046131714619943450017 := by
  unfold tailWord_3710109
  simp only [CollatzResearch.WordTrace]
  refine ⟨135318792115916204015957381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90212528077277469343971587 135318792115916204015957381)
  ·
    refine ⟨25372273521734288252992009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135318792115916204015957381 25372273521734288252992009)
    ·
      refine ⟨19029205141300716189744007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25372273521734288252992009 19029205141300716189744007)
      ·
        refine ⟨28543807711951074284616011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19029205141300716189744007 28543807711951074284616011)
        ·
          refine ⟨42815711567926611426924017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28543807711951074284616011 42815711567926611426924017)
          ·
            refine ⟨32111783675944958570193013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42815711567926611426924017 32111783675944958570193013)
            ·
              refine ⟨3010479719619839865955595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32111783675944958570193013 3010479719619839865955595)
              ·
                refine ⟨4515719579429759798933393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3010479719619839865955595 4515719579429759798933393)
                ·
                  refine ⟨3386789684572319849200045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4515719579429759798933393 3386789684572319849200045)
                  ·
                    refine ⟨1270046131714619943450017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3386789684572319849200045 1270046131714619943450017)
                    ·
                      rfl

theorem cell22_3710109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_3710109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710109 prefixEnd_3710109 := by exact prefixLift 3710109
  have htrace : WordTrace (prefixWord ++ tailWord_3710109) baseStart_3710109 baseEnd_3710109 := by
    simpa [prefixWord, tailWord_3710109, baseEnd_3710109] using wordTrace_append hprefix tailTrace_3710109
  have hstable : (prefixWord ++ tailWord_3710109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710109).length < 2 ^ (prefixWord ++ tailWord_3710109).sum := by decide
  have hdescent : baseEnd_3710109 < baseStart_3710109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710122 : List Nat := [3, 1, 5, 1, 1, 2, 1, 8]
def baseStart_3710122 : Nat := 118140960795 + 3710122 * 2 ^ 59
def prefixEnd_3710122 : Nat := 4983230072969 + 3 ^ 40 * 3710122 * 2
def baseEnd_3710122 : Nat := 141116731320032471430553

theorem tailTrace_3710122 : CollatzResearch.WordTrace tailWord_3710122 prefixEnd_3710122 141116731320032471430553 := by
  unfold tailWord_3710122
  simp only [CollatzResearch.WordTrace]
  refine ⟨33829816566217276809045155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90212844176579404824120413 33829816566217276809045155)
  ·
    refine ⟨50744724849325915213567733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33829816566217276809045155 50744724849325915213567733)
    ·
      refine ⟨4757317954624304551271975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50744724849325915213567733 4757317954624304551271975)
      ·
        refine ⟨7135976931936456826907963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4757317954624304551271975 7135976931936456826907963)
        ·
          refine ⟨10703965397904685240361945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7135976931936456826907963 10703965397904685240361945)
          ·
            refine ⟨8027974048428513930271459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10703965397904685240361945 8027974048428513930271459)
            ·
              refine ⟨12041961072642770895407189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8027974048428513930271459 12041961072642770895407189)
              ·
                refine ⟨141116731320032471430553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12041961072642770895407189 141116731320032471430553)
                ·
                  rfl

theorem cell22_3710122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 8].length) (baseStart_3710122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710122 prefixEnd_3710122 := by exact prefixLift 3710122
  have htrace : WordTrace (prefixWord ++ tailWord_3710122) baseStart_3710122 baseEnd_3710122 := by
    simpa [prefixWord, tailWord_3710122, baseEnd_3710122] using wordTrace_append hprefix tailTrace_3710122
  have hstable : (prefixWord ++ tailWord_3710122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710122).length < 2 ^ (prefixWord ++ tailWord_3710122).sum := by decide
  have hdescent : baseEnd_3710122 < baseStart_3710122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710154 : List Nat := [3, 1, 2, 1, 3, 4, 1, 1, 3, 3]
def baseStart_3710154 : Nat := 118140960795 + 3710154 * 2 ^ 59
def prefixEnd_3710154 : Nat := 4983230072969 + 3 ^ 40 * 3710154 * 2
def baseEnd_3710154 : Nat := 1270061536134254826074879

theorem tailTrace_3710154 : CollatzResearch.WordTrace tailWord_3710154 prefixEnd_3710154 1270061536134254826074879 := by
  unfold tailWord_3710154
  simp only [CollatzResearch.WordTrace]
  refine ⟨33830108350188294175336379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90213622267168784467563677 33830108350188294175336379)
  ·
    refine ⟨50745162525282441263004569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33830108350188294175336379 50745162525282441263004569)
    ·
      refine ⟨38058871893961830947253427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50745162525282441263004569 38058871893961830947253427)
      ·
        refine ⟨57088307840942746420880141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38058871893961830947253427 57088307840942746420880141)
        ·
          refine ⟨21408115440353529907830053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57088307840942746420880141 21408115440353529907830053)
          ·
            refine ⟨4014021645066286857718135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21408115440353529907830053 4014021645066286857718135)
            ·
              refine ⟨6021032467599430286577203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4014021645066286857718135 6021032467599430286577203)
              ·
                refine ⟨9031548701399145429865805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6021032467599430286577203 9031548701399145429865805)
                ·
                  refine ⟨3386830763024679536199677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9031548701399145429865805 3386830763024679536199677)
                  ·
                    refine ⟨1270061536134254826074879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3386830763024679536199677 1270061536134254826074879)
                    ·
                      rfl

theorem cell22_3710154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_3710154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710154 prefixEnd_3710154 := by exact prefixLift 3710154
  have htrace : WordTrace (prefixWord ++ tailWord_3710154) baseStart_3710154 baseEnd_3710154 := by
    simpa [prefixWord, tailWord_3710154, baseEnd_3710154] using wordTrace_append hprefix tailTrace_3710154
  have hstable : (prefixWord ++ tailWord_3710154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710154).length < 2 ^ (prefixWord ++ tailWord_3710154).sum := by decide
  have hdescent : baseEnd_3710154 < baseStart_3710154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710167 : List Nat := [1, 1, 3, 2, 1, 2, 6, 1, 5]
def baseStart_3710167 : Nat := 118140960795 + 3710167 * 2 ^ 59
def prefixEnd_3710167 : Nat := 4983230072969 + 3 ^ 40 * 3710167 * 2
def baseEnd_3710167 : Nat := 423355328766642375166613

theorem tailTrace_3710167 : CollatzResearch.WordTrace tailWord_3710167 prefixEnd_3710167 423355328766642375166613 := by
  unfold tailWord_3710167
  simp only [CollatzResearch.WordTrace]
  refine ⟨135320907549706079921568755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90213938366470719947712503 135320907549706079921568755)
  ·
    refine ⟨202981361324559119882353133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135320907549706079921568755 202981361324559119882353133)
    ·
      refine ⟨76118010496709669955882425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202981361324559119882353133 76118010496709669955882425)
      ·
        refine ⟨57088507872532252466911819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76118010496709669955882425 57088507872532252466911819)
        ·
          refine ⟨85632761808798378700367729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57088507872532252466911819 85632761808798378700367729)
          ·
            refine ⟨64224571356598784025275797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85632761808798378700367729 64224571356598784025275797)
            ·
              refine ⟨3010526782340568001184803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64224571356598784025275797 3010526782340568001184803)
              ·
                refine ⟨4515790173510852001777205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3010526782340568001184803 4515790173510852001777205)
                ·
                  refine ⟨423355328766642375166613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4515790173510852001777205 423355328766642375166613)
                  ·
                    rfl

theorem cell22_3710167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 5].length) (baseStart_3710167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710167 prefixEnd_3710167 := by exact prefixLift 3710167
  have htrace : WordTrace (prefixWord ++ tailWord_3710167) baseStart_3710167 baseEnd_3710167 := by
    simpa [prefixWord, tailWord_3710167, baseEnd_3710167] using wordTrace_append hprefix tailTrace_3710167
  have hstable : (prefixWord ++ tailWord_3710167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710167).length < 2 ^ (prefixWord ++ tailWord_3710167).sum := by decide
  have hdescent : baseEnd_3710167 < baseStart_3710167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710225 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 1, 6]
def baseStart_3710225 : Nat := 118140960795 + 3710225 * 2 ^ 59
def prefixEnd_3710225 : Nat := 4983230072969 + 3 ^ 40 * 3710225 * 2
def baseEnd_3710225 : Nat := 1270085840885234307549661

theorem tailTrace_3710225 : CollatzResearch.WordTrace tailWord_3710225 prefixEnd_3710225 1270085840885234307549661 := by
  unfold tailWord_3710225
  simp only [CollatzResearch.WordTrace]
  refine ⟨135323022983495955827180129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90215348655663970551453419 135323022983495955827180129)
  ·
    refine ⟨101492267237621966870385097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135323022983495955827180129 101492267237621966870385097)
    ·
      refine ⟨76119200428216475152788823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101492267237621966870385097 76119200428216475152788823)
      ·
        refine ⟨114178800642324712729183235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76119200428216475152788823 114178800642324712729183235)
        ·
          refine ⟨171268200963487069093774853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114178800642324712729183235 171268200963487069093774853)
          ·
            refine ⟨32112787680653825455082785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171268200963487069093774853 32112787680653825455082785)
            ·
              refine ⟨24084590760490369091312089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32112787680653825455082785 24084590760490369091312089)
              ·
                refine ⟨18063443070367776818484067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24084590760490369091312089 18063443070367776818484067)
                ·
                  refine ⟨27095164605551665227726101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18063443070367776818484067 27095164605551665227726101)
                  ·
                    refine ⟨1270085840885234307549661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27095164605551665227726101 1270085840885234307549661)
                    ·
                      rfl

theorem cell22_3710225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_3710225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710225 prefixEnd_3710225 := by exact prefixLift 3710225
  have htrace : WordTrace (prefixWord ++ tailWord_3710225) baseStart_3710225 baseEnd_3710225 := by
    simpa [prefixWord, tailWord_3710225, baseEnd_3710225] using wordTrace_append hprefix tailTrace_3710225
  have hstable : (prefixWord ++ tailWord_3710225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710225).length < 2 ^ (prefixWord ++ tailWord_3710225).sum := by decide
  have hdescent : baseEnd_3710225 < baseStart_3710225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710261 : List Nat := [1, 3, 3, 1, 2, 4, 1, 2, 2, 3]
def baseStart_3710261 : Nat := 118140960795 + 3710261 * 2 ^ 59
def prefixEnd_3710261 : Nat := 4983230072969 + 3 ^ 40 * 3710261 * 2
def baseEnd_3710261 : Nat := 1270098164420942213649551

theorem tailTrace_3710261 : CollatzResearch.WordTrace tailWord_3710261 prefixEnd_3710261 1270098164420942213649551 := by
  unfold tailWord_3710261
  simp only [CollatzResearch.WordTrace]
  refine ⟨135324336011365533975490637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90216224007577022650327091 135324336011365533975490637)
  ·
    refine ⟨50746626004262075240808989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135324336011365533975490637 50746626004262075240808989)
    ·
      refine ⟨19029984751598278215303371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50746626004262075240808989 19029984751598278215303371)
      ·
        refine ⟨28544977127397417322955057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19029984751598278215303371 28544977127397417322955057)
        ·
          refine ⟨21408732845548062992216293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28544977127397417322955057 21408732845548062992216293)
          ·
            refine ⟨4014137408540261811040555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21408732845548062992216293 4014137408540261811040555)
            ·
              refine ⟨6021206112810392716560833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4014137408540261811040555 6021206112810392716560833)
              ·
                refine ⟨4515904584607794537420625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6021206112810392716560833 4515904584607794537420625)
                ·
                  refine ⟨3386928438455845903065469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4515904584607794537420625 3386928438455845903065469)
                  ·
                    refine ⟨1270098164420942213649551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3386928438455845903065469 1270098164420942213649551)
                    ·
                      rfl

theorem cell22_3710261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_3710261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710261 prefixEnd_3710261 := by exact prefixLift 3710261
  have htrace : WordTrace (prefixWord ++ tailWord_3710261) baseStart_3710261 baseEnd_3710261 := by
    simpa [prefixWord, tailWord_3710261, baseEnd_3710261] using wordTrace_append hprefix tailTrace_3710261
  have hstable : (prefixWord ++ tailWord_3710261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710261).length < 2 ^ (prefixWord ++ tailWord_3710261).sum := by decide
  have hdescent : baseEnd_3710261 < baseStart_3710261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710332 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 3, 4]
def baseStart_3710332 : Nat := 118140960795 + 3710332 * 2 ^ 59
def prefixEnd_3710332 : Nat := 4983230072969 + 3 ^ 40 * 3710332 * 2
def baseEnd_3710332 : Nat := 1270122469171921695124333

theorem tailTrace_3710332 : CollatzResearch.WordTrace tailWord_3710332 prefixEnd_3710332 1270122469171921695124333 := by
  unfold tailWord_3710332
  simp only [CollatzResearch.WordTrace]
  refine ⟨67663462797054156550662625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90217950396072208734216833 67663462797054156550662625)
  ·
    refine ⟨50747597097790617412996969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67663462797054156550662625 50747597097790617412996969)
    ·
      refine ⟨38060697823342963059747727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50747597097790617412996969 38060697823342963059747727)
      ·
        refine ⟨57091046735014444589621591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38060697823342963059747727 57091046735014444589621591)
        ·
          refine ⟨85636570102521666884432387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57091046735014444589621591 85636570102521666884432387)
          ·
            refine ⟨128454855153782500326648581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85636570102521666884432387 128454855153782500326648581)
            ·
              refine ⟨24085285341334218811246609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128454855153782500326648581 24085285341334218811246609)
              ·
                refine ⟨18063964006000664108434957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24085285341334218811246609 18063964006000664108434957)
                ·
                  refine ⟨6773986502250249040663109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18063964006000664108434957 6773986502250249040663109)
                  ·
                    refine ⟨1270122469171921695124333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6773986502250249040663109 1270122469171921695124333)
                    ·
                      rfl

theorem cell22_3710332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_3710332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710332 prefixEnd_3710332 := by exact prefixLift 3710332
  have htrace : WordTrace (prefixWord ++ tailWord_3710332) baseStart_3710332 baseEnd_3710332 := by
    simpa [prefixWord, tailWord_3710332, baseEnd_3710332] using wordTrace_append hprefix tailTrace_3710332
  have hstable : (prefixWord ++ tailWord_3710332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710332).length < 2 ^ (prefixWord ++ tailWord_3710332).sum := by decide
  have hdescent : baseEnd_3710332 < baseStart_3710332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710392 : List Nat := [2, 1, 2, 1, 2, 2, 5, 7]
def baseStart_3710392 : Nat := 118140960795 + 3710392 * 2 ^ 59
def prefixEnd_3710392 : Nat := 4983230072969 + 3 ^ 40 * 3710392 * 2
def baseEnd_3710392 : Nat := 141127000933122393180461

theorem tailTrace_3710392 : CollatzResearch.WordTrace tailWord_3710392 prefixEnd_3710392 141127000933122393180461 := by
  unfold tailWord_3710392
  simp only [CollatzResearch.WordTrace]
  refine ⟨67664556986945471674254715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90219409315927295565672953 67664556986945471674254715)
  ·
    refine ⟨101496835480418207511382073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67664556986945471674254715 101496835480418207511382073)
    ·
      refine ⟨76122626610313655633536555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101496835480418207511382073 76122626610313655633536555)
      ·
        refine ⟨114183939915470483450304833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76122626610313655633536555 114183939915470483450304833)
        ·
          refine ⟨85637954936602862587728625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114183939915470483450304833 85637954936602862587728625)
          ·
            refine ⟨64228466202452146940796469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85637954936602862587728625 64228466202452146940796469)
            ·
              refine ⟨6021418706479888775699669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64228466202452146940796469 6021418706479888775699669)
              ·
                refine ⟨141127000933122393180461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6021418706479888775699669 141127000933122393180461)
                ·
                  rfl

theorem cell22_3710392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 7].length) (baseStart_3710392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710392 prefixEnd_3710392 := by exact prefixLift 3710392
  have htrace : WordTrace (prefixWord ++ tailWord_3710392) baseStart_3710392 baseEnd_3710392 := by
    simpa [prefixWord, tailWord_3710392, baseEnd_3710392] using wordTrace_append hprefix tailTrace_3710392
  have hstable : (prefixWord ++ tailWord_3710392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710392).length < 2 ^ (prefixWord ++ tailWord_3710392).sum := by decide
  have hdescent : baseEnd_3710392 < baseStart_3710392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710396 : List Nat := [2, 2, 2, 4, 2, 1, 2, 1, 1, 5]
def baseStart_3710396 : Nat := 118140960795 + 3710396 * 2 ^ 59
def prefixEnd_3710396 : Nat := 4983230072969 + 3 ^ 40 * 3710396 * 2
def baseEnd_3710396 : Nat := 1270144377679846861524137

theorem tailTrace_3710396 : CollatzResearch.WordTrace tailWord_3710396 prefixEnd_3710396 1270144377679846861524137 := by
  unfold tailWord_3710396
  simp only [CollatzResearch.WordTrace]
  refine ⟨67664629932938226015827521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90219506577250968021103361 67664629932938226015827521)
  ·
    refine ⟨50748472449703669511870641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67664629932938226015827521 50748472449703669511870641)
    ·
      refine ⟨38061354337277752133902981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50748472449703669511870641 38061354337277752133902981)
      ·
        refine ⟨7136503938239578525106809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38061354337277752133902981 7136503938239578525106809)
        ·
          refine ⟨5352377953679683893830107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7136503938239578525106809 5352377953679683893830107)
          ·
            refine ⟨8028566930519525840745161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5352377953679683893830107 8028566930519525840745161)
            ·
              refine ⟨6021425197889644380558871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8028566930519525840745161 6021425197889644380558871)
              ·
                refine ⟨9032137796834466570838307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6021425197889644380558871 9032137796834466570838307)
                ·
                  refine ⟨13548206695251699856257461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9032137796834466570838307 13548206695251699856257461)
                  ·
                    refine ⟨1270144377679846861524137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13548206695251699856257461 1270144377679846861524137)
                    ·
                      rfl

theorem cell22_3710396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_3710396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710396 prefixEnd_3710396 := by exact prefixLift 3710396
  have htrace : WordTrace (prefixWord ++ tailWord_3710396) baseStart_3710396 baseEnd_3710396 := by
    simpa [prefixWord, tailWord_3710396, baseEnd_3710396] using wordTrace_append hprefix tailTrace_3710396
  have hstable : (prefixWord ++ tailWord_3710396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710396).length < 2 ^ (prefixWord ++ tailWord_3710396).sum := by decide
  have hdescent : baseEnd_3710396 < baseStart_3710396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710475 : List Nat := [1, 1, 1, 1, 8, 2, 1, 3, 1, 3]
def baseStart_3710475 : Nat := 118140960795 + 3710475 * 2 ^ 59
def prefixEnd_3710475 : Nat := 4983230072969 + 3 ^ 40 * 3710475 * 2
def baseEnd_3710475 : Nat := 1270171420994316988798895

theorem tailTrace_3710475 : CollatzResearch.WordTrace tailWord_3710475 prefixEnd_3710475 1270171420994316988798895 := by
  unfold tailWord_3710475
  simp only [CollatzResearch.WordTrace]
  refine ⟨135332141232590248523780879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90221427488393499015853919 135332141232590248523780879)
  ·
    refine ⟨202998211848885372785671319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135332141232590248523780879 202998211848885372785671319)
    ·
      refine ⟨304497317773328059178506979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202998211848885372785671319 304497317773328059178506979)
      ·
        refine ⟨456745976659992088767760469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304497317773328059178506979 456745976659992088767760469)
        ·
          refine ⟨5352491913984282290247193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 456745976659992088767760469 5352491913984282290247193)
          ·
            refine ⟨4014368935488211717685395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5352491913984282290247193 4014368935488211717685395)
            ·
              refine ⟨6021553403232317576528093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4014368935488211717685395 6021553403232317576528093)
              ·
                refine ⟨2258082526212119091198035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6021553403232317576528093 2258082526212119091198035)
                ·
                  refine ⟨3387123789318178636797053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2258082526212119091198035 3387123789318178636797053)
                  ·
                    refine ⟨1270171420994316988798895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3387123789318178636797053 1270171420994316988798895)
                    ·
                      rfl

theorem cell22_3710475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 1, 3].length) (baseStart_3710475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710475 prefixEnd_3710475 := by exact prefixLift 3710475
  have htrace : WordTrace (prefixWord ++ tailWord_3710475) baseStart_3710475 baseEnd_3710475 := by
    simpa [prefixWord, tailWord_3710475, baseEnd_3710475] using wordTrace_append hprefix tailTrace_3710475
  have hstable : (prefixWord ++ tailWord_3710475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710475).length < 2 ^ (prefixWord ++ tailWord_3710475).sum := by decide
  have hdescent : baseEnd_3710475 < baseStart_3710475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710514 : List Nat := [3, 2, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_3710514 : Nat := 118140960795 + 3710514 * 2 ^ 59
def prefixEnd_3710514 : Nat := 4983230072969 + 3 ^ 40 * 3710514 * 2
def baseEnd_3710514 : Nat := 1270184771491333887073775

theorem tailTrace_3710514 : CollatzResearch.WordTrace tailWord_3710514 prefixEnd_3710514 1270184771491333887073775 := by
  unfold tailWord_3710514
  simp only [CollatzResearch.WordTrace]
  refine ⟨33833390919862239546112649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90222375786299305456300397 33833390919862239546112649)
  ·
    refine ⟨25375043189896679659584487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33833390919862239546112649 25375043189896679659584487)
    ·
      refine ⟨38062564784845019489376731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25375043189896679659584487 38062564784845019489376731)
      ·
        refine ⟨57093847177267529234065097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38062564784845019489376731 57093847177267529234065097)
        ·
          refine ⟨42820385382950646925548823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57093847177267529234065097 42820385382950646925548823)
          ·
            refine ⟨64230578074425970388323235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42820385382950646925548823 64230578074425970388323235)
            ·
              refine ⟨96345867111638955582484853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64230578074425970388323235 96345867111638955582484853)
              ·
                refine ⟨9032425041716152085857955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96345867111638955582484853 9032425041716152085857955)
                ·
                  refine ⟨13548637562574228128786933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9032425041716152085857955 13548637562574228128786933)
                  ·
                    refine ⟨1270184771491333887073775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13548637562574228128786933 1270184771491333887073775)
                    ·
                      rfl

theorem cell22_3710514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_3710514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710514 prefixEnd_3710514 := by exact prefixLift 3710514
  have htrace : WordTrace (prefixWord ++ tailWord_3710514) baseStart_3710514 baseEnd_3710514 := by
    simpa [prefixWord, tailWord_3710514, baseEnd_3710514] using wordTrace_append hprefix tailTrace_3710514
  have hstable : (prefixWord ++ tailWord_3710514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710514).length < 2 ^ (prefixWord ++ tailWord_3710514).sum := by decide
  have hdescent : baseEnd_3710514 < baseStart_3710514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710518 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_3710518 : Nat := 118140960795 + 3710518 * 2 ^ 59
def prefixEnd_3710518 : Nat := 4983230072969 + 3 ^ 40 * 3710518 * 2
def baseEnd_3710518 : Nat := 1270186140773079209973763

theorem tailTrace_3710518 : CollatzResearch.WordTrace tailWord_3710518 prefixEnd_3710518 1270186140773079209973763 := by
  unfold tailWord_3710518
  simp only [CollatzResearch.WordTrace]
  refine ⟨8458356848214654179224763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90222473047622977911730805 8458356848214654179224763)
  ·
    refine ⟨12687535272321981268837145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8458356848214654179224763 12687535272321981268837145)
    ·
      refine ⟨9515651454241485951627859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12687535272321981268837145 9515651454241485951627859)
      ·
        refine ⟨14273477181362228927441789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9515651454241485951627859 14273477181362228927441789)
        ·
          refine ⟨5352553943010835847790671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14273477181362228927441789 5352553943010835847790671)
          ·
            refine ⟨8028830914516253771686007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5352553943010835847790671 8028830914516253771686007)
            ·
              refine ⟨12043246371774380657529011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8028830914516253771686007 12043246371774380657529011)
              ·
                refine ⟨18064869557661570986293517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12043246371774380657529011 18064869557661570986293517)
                ·
                  refine ⟨6774326084123089119860069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18064869557661570986293517 6774326084123089119860069)
                  ·
                    refine ⟨1270186140773079209973763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6774326084123089119860069 1270186140773079209973763)
                    ·
                      rfl

theorem cell22_3710518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_3710518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710518 prefixEnd_3710518 := by exact prefixLift 3710518
  have htrace : WordTrace (prefixWord ++ tailWord_3710518) baseStart_3710518 baseEnd_3710518 := by
    simpa [prefixWord, tailWord_3710518, baseEnd_3710518] using wordTrace_append hprefix tailTrace_3710518
  have hstable : (prefixWord ++ tailWord_3710518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710518).length < 2 ^ (prefixWord ++ tailWord_3710518).sum := by decide
  have hdescent : baseEnd_3710518 < baseStart_3710518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710546 : List Nat := [3, 2, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_3710546 : Nat := 118140960795 + 3710546 * 2 ^ 59
def prefixEnd_3710546 : Nat := 4983230072969 + 3 ^ 40 * 3710546 * 2
def baseEnd_3710546 : Nat := 1270195725745296470273677

theorem tailTrace_3710546 : CollatzResearch.WordTrace tailWord_3710546 prefixEnd_3710546 1270195725745296470273677 := by
  unfold tailWord_3710546
  simp only [CollatzResearch.WordTrace]
  refine ⟨33833682703833256912403873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90223153876888685099743661 33833682703833256912403873)
  ·
    refine ⟨25375262027874942684302905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33833682703833256912403873 25375262027874942684302905)
    ·
      refine ⟨19031446520906207013227179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25375262027874942684302905 19031446520906207013227179)
      ·
        refine ⟨28547169781359310519840769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19031446520906207013227179 28547169781359310519840769)
        ·
          refine ⟨21410377336019482889880577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28547169781359310519840769 21410377336019482889880577)
          ·
            refine ⟨16057783002014612167410433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21410377336019482889880577 16057783002014612167410433)
            ·
              refine ⟨12043337251510959125557825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16057783002014612167410433 12043337251510959125557825)
              ·
                refine ⟨9032502938633219344168369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12043337251510959125557825 9032502938633219344168369)
                ·
                  refine ⟨6774377203974914508126277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9032502938633219344168369 6774377203974914508126277)
                  ·
                    refine ⟨1270195725745296470273677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6774377203974914508126277 1270195725745296470273677)
                    ·
                      rfl

theorem cell22_3710546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_3710546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710546 prefixEnd_3710546 := by exact prefixLift 3710546
  have htrace : WordTrace (prefixWord ++ tailWord_3710546) baseStart_3710546 baseEnd_3710546 := by
    simpa [prefixWord, tailWord_3710546, baseEnd_3710546] using wordTrace_append hprefix tailTrace_3710546
  have hstable : (prefixWord ++ tailWord_3710546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710546).length < 2 ^ (prefixWord ++ tailWord_3710546).sum := by decide
  have hdescent : baseEnd_3710546 < baseStart_3710546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710548 : List Nat := [2, 4, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_3710548 : Nat := 118140960795 + 3710548 * 2 ^ 59
def prefixEnd_3710548 : Nat := 4983230072969 + 3 ^ 40 * 3710548 * 2
def baseEnd_3710548 : Nat := 1270196410386169131723671

theorem tailTrace_3710548 : CollatzResearch.WordTrace tailWord_3710548 prefixEnd_3710548 1270196410386169131723671 := by
  unfold tailWord_3710548
  simp only [CollatzResearch.WordTrace]
  refine ⟨67667401880662890995594149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90223202507550521327458865 67667401880662890995594149)
  ·
    refine ⟨12687637852624292061673903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67667401880662890995594149 12687637852624292061673903)
    ·
      refine ⟨19031456778936438092510855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12687637852624292061673903 19031456778936438092510855)
      ·
        refine ⟨28547185168404657138766283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19031456778936438092510855 28547185168404657138766283)
        ·
          refine ⟨42820777752606985708149425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28547185168404657138766283 42820777752606985708149425)
          ·
            refine ⟨32115583314455239281112069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42820777752606985708149425 32115583314455239281112069)
            ·
              refine ⟨6021671871460357365208513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32115583314455239281112069 6021671871460357365208513)
              ·
                refine ⟨4516253903595268023906385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6021671871460357365208513 4516253903595268023906385)
                ·
                  refine ⟨3387190427696451017929789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4516253903595268023906385 3387190427696451017929789)
                  ·
                    refine ⟨1270196410386169131723671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3387190427696451017929789 1270196410386169131723671)
                    ·
                      rfl

theorem cell22_3710548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_3710548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710548 prefixEnd_3710548 := by exact prefixLift 3710548
  have htrace : WordTrace (prefixWord ++ tailWord_3710548) baseStart_3710548 baseEnd_3710548 := by
    simpa [prefixWord, tailWord_3710548, baseEnd_3710548] using wordTrace_append hprefix tailTrace_3710548
  have hstable : (prefixWord ++ tailWord_3710548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710548).length < 2 ^ (prefixWord ++ tailWord_3710548).sum := by decide
  have hdescent : baseEnd_3710548 < baseStart_3710548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710576 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 5, 3]
def baseStart_3710576 : Nat := 118140960795 + 3710576 * 2 ^ 59
def prefixEnd_3710576 : Nat := 4983230072969 + 3 ^ 40 * 3710576 * 2
def baseEnd_3710576 : Nat := 1270205995358386392023585

theorem tailTrace_3710576 : CollatzResearch.WordTrace tailWord_3710576 prefixEnd_3710576 1270205995358386392023585 := by
  unfold tailWord_3710576
  simp only [CollatzResearch.WordTrace]
  refine ⟨67667912502612171386603791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90223883336816228515471721 67667912502612171386603791)
  ·
    refine ⟨101501868753918257079905687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67667912502612171386603791 101501868753918257079905687)
    ·
      refine ⟨152252803130877385619858531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101501868753918257079905687 152252803130877385619858531)
      ·
        refine ⟨228379204696316078429787797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152252803130877385619858531 228379204696316078429787797)
        ·
          refine ⟨10705275220139816176396303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 228379204696316078429787797 10705275220139816176396303)
          ·
            refine ⟨16057912830209724264594455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10705275220139816176396303 16057912830209724264594455)
            ·
              refine ⟨24086869245314586396891683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16057912830209724264594455 24086869245314586396891683)
              ·
                refine ⟨36130303867971879595337525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24086869245314586396891683 36130303867971879595337525)
                ·
                  refine ⟨3387215987622363712062893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36130303867971879595337525 3387215987622363712062893)
                  ·
                    refine ⟨1270205995358386392023585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3387215987622363712062893 1270205995358386392023585)
                    ·
                      rfl

theorem cell22_3710576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 5, 3].length) (baseStart_3710576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710576 prefixEnd_3710576 := by exact prefixLift 3710576
  have htrace : WordTrace (prefixWord ++ tailWord_3710576) baseStart_3710576 baseEnd_3710576 := by
    simpa [prefixWord, tailWord_3710576, baseEnd_3710576] using wordTrace_append hprefix tailTrace_3710576
  have hstable : (prefixWord ++ tailWord_3710576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710576).length < 2 ^ (prefixWord ++ tailWord_3710576).sum := by decide
  have hdescent : baseEnd_3710576 < baseStart_3710576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710604 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 4, 5]
def baseStart_3710604 : Nat := 118140960795 + 3710604 * 2 ^ 59
def prefixEnd_3710604 : Nat := 4983230072969 + 3 ^ 40 * 3710604 * 2
def baseEnd_3710604 : Nat := 1270215580330603652323499

theorem tailTrace_3710604 : CollatzResearch.WordTrace tailWord_3710604 prefixEnd_3710604 1270215580330603652323499 := by
  unfold tailWord_3710604
  simp only [CollatzResearch.WordTrace]
  refine ⟨67668423124561451777613433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90224564166081935703484577 67668423124561451777613433)
  ·
    refine ⟨50751317343421088833210075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67668423124561451777613433 50751317343421088833210075)
    ·
      refine ⟨76126976015131633249815113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50751317343421088833210075 76126976015131633249815113)
      ·
        refine ⟨57095232011348724937361335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76126976015131633249815113 57095232011348724937361335)
        ·
          refine ⟨85642848017023087406042003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57095232011348724937361335 85642848017023087406042003)
          ·
            refine ⟨128464272025534631109063005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85642848017023087406042003 128464272025534631109063005)
            ·
              refine ⟨48174102009575486665898627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128464272025534631109063005 48174102009575486665898627)
              ·
                refine ⟨72261153014363229998847941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48174102009575486665898627 72261153014363229998847941)
                ·
                  refine ⟨13548966190193105624783989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72261153014363229998847941 13548966190193105624783989)
                  ·
                    refine ⟨1270215580330603652323499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13548966190193105624783989 1270215580330603652323499)
                    ·
                      rfl

theorem cell22_3710604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_3710604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710604 prefixEnd_3710604 := by exact prefixLift 3710604
  have htrace : WordTrace (prefixWord ++ tailWord_3710604) baseStart_3710604 baseEnd_3710604 := by
    simpa [prefixWord, tailWord_3710604, baseEnd_3710604] using wordTrace_append hprefix tailTrace_3710604
  have hstable : (prefixWord ++ tailWord_3710604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710604).length < 2 ^ (prefixWord ++ tailWord_3710604).sum := by decide
  have hdescent : baseEnd_3710604 < baseStart_3710604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710606 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 7]
def baseStart_3710606 : Nat := 118140960795 + 3710606 * 2 ^ 59
def prefixEnd_3710606 : Nat := 4983230072969 + 3 ^ 40 * 3710606 * 2
def baseEnd_3710606 : Nat := 423405421657158771257831

theorem tailTrace_3710606 : CollatzResearch.WordTrace tailWord_3710606 prefixEnd_3710606 423405421657158771257831 := by
  unfold tailWord_3710606
  simp only [CollatzResearch.WordTrace]
  refine ⟨16917114899389457237099959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90224612796743771931199781 16917114899389457237099959)
  ·
    refine ⟨25375672349084185855649939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16917114899389457237099959 25375672349084185855649939)
    ·
      refine ⟨38063508523626278783474909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25375672349084185855649939 38063508523626278783474909)
      ·
        refine ⟨14273815696359854543803091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38063508523626278783474909 14273815696359854543803091)
        ·
          refine ⟨21410723544539781815704637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14273815696359854543803091 21410723544539781815704637)
          ·
            refine ⟨8029021329202418180889239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21410723544539781815704637 8029021329202418180889239)
            ·
              refine ⟨12043531993803627271333859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8029021329202418180889239 12043531993803627271333859)
              ·
                refine ⟨18065297990705440907000789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12043531993803627271333859 18065297990705440907000789)
                ·
                  refine ⟨423405421657158771257831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18065297990705440907000789 423405421657158771257831)
                  ·
                    rfl

theorem cell22_3710606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_3710606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710606 prefixEnd_3710606 := by exact prefixLift 3710606
  have htrace : WordTrace (prefixWord ++ tailWord_3710606) baseStart_3710606 baseEnd_3710606 := by
    simpa [prefixWord, tailWord_3710606, baseEnd_3710606] using wordTrace_append hprefix tailTrace_3710606
  have hstable : (prefixWord ++ tailWord_3710606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710606).length < 2 ^ (prefixWord ++ tailWord_3710606).sum := by decide
  have hdescent : baseEnd_3710606 < baseStart_3710606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710610 : List Nat := [3, 2, 3, 1, 3, 1, 2, 1, 3, 3]
def baseStart_3710610 : Nat := 118140960795 + 3710610 * 2 ^ 59
def prefixEnd_3710610 : Nat := 4983230072969 + 3 ^ 40 * 3710610 * 2
def baseEnd_3710610 : Nat := 1270217634253221636673481

theorem tailTrace_3710610 : CollatzResearch.WordTrace tailWord_3710610 prefixEnd_3710610 1270217634253221636673481 := by
  unfold tailWord_3710610
  simp only [CollatzResearch.WordTrace]
  refine ⟨33834266271775291644986321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90224710058067444386630189 33834266271775291644986321)
  ·
    refine ⟨25375699703831468733739741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33834266271775291644986321 25375699703831468733739741)
    ·
      refine ⟨9515887388936800775152403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25375699703831468733739741 9515887388936800775152403)
      ·
        refine ⟨14273831083405201162728605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9515887388936800775152403 14273831083405201162728605)
        ·
          refine ⟨5352686656276950436023227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14273831083405201162728605 5352686656276950436023227)
          ·
            refine ⟨8029029984415425654034841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5352686656276950436023227 8029029984415425654034841)
            ·
              refine ⟨6021772488311569240526131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8029029984415425654034841 6021772488311569240526131)
              ·
                refine ⟨9032658732467353860789197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6021772488311569240526131 9032658732467353860789197)
                ·
                  refine ⟨3387247024675257697795949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9032658732467353860789197 3387247024675257697795949)
                  ·
                    refine ⟨1270217634253221636673481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3387247024675257697795949 1270217634253221636673481)
                    ·
                      rfl

theorem cell22_3710610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_3710610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710610 prefixEnd_3710610 := by exact prefixLift 3710610
  have htrace : WordTrace (prefixWord ++ tailWord_3710610) baseStart_3710610 baseEnd_3710610 := by
    simpa [prefixWord, tailWord_3710610, baseEnd_3710610] using wordTrace_append hprefix tailTrace_3710610
  have hstable : (prefixWord ++ tailWord_3710610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710610).length < 2 ^ (prefixWord ++ tailWord_3710610).sum := by decide
  have hdescent : baseEnd_3710610 < baseStart_3710610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710696 : List Nat := [2, 1, 4, 1, 3, 1, 2, 8]
def baseStart_3710696 : Nat := 118140960795 + 3710696 * 2 ^ 59
def prefixEnd_3710696 : Nat := 4983230072969 + 3 ^ 40 * 3710696 * 2
def baseEnd_3710696 : Nat := 141138563756749564335913

theorem tailTrace_3710696 : CollatzResearch.WordTrace tailWord_3710696 prefixEnd_3710696 141138563756749564335913 := by
  unfold tailWord_3710696
  simp only [CollatzResearch.WordTrace]
  refine ⟨67670100882394801633787971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90226801176526402178383961 67670100882394801633787971)
  ·
    refine ⟨101505151323592202450681957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67670100882394801633787971 101505151323592202450681957)
    ·
      refine ⟨19032215873173537959502867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101505151323592202450681957 19032215873173537959502867)
      ·
        refine ⟨28548323809760306939254301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19032215873173537959502867 28548323809760306939254301)
        ·
          refine ⟨10705621428660115102220363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28548323809760306939254301 10705621428660115102220363)
          ·
            refine ⟨16058432142990172653330545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10705621428660115102220363 16058432142990172653330545)
            ·
              refine ⟨12043824107242629489997909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16058432142990172653330545 12043824107242629489997909)
              ·
                refine ⟨141138563756749564335913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12043824107242629489997909 141138563756749564335913)
                ·
                  rfl

theorem cell22_3710696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 8].length) (baseStart_3710696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710696 prefixEnd_3710696 := by exact prefixLift 3710696
  have htrace : WordTrace (prefixWord ++ tailWord_3710696) baseStart_3710696 baseEnd_3710696 := by
    simpa [prefixWord, tailWord_3710696, baseEnd_3710696] using wordTrace_append hprefix tailTrace_3710696
  have hstable : (prefixWord ++ tailWord_3710696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710696).length < 2 ^ (prefixWord ++ tailWord_3710696).sum := by decide
  have hdescent : baseEnd_3710696 < baseStart_3710696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710728 : List Nat := [2, 1, 3, 2, 2, 1, 2, 3, 3, 3]
def baseStart_3710728 : Nat := 118140960795 + 3710728 * 2 ^ 59
def prefixEnd_3710728 : Nat := 4983230072969 + 3 ^ 40 * 3710728 * 2
def baseEnd_3710728 : Nat := 1270258028064708662223119

theorem tailTrace_3710728 : CollatzResearch.WordTrace tailWord_3710728 prefixEnd_3710728 1270258028064708662223119 := by
  unfold tailWord_3710728
  simp only [CollatzResearch.WordTrace]
  refine ⟨67670684450336836366370419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90227579267115781821827225 67670684450336836366370419)
  ·
    refine ⟨101506026675505254549555629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67670684450336836366370419 101506026675505254549555629)
    ·
      refine ⟨38064760003314470456083361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101506026675505254549555629 38064760003314470456083361)
      ·
        refine ⟨28548570002485852842062521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38064760003314470456083361 28548570002485852842062521)
        ·
          refine ⟨21411427501864389631546891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28548570002485852842062521 21411427501864389631546891)
          ·
            refine ⟨32117141252796584447320337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21411427501864389631546891 32117141252796584447320337)
            ·
              refine ⟨24087855939597438335490253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32117141252796584447320337 24087855939597438335490253)
              ·
                refine ⟨9032945977349039375808845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24087855939597438335490253 9032945977349039375808845)
                ·
                  refine ⟨3387354741505889765928317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9032945977349039375808845 3387354741505889765928317)
                  ·
                    refine ⟨1270258028064708662223119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3387354741505889765928317 1270258028064708662223119)
                    ·
                      rfl

theorem cell22_3710728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_3710728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710728 prefixEnd_3710728 := by exact prefixLift 3710728
  have htrace : WordTrace (prefixWord ++ tailWord_3710728) baseStart_3710728 baseEnd_3710728 := by
    simpa [prefixWord, tailWord_3710728, baseEnd_3710728] using wordTrace_append hprefix tailTrace_3710728
  have hstable : (prefixWord ++ tailWord_3710728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710728).length < 2 ^ (prefixWord ++ tailWord_3710728).sum := by decide
  have hdescent : baseEnd_3710728 < baseStart_3710728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710805 : List Nat := [1, 3, 2, 2, 2, 3, 2, 2, 1, 4]
def baseStart_3710805 : Nat := 118140960795 + 3710805 * 2 ^ 59
def prefixEnd_3710805 : Nat := 4983230072969 + 3 ^ 40 * 3710805 * 2
def baseEnd_3710805 : Nat := 1270284386738306128047883

theorem tailTrace_3710805 : CollatzResearch.WordTrace tailWord_3710805 prefixEnd_3710805 1270284386738306128047883 := by
  unfold tailWord_3710805
  simp only [CollatzResearch.WordTrace]
  refine ⟨135344177321394714883293869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90229451547596476588862579 135344177321394714883293869)
  ·
    refine ⟨50754066495523018081235201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135344177321394714883293869 50754066495523018081235201)
    ·
      refine ⟨38065549871642263560926401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50754066495523018081235201 38065549871642263560926401)
      ·
        refine ⟨28549162403731697670694801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38065549871642263560926401 28549162403731697670694801)
        ·
          refine ⟨21411871802798773253021101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28549162403731697670694801 21411871802798773253021101)
          ·
            refine ⟨8029451926049539969882913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21411871802798773253021101 8029451926049539969882913)
            ·
              refine ⟨6022088944537154977412185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8029451926049539969882913 6022088944537154977412185)
              ·
                refine ⟨4516566708402866233059139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6022088944537154977412185 4516566708402866233059139)
                ·
                  refine ⟨6774850062604299349588709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4516566708402866233059139 6774850062604299349588709)
                  ·
                    refine ⟨1270284386738306128047883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6774850062604299349588709 1270284386738306128047883)
                    ·
                      rfl

theorem cell22_3710805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_3710805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710805 prefixEnd_3710805 := by exact prefixLift 3710805
  have htrace : WordTrace (prefixWord ++ tailWord_3710805) baseStart_3710805 baseEnd_3710805 := by
    simpa [prefixWord, tailWord_3710805, baseEnd_3710805] using wordTrace_append hprefix tailTrace_3710805
  have hstable : (prefixWord ++ tailWord_3710805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710805).length < 2 ^ (prefixWord ++ tailWord_3710805).sum := by decide
  have hdescent : baseEnd_3710805 < baseStart_3710805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710833 : List Nat := [1, 2, 2, 2, 1, 3, 3, 2, 2, 4]
def baseStart_3710833 : Nat := 118140960795 + 3710833 * 2 ^ 59
def prefixEnd_3710833 : Nat := 4983230072969 + 3 ^ 40 * 3710833 * 2
def baseEnd_3710833 : Nat := 1270293971710523388347797

theorem tailTrace_3710833 : CollatzResearch.WordTrace tailWord_3710833 prefixEnd_3710833 1270293971710523388347797 := by
  unfold tailWord_3710833
  simp only [CollatzResearch.WordTrace]
  refine ⟨135345198565293275665313153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90230132376862183776875435 135345198565293275665313153)
  ·
    refine ⟨101508898923969956748984865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135345198565293275665313153 101508898923969956748984865)
    ·
      refine ⟨76131674192977467561738649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101508898923969956748984865 76131674192977467561738649)
      ·
        refine ⟨57098755644733100671303987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76131674192977467561738649 57098755644733100671303987)
        ·
          refine ⟨85648133467099651006955981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57098755644733100671303987 85648133467099651006955981)
          ·
            refine ⟨32118050050162369127608493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85648133467099651006955981 32118050050162369127608493)
            ·
              refine ⟨12044268768810888422853185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32118050050162369127608493 12044268768810888422853185)
              ·
                refine ⟨9033201576608166317139889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12044268768810888422853185 9033201576608166317139889)
                ·
                  refine ⟨6774901182456124737854917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9033201576608166317139889 6774901182456124737854917)
                  ·
                    refine ⟨1270293971710523388347797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6774901182456124737854917 1270293971710523388347797)
                    ·
                      rfl

theorem cell22_3710833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_3710833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710833 prefixEnd_3710833 := by exact prefixLift 3710833
  have htrace : WordTrace (prefixWord ++ tailWord_3710833) baseStart_3710833 baseEnd_3710833 := by
    simpa [prefixWord, tailWord_3710833, baseEnd_3710833] using wordTrace_append hprefix tailTrace_3710833
  have hstable : (prefixWord ++ tailWord_3710833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710833).length < 2 ^ (prefixWord ++ tailWord_3710833).sum := by decide
  have hdescent : baseEnd_3710833 < baseStart_3710833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710837 : List Nat := [1, 3, 4, 1, 1, 1, 5, 2, 4]
def baseStart_3710837 : Nat := 118140960795 + 3710837 * 2 ^ 59
def prefixEnd_3710837 : Nat := 4983230072969 + 3 ^ 40 * 3710837 * 2
def baseEnd_3710837 : Nat := 423431780330756237082595

theorem tailTrace_3710837 : CollatzResearch.WordTrace tailWord_3710837 prefixEnd_3710837 423431780330756237082595 := by
  unfold tailWord_3710837
  simp only [CollatzResearch.WordTrace]
  refine ⟨135345344457278784348458765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90230229638185856232305843 135345344457278784348458765)
  ·
    refine ⟨50754504171479544130672037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135345344457278784348458765 50754504171479544130672037)
    ·
      refine ⟨9516469532152414524501007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50754504171479544130672037 9516469532152414524501007)
      ·
        refine ⟨14274704298228621786751511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9516469532152414524501007 14274704298228621786751511)
        ·
          refine ⟨21412056447342932680127267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14274704298228621786751511 21412056447342932680127267)
          ·
            refine ⟨32118084671014399020190901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21412056447342932680127267 32118084671014399020190901)
            ·
              refine ⟨3011070437907599908142897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32118084671014399020190901 3011070437907599908142897)
              ·
                refine ⟨2258302828430699931107173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3011070437907599908142897 2258302828430699931107173)
                ·
                  refine ⟨423431780330756237082595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2258302828430699931107173 423431780330756237082595)
                  ·
                    rfl

theorem cell22_3710837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_3710837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710837 prefixEnd_3710837 := by exact prefixLift 3710837
  have htrace : WordTrace (prefixWord ++ tailWord_3710837) baseStart_3710837 baseEnd_3710837 := by
    simpa [prefixWord, tailWord_3710837, baseEnd_3710837] using wordTrace_append hprefix tailTrace_3710837
  have hstable : (prefixWord ++ tailWord_3710837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710837).length < 2 ^ (prefixWord ++ tailWord_3710837).sum := by decide
  have hdescent : baseEnd_3710837 < baseStart_3710837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710852 : List Nat := [2, 3, 2, 1, 1, 1, 6, 1, 2, 3]
def baseStart_3710852 : Nat := 118140960795 + 3710852 * 2 ^ 59
def prefixEnd_3710852 : Nat := 4983230072969 + 3 ^ 40 * 3710852 * 2
def baseEnd_3710852 : Nat := 1270300475798813672122739

theorem tailTrace_3710852 : CollatzResearch.WordTrace tailWord_3710852 prefixEnd_3710852 1270300475798813672122739 := by
  unfold tailWord_3710852
  simp only [CollatzResearch.WordTrace]
  refine ⟨67672945776112220955127405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90230594368149627940169873 67672945776112220955127405)
  ·
    refine ⟨25377354666042082858172777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67672945776112220955127405 25377354666042082858172777)
    ·
      refine ⟨19033015999531562143629583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25377354666042082858172777 19033015999531562143629583)
      ·
        refine ⟨28549523999297343215444375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19033015999531562143629583 28549523999297343215444375)
        ·
          refine ⟨42824285998946014823166563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28549523999297343215444375 42824285998946014823166563)
          ·
            refine ⟨64236428998419022234749845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42824285998946014823166563 64236428998419022234749845)
            ·
              refine ⟨3011082609300891667253899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64236428998419022234749845 3011082609300891667253899)
              ·
                refine ⟨4516623913951337500880849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3011082609300891667253899 4516623913951337500880849)
                ·
                  refine ⟨3387467935463503125660637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4516623913951337500880849 3387467935463503125660637)
                  ·
                    refine ⟨1270300475798813672122739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3387467935463503125660637 1270300475798813672122739)
                    ·
                      rfl

theorem cell22_3710852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_3710852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710852 prefixEnd_3710852 := by exact prefixLift 3710852
  have htrace : WordTrace (prefixWord ++ tailWord_3710852) baseStart_3710852 baseEnd_3710852 := by
    simpa [prefixWord, tailWord_3710852, baseEnd_3710852] using wordTrace_append hprefix tailTrace_3710852
  have hstable : (prefixWord ++ tailWord_3710852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710852).length < 2 ^ (prefixWord ++ tailWord_3710852).sum := by decide
  have hdescent : baseEnd_3710852 < baseStart_3710852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710888 : List Nat := [2, 1, 6, 2, 2, 1, 2, 2, 4]
def baseStart_3710888 : Nat := 118140960795 + 3710888 * 2 ^ 59
def prefixEnd_3710888 : Nat := 4983230072969 + 3 ^ 40 * 3710888 * 2
def baseEnd_3710888 : Nat := 423437599778173859407543

theorem tailTrace_3710888 : CollatzResearch.WordTrace tailWord_3710888 prefixEnd_3710888 423437599778173859407543 := by
  unfold tailWord_3710888
  simp only [CollatzResearch.WordTrace]
  refine ⟨67673602290047010029282659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90231469720062680039043545 67673602290047010029282659)
  ·
    refine ⟨101510403435070515043923989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67673602290047010029282659 101510403435070515043923989)
    ·
      refine ⟨4758300161018930392683937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101510403435070515043923989 4758300161018930392683937)
      ·
        refine ⟨3568725120764197794512953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4758300161018930392683937 3568725120764197794512953)
        ·
          refine ⟨2676543840573148345884715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3568725120764197794512953 2676543840573148345884715)
          ·
            refine ⟨4014815760859722518827073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2676543840573148345884715 4014815760859722518827073)
            ·
              refine ⟨3011111820644791889120305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4014815760859722518827073 3011111820644791889120305)
              ·
                refine ⟨2258333865483593916840229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3011111820644791889120305 2258333865483593916840229)
                ·
                  refine ⟨423437599778173859407543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2258333865483593916840229 423437599778173859407543)
                  ·
                    rfl

theorem cell22_3710888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 4].length) (baseStart_3710888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710888 prefixEnd_3710888 := by exact prefixLift 3710888
  have htrace : WordTrace (prefixWord ++ tailWord_3710888) baseStart_3710888 baseEnd_3710888 := by
    simpa [prefixWord, tailWord_3710888, baseEnd_3710888] using wordTrace_append hprefix tailTrace_3710888
  have hstable : (prefixWord ++ tailWord_3710888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710888).length < 2 ^ (prefixWord ++ tailWord_3710888).sum := by decide
  have hdescent : baseEnd_3710888 < baseStart_3710888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710910 : List Nat := [4, 2, 1, 1, 1, 3, 2, 3, 5]
def baseStart_3710910 : Nat := 118140960795 + 3710910 * 2 ^ 59
def prefixEnd_3710910 : Nat := 4983230072969 + 3 ^ 40 * 3710910 * 2
def baseEnd_3710910 : Nat := 423440110128040284724187

theorem tailTrace_3710910 : CollatzResearch.WordTrace tailWord_3710910 prefixEnd_3710910 423440110128040284724187 := by
  unfold tailWord_3710910
  simp only [CollatzResearch.WordTrace]
  refine ⟨16918500873251789726983273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90232004657342878543910789 16918500873251789726983273)
  ·
    refine ⟨12688875654938842295237455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16918500873251789726983273 12688875654938842295237455)
    ·
      refine ⟨19033313482408263442856183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12688875654938842295237455 19033313482408263442856183)
      ·
        refine ⟨28549970223612395164284275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19033313482408263442856183 28549970223612395164284275)
        ·
          refine ⟨42824955335418592746426413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28549970223612395164284275 42824955335418592746426413)
          ·
            refine ⟨16059358250781972279909905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42824955335418592746426413 16059358250781972279909905)
            ·
              refine ⟨12044518688086479209932429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16059358250781972279909905 12044518688086479209932429)
              ·
                refine ⟨4516694508032429703724661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12044518688086479209932429 4516694508032429703724661)
                ·
                  refine ⟨423440110128040284724187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4516694508032429703724661 423440110128040284724187)
                  ·
                    rfl

theorem cell22_3710910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_3710910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710910 prefixEnd_3710910 := by exact prefixLift 3710910
  have htrace : WordTrace (prefixWord ++ tailWord_3710910) baseStart_3710910 baseEnd_3710910 := by
    simpa [prefixWord, tailWord_3710910, baseEnd_3710910] using wordTrace_append hprefix tailTrace_3710910
  have hstable : (prefixWord ++ tailWord_3710910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710910).length < 2 ^ (prefixWord ++ tailWord_3710910).sum := by decide
  have hdescent : baseEnd_3710910 < baseStart_3710910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710923 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 3, 4]
def baseStart_3710923 : Nat := 118140960795 + 3710923 * 2 ^ 59
def prefixEnd_3710923 : Nat := 4983230072969 + 3 ^ 40 * 3710923 * 2
def baseEnd_3710923 : Nat := 1270324780549793153597521

theorem tailTrace_3710923 : CollatzResearch.WordTrace tailWord_3710923 prefixEnd_3710923 1270324780549793153597521 := by
  unfold tailWord_3710923
  simp only [CollatzResearch.WordTrace]
  refine ⟨135348481134967221036089423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90232320756644814024059615 135348481134967221036089423)
  ·
    refine ⟨203022721702450831554134135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135348481134967221036089423 203022721702450831554134135)
    ·
      refine ⟨304534082553676247331201203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203022721702450831554134135 304534082553676247331201203)
      ·
        refine ⟨456801123830514370996801805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304534082553676247331201203 456801123830514370996801805)
        ·
          refine ⟨171300421436442889123800677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 456801123830514370996801805 171300421436442889123800677)
          ·
            refine ⟨32118829019333041710712627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171300421436442889123800677 32118829019333041710712627)
            ·
              refine ⟨48178243528999562566068941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32118829019333041710712627 48178243528999562566068941)
              ·
                refine ⟨18066841323374835962275853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48178243528999562566068941 18066841323374835962275853)
                ·
                  refine ⟨6775065496265563485853445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18066841323374835962275853 6775065496265563485853445)
                  ·
                    refine ⟨1270324780549793153597521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6775065496265563485853445 1270324780549793153597521)
                    ·
                      rfl

theorem cell22_3710923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 4].length) (baseStart_3710923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710923 prefixEnd_3710923 := by exact prefixLift 3710923
  have htrace : WordTrace (prefixWord ++ tailWord_3710923) baseStart_3710923 baseEnd_3710923 := by
    simpa [prefixWord, tailWord_3710923, baseEnd_3710923] using wordTrace_append hprefix tailTrace_3710923
  have hstable : (prefixWord ++ tailWord_3710923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710923).length < 2 ^ (prefixWord ++ tailWord_3710923).sum := by decide
  have hdescent : baseEnd_3710923 < baseStart_3710923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710968 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 1, 6]
def baseStart_3710968 : Nat := 118140960795 + 3710968 * 2 ^ 59
def prefixEnd_3710968 : Nat := 4983230072969 + 3 ^ 40 * 3710968 * 2
def baseEnd_3710968 : Nat := 1270340184969428036222383

theorem tailTrace_3710968 : CollatzResearch.WordTrace tailWord_3710968 prefixEnd_3710968 1270340184969428036222383 := by
  unfold tailWord_3710968
  simp only [CollatzResearch.WordTrace]
  refine ⟨67675061209902096860738779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90233414946536129147651705 67675061209902096860738779)
  ·
    refine ⟨101512591814853145291108169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67675061209902096860738779 101512591814853145291108169)
    ·
      refine ⟨76134443861139858968331127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101512591814853145291108169 76134443861139858968331127)
      ·
        refine ⟨114201665791709788452496691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76134443861139858968331127 114201665791709788452496691)
        ·
          refine ⟨171302498687564682678745037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114201665791709788452496691 171302498687564682678745037)
          ·
            refine ⟨64238437007836756004529389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171302498687564682678745037 64238437007836756004529389)
            ·
              refine ⟨24089413877938783501698521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64238437007836756004529389 24089413877938783501698521)
              ·
                refine ⟨18067060408454087626273891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24089413877938783501698521 18067060408454087626273891)
                ·
                  refine ⟨27100590612681131439410837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18067060408454087626273891 27100590612681131439410837)
                  ·
                    refine ⟨1270340184969428036222383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27100590612681131439410837 1270340184969428036222383)
                    ·
                      rfl

theorem cell22_3710968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_3710968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710968 prefixEnd_3710968 := by exact prefixLift 3710968
  have htrace : WordTrace (prefixWord ++ tailWord_3710968) baseStart_3710968 baseEnd_3710968 := by
    simpa [prefixWord, tailWord_3710968, baseEnd_3710968] using wordTrace_append hprefix tailTrace_3710968
  have hstable : (prefixWord ++ tailWord_3710968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710968).length < 2 ^ (prefixWord ++ tailWord_3710968).sum := by decide
  have hdescent : baseEnd_3710968 < baseStart_3710968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710974 : List Nat := [4, 2, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_3710974 : Nat := 118140960795 + 3710974 * 2 ^ 59
def prefixEnd_3710974 : Nat := 4983230072969 + 3 ^ 40 * 3710974 * 2
def baseEnd_3710974 : Nat := 1270342238892046020572365

theorem tailTrace_3710974 : CollatzResearch.WordTrace tailWord_3710974 prefixEnd_3710974 1270342238892046020572365 := by
  unfold tailWord_3710974
  simp only [CollatzResearch.WordTrace]
  refine ⟨16918792657222807093274497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90233560838521637830797317 16918792657222807093274497)
  ·
    refine ⟨12689094492917105319955873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16918792657222807093274497 12689094492917105319955873)
    ·
      refine ⟨9516820869687828989966905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12689094492917105319955873 9516820869687828989966905)
      ·
        refine ⟨7137615652265871742475179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9516820869687828989966905 7137615652265871742475179)
        ·
          refine ⟨10706423478398807613712769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7137615652265871742475179 10706423478398807613712769)
          ·
            refine ⟨8029817608799105710284577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10706423478398807613712769 8029817608799105710284577)
            ·
              refine ⟨6022363206599329282713433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8029817608799105710284577 6022363206599329282713433)
              ·
                refine ⟨4516772404949496962035075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6022363206599329282713433 4516772404949496962035075)
                ·
                  refine ⟨6775158607424245443052613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4516772404949496962035075 6775158607424245443052613)
                  ·
                    refine ⟨1270342238892046020572365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6775158607424245443052613 1270342238892046020572365)
                    ·
                      rfl

theorem cell22_3710974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_3710974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710974 prefixEnd_3710974 := by exact prefixLift 3710974
  have htrace : WordTrace (prefixWord ++ tailWord_3710974) baseStart_3710974 baseEnd_3710974 := by
    simpa [prefixWord, tailWord_3710974, baseEnd_3710974] using wordTrace_append hprefix tailTrace_3710974
  have hstable : (prefixWord ++ tailWord_3710974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710974).length < 2 ^ (prefixWord ++ tailWord_3710974).sum := by decide
  have hdescent : baseEnd_3710974 < baseStart_3710974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710982 : List Nat := [6, 2, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_3710982 : Nat := 118140960795 + 3710982 * 2 ^ 59
def prefixEnd_3710982 : Nat := 4983230072969 + 3 ^ 40 * 3710982 * 2
def baseEnd_3710982 : Nat := 1270344977455536666372341

theorem tailTrace_3710982 : CollatzResearch.WordTrace tailWord_3710982 prefixEnd_3710982 1270344977455536666372341 := by
  unfold tailWord_3710982
  simp only [CollatzResearch.WordTrace]
  refine ⟨4229707282554796066015225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90233755361168982741658133 4229707282554796066015225)
  ·
    refine ⟨3172280461916097049511419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4229707282554796066015225 3172280461916097049511419)
    ·
      refine ⟨4758420692874145574267129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3172280461916097049511419 4758420692874145574267129)
      ·
        refine ⟨3568815519655609180700347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4758420692874145574267129 3568815519655609180700347)
        ·
          refine ⟨5353223279483413771050521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3568815519655609180700347 5353223279483413771050521)
          ·
            refine ⟨4014917459612560328287891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5353223279483413771050521 4014917459612560328287891)
            ·
              refine ⟨6022376189418840492431837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4014917459612560328287891 6022376189418840492431837)
              ·
                refine ⟨2258391071032065184661939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6022376189418840492431837 2258391071032065184661939)
                ·
                  refine ⟨3387586606548097776992909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2258391071032065184661939 3387586606548097776992909)
                  ·
                    refine ⟨1270344977455536666372341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3387586606548097776992909 1270344977455536666372341)
                    ·
                      rfl

theorem cell22_3710982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_3710982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3710982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3710982 prefixEnd_3710982 := by exact prefixLift 3710982
  have htrace : WordTrace (prefixWord ++ tailWord_3710982) baseStart_3710982 baseEnd_3710982 := by
    simpa [prefixWord, tailWord_3710982, baseEnd_3710982] using wordTrace_append hprefix tailTrace_3710982
  have hstable : (prefixWord ++ tailWord_3710982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710982).length < 2 ^ (prefixWord ++ tailWord_3710982).sum := by decide
  have hdescent : baseEnd_3710982 < baseStart_3710982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711043 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 3, 7]
def baseStart_3711043 : Nat := 118140960795 + 3711043 * 2 ^ 59
def prefixEnd_3711043 : Nat := 4983230072969 + 3 ^ 40 * 3711043 * 2
def baseEnd_3711043 : Nat := 1270365859002152840597153

theorem tailTrace_3711043 : CollatzResearch.WordTrace tailWord_3711043 prefixEnd_3711043 1270365859002152840597153 := by
  unfold tailWord_3711043
  simp only [CollatzResearch.WordTrace]
  refine ⟨135352857894532481530457783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90235238596354987686971855 135352857894532481530457783)
  ·
    refine ⟨203029286841798722295686675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135352857894532481530457783 203029286841798722295686675)
    ·
      refine ⟨304543930262698083443530013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203029286841798722295686675 304543930262698083443530013)
      ·
        refine ⟨114203973848511781291323755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304543930262698083443530013 114203973848511781291323755)
        ·
          refine ⟨171305960772767671936985633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114203973848511781291323755 171305960772767671936985633)
          ·
            refine ⟨128479470579575753952739225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171305960772767671936985633 128479470579575753952739225)
            ·
              refine ⟨96359602934681815464554419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128479470579575753952739225 96359602934681815464554419)
              ·
                refine ⟨144539404402022723196831629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96359602934681815464554419 144539404402022723196831629)
                ·
                  refine ⟨54202276650758521198811861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144539404402022723196831629 54202276650758521198811861)
                  ·
                    refine ⟨1270365859002152840597153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54202276650758521198811861 1270365859002152840597153)
                    ·
                      rfl

theorem cell22_3711043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 7].length) (baseStart_3711043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711043 prefixEnd_3711043 := by exact prefixLift 3711043
  have htrace : WordTrace (prefixWord ++ tailWord_3711043) baseStart_3711043 baseEnd_3711043 := by
    simpa [prefixWord, tailWord_3711043, baseEnd_3711043] using wordTrace_append hprefix tailTrace_3711043
  have hstable : (prefixWord ++ tailWord_3711043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711043).length < 2 ^ (prefixWord ++ tailWord_3711043).sum := by decide
  have hdescent : baseEnd_3711043 < baseStart_3711043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711060 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_3711060 : Nat := 118140960795 + 3711060 * 2 ^ 59
def prefixEnd_3711060 : Nat := 4983230072969 + 3 ^ 40 * 3711060 * 2
def baseEnd_3711060 : Nat := 1270371678449570462922101

theorem tailTrace_3711060 : CollatzResearch.WordTrace tailWord_3711060 prefixEnd_3711060 1270371678449570462922101 := by
  unfold tailWord_3711060
  simp only [CollatzResearch.WordTrace]
  refine ⟨67676738967735446716913317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90235651956980595622551089 67676738967735446716913317)
  ·
    refine ⟨12689388556450396259421247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67676738967735446716913317 12689388556450396259421247)
    ·
      refine ⟨19034082834675594389131871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12689388556450396259421247 19034082834675594389131871)
      ·
        refine ⟨28551124252013391583697807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19034082834675594389131871 28551124252013391583697807)
        ·
          refine ⟨42826686378020087375546711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28551124252013391583697807 42826686378020087375546711)
          ·
            refine ⟨64240029567030131063320067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42826686378020087375546711 64240029567030131063320067)
            ·
              refine ⟨96360044350545196594980101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64240029567030131063320067 96360044350545196594980101)
              ·
                refine ⟨18067508315727224361558769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96360044350545196594980101 18067508315727224361558769)
                ·
                  refine ⟨13550631236795418271169077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18067508315727224361558769 13550631236795418271169077)
                  ·
                    refine ⟨1270371678449570462922101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13550631236795418271169077 1270371678449570462922101)
                    ·
                      rfl

theorem cell22_3711060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_3711060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711060 prefixEnd_3711060 := by exact prefixLift 3711060
  have htrace : WordTrace (prefixWord ++ tailWord_3711060) baseStart_3711060 baseEnd_3711060 := by
    simpa [prefixWord, tailWord_3711060, baseEnd_3711060] using wordTrace_append hprefix tailTrace_3711060
  have hstable : (prefixWord ++ tailWord_3711060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711060).length < 2 ^ (prefixWord ++ tailWord_3711060).sum := by decide
  have hdescent : baseEnd_3711060 < baseStart_3711060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711075 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 3, 4]
def baseStart_3711075 : Nat := 118140960795 + 3711075 * 2 ^ 59
def prefixEnd_3711075 : Nat := 4983230072969 + 3 ^ 40 * 3711075 * 2
def baseEnd_3711075 : Nat := 1270376813256115423797055

theorem tailTrace_3711075 : CollatzResearch.WordTrace tailWord_3711075 prefixEnd_3711075 1270376813256115423797055 := by
  unfold tailWord_3711075
  simp only [CollatzResearch.WordTrace]
  refine ⟨135354025030416550995622679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90236016686944367330415119 135354025030416550995622679)
  ·
    refine ⟨203031037545624826493434019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135354025030416550995622679 203031037545624826493434019)
    ·
      refine ⟨304546556318437239740151029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203031037545624826493434019 304546556318437239740151029)
      ·
        refine ⟨28551239654853491225639159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 304546556318437239740151029 28551239654853491225639159)
        ·
          refine ⟨42826859482280236838458739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28551239654853491225639159 42826859482280236838458739)
          ·
            refine ⟨64240289223420355257688109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42826859482280236838458739 64240289223420355257688109)
            ·
              refine ⟨24090108458782633221633041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64240289223420355257688109 24090108458782633221633041)
              ·
                refine ⟨18067581344086974916224781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24090108458782633221633041 18067581344086974916224781)
                ·
                  refine ⟨6775343004032615593584293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18067581344086974916224781 6775343004032615593584293)
                  ·
                    refine ⟨1270376813256115423797055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6775343004032615593584293 1270376813256115423797055)
                    ·
                      rfl

theorem cell22_3711075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 4].length) (baseStart_3711075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711075 prefixEnd_3711075 := by exact prefixLift 3711075
  have htrace : WordTrace (prefixWord ++ tailWord_3711075) baseStart_3711075 baseEnd_3711075 := by
    simpa [prefixWord, tailWord_3711075, baseEnd_3711075] using wordTrace_append hprefix tailTrace_3711075
  have hstable : (prefixWord ++ tailWord_3711075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711075).length < 2 ^ (prefixWord ++ tailWord_3711075).sum := by decide
  have hdescent : baseEnd_3711075 < baseStart_3711075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711090 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 8]
def baseStart_3711090 : Nat := 118140960795 + 3711090 * 2 ^ 59
def prefixEnd_3711090 : Nat := 4983230072969 + 3 ^ 40 * 3711090 * 2
def baseEnd_3711090 : Nat := 423460649354220128224003

theorem tailTrace_3711090 : CollatzResearch.WordTrace tailWord_3711090 prefixEnd_3711090 423460649354220128224003 := by
  unfold tailWord_3711090
  simp only [CollatzResearch.WordTrace]
  refine ⟨33838643031340552139354681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90236381416908139038279149 33838643031340552139354681)
  ·
    refine ⟨25378982273505414104516011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33838643031340552139354681 25378982273505414104516011)
    ·
      refine ⟨38068473410258121156774017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25378982273505414104516011 38068473410258121156774017)
      ·
        refine ⟨28551355057693590867580513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38068473410258121156774017 28551355057693590867580513)
        ·
          refine ⟨21413516293270193150685385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28551355057693590867580513 21413516293270193150685385)
          ·
            refine ⟨16060137219952644863014039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21413516293270193150685385 16060137219952644863014039)
            ·
              refine ⟨24090205829928967294521059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16060137219952644863014039 24090205829928967294521059)
              ·
                refine ⟨36135308744893450941781589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24090205829928967294521059 36135308744893450941781589)
                ·
                  refine ⟨423460649354220128224003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36135308744893450941781589 423460649354220128224003)
                  ·
                    rfl

theorem cell22_3711090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_3711090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711090 prefixEnd_3711090 := by exact prefixLift 3711090
  have htrace : WordTrace (prefixWord ++ tailWord_3711090) baseStart_3711090 baseEnd_3711090 := by
    simpa [prefixWord, tailWord_3711090, baseEnd_3711090] using wordTrace_append hprefix tailTrace_3711090
  have hstable : (prefixWord ++ tailWord_3711090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711090).length < 2 ^ (prefixWord ++ tailWord_3711090).sum := by decide
  have hdescent : baseEnd_3711090 < baseStart_3711090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711107 : List Nat := [1, 1, 1, 3, 3, 3, 1, 5, 4]
def baseStart_3711107 : Nat := 118140960795 + 3711107 * 2 ^ 59
def prefixEnd_3711107 : Nat := 4983230072969 + 3 ^ 40 * 3711107 * 2
def baseEnd_3711107 : Nat := 423462589170026002332319

theorem tailTrace_3711107 : CollatzResearch.WordTrace tailWord_3711107 prefixEnd_3711107 423462589170026002332319 := by
  unfold tailWord_3711107
  simp only [CollatzResearch.WordTrace]
  refine ⟨135355192166300620460787575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90236794777533746973858383 135355192166300620460787575)
  ·
    refine ⟨203032788249450930691181363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135355192166300620460787575 203032788249450930691181363)
    ·
      refine ⟨304549182374176396036772045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203032788249450930691181363 304549182374176396036772045)
      ·
        refine ⟨114205943390316148513789517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304549182374176396036772045 114205943390316148513789517)
        ·
          refine ⟨42827228771368555692671069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114205943390316148513789517 42827228771368555692671069)
          ·
            refine ⟨16060210789263208384751651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42827228771368555692671069 16060210789263208384751651)
            ·
              refine ⟨24090316183894812577127477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16060210789263208384751651 24090316183894812577127477)
              ·
                refine ⟨2258467142240138679105701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24090316183894812577127477 2258467142240138679105701)
                ·
                  refine ⟨423462589170026002332319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2258467142240138679105701 423462589170026002332319)
                  ·
                    rfl

theorem cell22_3711107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 4].length) (baseStart_3711107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711107 prefixEnd_3711107 := by exact prefixLift 3711107
  have htrace : WordTrace (prefixWord ++ tailWord_3711107) baseStart_3711107 baseEnd_3711107 := by
    simpa [prefixWord, tailWord_3711107, baseEnd_3711107] using wordTrace_append hprefix tailTrace_3711107
  have hstable : (prefixWord ++ tailWord_3711107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711107).length < 2 ^ (prefixWord ++ tailWord_3711107).sum := by decide
  have hdescent : baseEnd_3711107 < baseStart_3711107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711109 : List Nat := [1, 3, 1, 1, 5, 1, 4, 1, 1, 4]
def baseStart_3711109 : Nat := 118140960795 + 3711109 * 2 ^ 59
def prefixEnd_3711109 : Nat := 4983230072969 + 3 ^ 40 * 3711109 * 2
def baseEnd_3711109 : Nat := 1270388452150950668446951

theorem tailTrace_3711109 : CollatzResearch.WordTrace tailWord_3711109 prefixEnd_3711109 1270388452150950668446951 := by
  unfold tailWord_3711109
  simp only [CollatzResearch.WordTrace]
  refine ⟨135355265112293374802360381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90236843408195583201573587 135355265112293374802360381)
  ·
    refine ⟨50758224417110015550885143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135355265112293374802360381 50758224417110015550885143)
    ·
      refine ⟨76137336625665023326327715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50758224417110015550885143 76137336625665023326327715)
      ·
        refine ⟨114206004938497534989491573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76137336625665023326327715 114206004938497534989491573)
        ·
          refine ⟨10706812962984143905264835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114206004938497534989491573 10706812962984143905264835)
          ·
            refine ⟨16060219444476215857897253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10706812962984143905264835 16060219444476215857897253)
            ·
              refine ⟨3011291145839290473355735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16060219444476215857897253 3011291145839290473355735)
              ·
                refine ⟨4516936718758935710033603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3011291145839290473355735 4516936718758935710033603)
                ·
                  refine ⟨6775405078138403565050405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4516936718758935710033603 6775405078138403565050405)
                  ·
                    refine ⟨1270388452150950668446951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6775405078138403565050405 1270388452150950668446951)
                    ·
                      rfl

theorem cell22_3711109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 1, 4].length) (baseStart_3711109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711109 prefixEnd_3711109 := by exact prefixLift 3711109
  have htrace : WordTrace (prefixWord ++ tailWord_3711109) baseStart_3711109 baseEnd_3711109 := by
    simpa [prefixWord, tailWord_3711109, baseEnd_3711109] using wordTrace_append hprefix tailTrace_3711109
  have hstable : (prefixWord ++ tailWord_3711109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711109).length < 2 ^ (prefixWord ++ tailWord_3711109).sum := by decide
  have hdescent : baseEnd_3711109 < baseStart_3711109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711120 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 4, 4]
def baseStart_3711120 : Nat := 118140960795 + 3711120 * 2 ^ 59
def prefixEnd_3711120 : Nat := 4983230072969 + 3 ^ 40 * 3711120 * 2
def baseEnd_3711120 : Nat := 1270392217675750306421917

theorem tailTrace_3711120 : CollatzResearch.WordTrace tailWord_3711120 prefixEnd_3711120 1270392217675750306421917 := by
  unfold tailWord_3711120
  simp only [CollatzResearch.WordTrace]
  refine ⟨67677833157626761840505407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90237110876835682454007209 67677833157626761840505407)
  ·
    refine ⟨101516749736440142760758111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67677833157626761840505407 101516749736440142760758111)
    ·
      refine ⟨152275124604660214141137167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101516749736440142760758111 152275124604660214141137167)
      ·
        refine ⟨228412686906990321211705751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152275124604660214141137167 228412686906990321211705751)
        ·
          refine ⟨342619030360485481817558627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228412686906990321211705751 342619030360485481817558627)
          ·
            refine ⟨513928545540728222726337941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342619030360485481817558627 513928545540728222726337941)
            ·
              refine ⟨24090400572221635440297091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 513928545540728222726337941 24090400572221635440297091)
              ·
                refine ⟨36135600858332453160445637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24090400572221635440297091 36135600858332453160445637)
                ·
                  refine ⟨6775425160937334967583557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36135600858332453160445637 6775425160937334967583557)
                  ·
                    refine ⟨1270392217675750306421917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6775425160937334967583557 1270392217675750306421917)
                    ·
                      rfl

theorem cell22_3711120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_3711120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711120 prefixEnd_3711120 := by exact prefixLift 3711120
  have htrace : WordTrace (prefixWord ++ tailWord_3711120) baseStart_3711120 baseEnd_3711120 := by
    simpa [prefixWord, tailWord_3711120, baseEnd_3711120] using wordTrace_append hprefix tailTrace_3711120
  have hstable : (prefixWord ++ tailWord_3711120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711120).length < 2 ^ (prefixWord ++ tailWord_3711120).sum := by decide
  have hdescent : baseEnd_3711120 < baseStart_3711120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711165 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_3711165 : Nat := 118140960795 + 3711165 * 2 ^ 59
def prefixEnd_3711165 : Nat := 4983230072969 + 3 ^ 40 * 3711165 * 2
def baseEnd_3711165 : Nat := 1270407622095385189046779

theorem tailTrace_3711165 : CollatzResearch.WordTrace tailWord_3711165 prefixEnd_3711165 1270407622095385189046779 := by
  unfold tailWord_3711165
  simp only [CollatzResearch.WordTrace]
  refine ⟨135357307600090496366398949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90238205066726997577599299 135357307600090496366398949)
  ·
    refine ⟨25379495175016968068699803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135357307600090496366398949 25379495175016968068699803)
    ·
      refine ⟨38069242762525452103049705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25379495175016968068699803 38069242762525452103049705)
      ·
        refine ⟨28551932071894089077287279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38069242762525452103049705 28551932071894089077287279)
        ·
          refine ⟨42827898107841133615930919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28551932071894089077287279 42827898107841133615930919)
          ·
            refine ⟨64241847161761700423896379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42827898107841133615930919 64241847161761700423896379)
            ·
              refine ⟨96362770742642550635844569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64241847161761700423896379 96362770742642550635844569)
              ·
                refine ⟨72272078056981912976883427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96362770742642550635844569 72272078056981912976883427)
                ·
                  refine ⟨108408117085472869465325141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72272078056981912976883427 108408117085472869465325141)
                  ·
                    refine ⟨1270407622095385189046779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108408117085472869465325141 1270407622095385189046779)
                    ·
                      rfl

theorem cell22_3711165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_3711165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711165 prefixEnd_3711165 := by exact prefixLift 3711165
  have htrace : WordTrace (prefixWord ++ tailWord_3711165) baseStart_3711165 baseEnd_3711165 := by
    simpa [prefixWord, tailWord_3711165, baseEnd_3711165] using wordTrace_append hprefix tailTrace_3711165
  have hstable : (prefixWord ++ tailWord_3711165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711165).length < 2 ^ (prefixWord ++ tailWord_3711165).sum := by decide
  have hdescent : baseEnd_3711165 < baseStart_3711165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711169 : List Nat := [1, 2, 6, 1, 2, 2, 8]
def baseStart_3711169 : Nat := 118140960795 + 3711169 * 2 ^ 59
def prefixEnd_3711169 : Nat := 4983230072969 + 3 ^ 40 * 3711169 * 2
def baseEnd_3711169 : Nat := 47052184865819648590621

theorem tailTrace_3711169 : CollatzResearch.WordTrace tailWord_3711169 prefixEnd_3711169 47052184865819648590621 := by
  unfold tailWord_3711169
  simp only [CollatzResearch.WordTrace]
  refine ⟨135357453492076005049544561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90238302328050670033029707 135357453492076005049544561)
  ·
    refine ⟨101518090119057003787158421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135357453492076005049544561 101518090119057003787158421)
    ·
      refine ⟨4758660474330797052523051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101518090119057003787158421 4758660474330797052523051)
      ·
        refine ⟨7137990711496195578784577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4758660474330797052523051 7137990711496195578784577)
        ·
          refine ⟨5353493033622146684088433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7137990711496195578784577 5353493033622146684088433)
          ·
            refine ⟨4015119775216610013066325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5353493033622146684088433 4015119775216610013066325)
            ·
              refine ⟨47052184865819648590621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4015119775216610013066325 47052184865819648590621)
              ·
                rfl

theorem cell22_3711169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 8].length) (baseStart_3711169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711169 prefixEnd_3711169 := by exact prefixLift 3711169
  have htrace : WordTrace (prefixWord ++ tailWord_3711169) baseStart_3711169 baseEnd_3711169 := by
    simpa [prefixWord, tailWord_3711169, baseEnd_3711169] using wordTrace_append hprefix tailTrace_3711169
  have hstable : (prefixWord ++ tailWord_3711169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711169).length < 2 ^ (prefixWord ++ tailWord_3711169).sum := by decide
  have hdescent : baseEnd_3711169 < baseStart_3711169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711190 : List Nat := [5, 2, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_3711190 : Nat := 118140960795 + 3711190 * 2 ^ 59
def prefixEnd_3711190 : Nat := 4983230072969 + 3 ^ 40 * 3711190 * 2
def baseEnd_3711190 : Nat := 1270416180106293457171703

theorem tailTrace_3711190 : CollatzResearch.WordTrace tailWord_3711190 prefixEnd_3711190 1270416180106293457171703 := by
  unfold tailWord_3711190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8459888714062495352253689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90238812949999950424039349 8459888714062495352253689)
  ·
    refine ⟨6344916535546871514190267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8459888714062495352253689 6344916535546871514190267)
    ·
      refine ⟨9517374803320307271285401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6344916535546871514190267 9517374803320307271285401)
      ·
        refine ⟨7138031102490230453464051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9517374803320307271285401 7138031102490230453464051)
        ·
          refine ⟨10707046653735345680196077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7138031102490230453464051 10707046653735345680196077)
          ·
            refine ⟨4015142495150754630073529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10707046653735345680196077 4015142495150754630073529)
            ·
              refine ⟨3011356871363065972555147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4015142495150754630073529 3011356871363065972555147)
              ·
                refine ⟨4517035307044598958832721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3011356871363065972555147 4517035307044598958832721)
                ·
                  refine ⟨3387776480283449219124541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4517035307044598958832721 3387776480283449219124541)
                  ·
                    refine ⟨1270416180106293457171703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3387776480283449219124541 1270416180106293457171703)
                    ·
                      rfl

theorem cell22_3711190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_3711190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711190 prefixEnd_3711190 := by exact prefixLift 3711190
  have htrace : WordTrace (prefixWord ++ tailWord_3711190) baseStart_3711190 baseEnd_3711190 := by
    simpa [prefixWord, tailWord_3711190, baseEnd_3711190] using wordTrace_append hprefix tailTrace_3711190
  have hstable : (prefixWord ++ tailWord_3711190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711190).length < 2 ^ (prefixWord ++ tailWord_3711190).sum := by decide
  have hdescent : baseEnd_3711190 < baseStart_3711190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711225 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 10]
def baseStart_3711225 : Nat := 118140960795 + 3711225 * 2 ^ 59
def prefixEnd_3711225 : Nat := 4983230072969 + 3 ^ 40 * 3711225 * 2
def baseEnd_3711225 : Nat := 423476053773855010848865

theorem tailTrace_3711225 : CollatzResearch.WordTrace tailWord_3711225 prefixEnd_3711225 423476053773855010848865 := by
  unfold tailWord_3711225
  simp only [CollatzResearch.WordTrace]
  refine ⟨135359495979873126613583129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90239663986582084409055419 135359495979873126613583129)
  ·
    refine ⟨101519621984904844960187347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135359495979873126613583129 101519621984904844960187347)
    ·
      refine ⟨152279432977357267440281021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101519621984904844960187347 152279432977357267440281021)
      ·
        refine ⟨57104787366508975290105383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152279432977357267440281021 57104787366508975290105383)
        ·
          refine ⟨85657181049763462935158075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57104787366508975290105383 85657181049763462935158075)
          ·
            refine ⟨128485771574645194402737113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85657181049763462935158075 128485771574645194402737113)
            ·
              refine ⟨96364328680983895802052835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128485771574645194402737113 96364328680983895802052835)
              ·
                refine ⟨144546493021475843703079253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96364328680983895802052835 144546493021475843703079253)
                ·
                  refine ⟨423476053773855010848865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 144546493021475843703079253 423476053773855010848865)
                  ·
                    rfl

theorem cell22_3711225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 10].length) (baseStart_3711225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711225 prefixEnd_3711225 := by exact prefixLift 3711225
  have htrace : WordTrace (prefixWord ++ tailWord_3711225) baseStart_3711225 baseEnd_3711225 := by
    simpa [prefixWord, tailWord_3711225, baseEnd_3711225] using wordTrace_append hprefix tailTrace_3711225
  have hstable : (prefixWord ++ tailWord_3711225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711225).length < 2 ^ (prefixWord ++ tailWord_3711225).sum := by decide
  have hdescent : baseEnd_3711225 < baseStart_3711225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711278 : List Nat := [4, 1, 3, 3, 1, 1, 1, 3, 1, 4]
def baseStart_3711278 : Nat := 118140960795 + 3711278 * 2 ^ 59
def prefixEnd_3711278 : Nat := 4983230072969 + 3 ^ 40 * 3711278 * 2
def baseEnd_3711278 : Nat := 1270446304304690560971433

theorem tailTrace_3711278 : CollatzResearch.WordTrace tailWord_3711278 prefixEnd_3711278 1270446304304690560971433 := by
  unfold tailWord_3711278
  simp only [CollatzResearch.WordTrace]
  refine ⟨16920178631085139583157811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90240952699120744443508325 16920178631085139583157811)
  ·
    refine ⟨25380267946627709374736717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16920178631085139583157811 25380267946627709374736717)
    ·
      refine ⟨9517600479985391015526269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25380267946627709374736717 9517600479985391015526269)
      ·
        refine ⟨3569100179994521630822351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9517600479985391015526269 3569100179994521630822351)
        ·
          refine ⟨5353650269991782446233527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3569100179994521630822351 5353650269991782446233527)
          ·
            refine ⟨8030475404987673669350291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5353650269991782446233527 8030475404987673669350291)
            ·
              refine ⟨12045713107481510504025437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8030475404987673669350291 12045713107481510504025437)
              ·
                refine ⟨4517142415305566439009539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12045713107481510504025437 4517142415305566439009539)
                ·
                  refine ⟨6775713622958349658514309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4517142415305566439009539 6775713622958349658514309)
                  ·
                    refine ⟨1270446304304690560971433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6775713622958349658514309 1270446304304690560971433)
                    ·
                      rfl

theorem cell22_3711278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_3711278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711278 prefixEnd_3711278 := by exact prefixLift 3711278
  have htrace : WordTrace (prefixWord ++ tailWord_3711278) baseStart_3711278 baseEnd_3711278 := by
    simpa [prefixWord, tailWord_3711278, baseEnd_3711278] using wordTrace_append hprefix tailTrace_3711278
  have hstable : (prefixWord ++ tailWord_3711278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711278).length < 2 ^ (prefixWord ++ tailWord_3711278).sum := by decide
  have hdescent : baseEnd_3711278 < baseStart_3711278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711319 : List Nat := [1, 1, 3, 2, 3, 1, 1, 4, 3, 3]
def baseStart_3711319 : Nat := 118140960795 + 3711319 * 2 ^ 59
def prefixEnd_3711319 : Nat := 4983230072969 + 3 ^ 40 * 3711319 * 2
def baseEnd_3711319 : Nat := 1270460339442580120696307

theorem tailTrace_3711319 : CollatzResearch.WordTrace tailWord_3711319 prefixEnd_3711319 1270460339442580120696307 := by
  unfold tailWord_3711319
  simp only [CollatzResearch.WordTrace]
  refine ⟨135362924441532580667505011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90241949627688387111670007 135362924441532580667505011)
  ·
    refine ⟨203044386662298871001257517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135362924441532580667505011 203044386662298871001257517)
    ·
      refine ⟨76141644998362076625471569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203044386662298871001257517 76141644998362076625471569)
      ·
        refine ⟨57106233748771557469103677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76141644998362076625471569 57106233748771557469103677)
        ·
          refine ⟨21414837655789334050913879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57106233748771557469103677 21414837655789334050913879)
          ·
            refine ⟨32122256483684001076370819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21414837655789334050913879 32122256483684001076370819)
            ·
              refine ⟨48183384725526001614556229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32122256483684001076370819 48183384725526001614556229)
              ·
                refine ⟨9034384636036125302729293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48183384725526001614556229 9034384636036125302729293)
                ·
                  refine ⟨3387894238513546988523485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9034384636036125302729293 3387894238513546988523485)
                  ·
                    refine ⟨1270460339442580120696307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3387894238513546988523485 1270460339442580120696307)
                    ·
                      rfl

theorem cell22_3711319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_3711319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711319 prefixEnd_3711319 := by exact prefixLift 3711319
  have htrace : WordTrace (prefixWord ++ tailWord_3711319) baseStart_3711319 baseEnd_3711319 := by
    simpa [prefixWord, tailWord_3711319, baseEnd_3711319] using wordTrace_append hprefix tailTrace_3711319
  have hstable : (prefixWord ++ tailWord_3711319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711319).length < 2 ^ (prefixWord ++ tailWord_3711319).sum := by decide
  have hdescent : baseEnd_3711319 < baseStart_3711319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711332 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 9]
def baseStart_3711332 : Nat := 118140960795 + 3711332 * 2 ^ 59
def prefixEnd_3711332 : Nat := 4983230072969 + 3 ^ 40 * 3711332 * 2
def baseEnd_3711332 : Nat := 423488263202750806707089

theorem tailTrace_3711332 : CollatzResearch.WordTrace tailWord_3711332 prefixEnd_3711332 423488263202750806707089 := by
  unfold tailWord_3711332
  simp only [CollatzResearch.WordTrace]
  refine ⟨67681699295242741943864125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90242265726990322591818833 67681699295242741943864125)
  ·
    refine ⟨25380637235716028228949047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67681699295242741943864125 25380637235716028228949047)
    ·
      refine ⟨38070955853574042343423571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25380637235716028228949047 38070955853574042343423571)
      ·
        refine ⟨57106433780361063515135357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38070955853574042343423571 57106433780361063515135357)
        ·
          refine ⟨21414912667635398818175759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57106433780361063515135357 21414912667635398818175759)
          ·
            refine ⟨32122369001453098227263639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21414912667635398818175759 32122369001453098227263639)
            ·
              refine ⟨48183553502179647340895459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32122369001453098227263639 48183553502179647340895459)
              ·
                refine ⟨72275330253269471011343189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48183553502179647340895459 72275330253269471011343189)
                ·
                  refine ⟨423488263202750806707089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72275330253269471011343189 423488263202750806707089)
                  ·
                    rfl

theorem cell22_3711332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_3711332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711332 prefixEnd_3711332 := by exact prefixLift 3711332
  have htrace : WordTrace (prefixWord ++ tailWord_3711332) baseStart_3711332 baseEnd_3711332 := by
    simpa [prefixWord, tailWord_3711332, baseEnd_3711332] using wordTrace_append hprefix tailTrace_3711332
  have hstable : (prefixWord ++ tailWord_3711332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711332).length < 2 ^ (prefixWord ++ tailWord_3711332).sum := by decide
  have hdescent : baseEnd_3711332 < baseStart_3711332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711349 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 7]
def baseStart_3711349 : Nat := 118140960795 + 3711349 * 2 ^ 59
def prefixEnd_3711349 : Nat := 4983230072969 + 3 ^ 40 * 3711349 * 2
def baseEnd_3711349 : Nat := 423490203018556680815405

theorem tailTrace_3711349 : CollatzResearch.WordTrace tailWord_3711349 prefixEnd_3711349 423490203018556680815405 := by
  unfold tailWord_3711349
  simp only [CollatzResearch.WordTrace]
  refine ⟨135364018631423895791097101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90242679087615930527398067 135364018631423895791097101)
  ·
    refine ⟨50761506986783960921661413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135364018631423895791097101 50761506986783960921661413)
    ·
      refine ⟨9517782560021992672811515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50761506986783960921661413 9517782560021992672811515)
      ·
        refine ⟨14276673840032989009217273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9517782560021992672811515 14276673840032989009217273)
        ·
          refine ⟨10707505380024741756912955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14276673840032989009217273 10707505380024741756912955)
          ·
            refine ⟨16061258070037112635369433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10707505380024741756912955 16061258070037112635369433)
            ·
              refine ⟨12045943552527834476527075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16061258070037112635369433 12045943552527834476527075)
              ·
                refine ⟨18068915328791751714790613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12045943552527834476527075 18068915328791751714790613)
                ·
                  refine ⟨423490203018556680815405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18068915328791751714790613 423490203018556680815405)
                  ·
                    rfl

theorem cell22_3711349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_3711349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711349 prefixEnd_3711349 := by exact prefixLift 3711349
  have htrace : WordTrace (prefixWord ++ tailWord_3711349) baseStart_3711349 baseEnd_3711349 := by
    simpa [prefixWord, tailWord_3711349, baseEnd_3711349] using wordTrace_append hprefix tailTrace_3711349
  have hstable : (prefixWord ++ tailWord_3711349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711349).length < 2 ^ (prefixWord ++ tailWord_3711349).sum := by decide
  have hdescent : baseEnd_3711349 < baseStart_3711349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711407 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 5, 6]
def baseStart_3711407 : Nat := 118140960795 + 3711407 * 2 ^ 59
def prefixEnd_3711407 : Nat := 4983230072969 + 3 ^ 40 * 3711407 * 2
def baseEnd_3711407 : Nat := 1270490463640977224496037

theorem tailTrace_3711407 : CollatzResearch.WordTrace tailWord_3711407 prefixEnd_3711407 1270490463640977224496037 := by
  unfold tailWord_3711407
  simp only [CollatzResearch.WordTrace]
  refine ⟨135366134065213771696708475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90244089376809181131138983 135366134065213771696708475)
  ·
    refine ⟨203049201097820657545062713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135366134065213771696708475 203049201097820657545062713)
    ·
      refine ⟨152286900823365493158797035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203049201097820657545062713 152286900823365493158797035)
      ·
        refine ⟨228430351235048239738195553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152286900823365493158797035 228430351235048239738195553)
        ·
          refine ⟨171322763426286179803646665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228430351235048239738195553 171322763426286179803646665)
          ·
            refine ⟨128492072569714634852734999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171322763426286179803646665 128492072569714634852734999)
            ·
              refine ⟨192738108854571952279102499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128492072569714634852734999 192738108854571952279102499)
              ·
                refine ⟨289107163281857928418653749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192738108854571952279102499 289107163281857928418653749)
                ·
                  refine ⟨27103796557674180789248789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 289107163281857928418653749 27103796557674180789248789)
                  ·
                    refine ⟨1270490463640977224496037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27103796557674180789248789 1270490463640977224496037)
                    ·
                      rfl

theorem cell22_3711407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_3711407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711407 prefixEnd_3711407 := by exact prefixLift 3711407
  have htrace : WordTrace (prefixWord ++ tailWord_3711407) baseStart_3711407 baseEnd_3711407 := by
    simpa [prefixWord, tailWord_3711407, baseEnd_3711407] using wordTrace_append hprefix tailTrace_3711407
  have hstable : (prefixWord ++ tailWord_3711407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711407).length < 2 ^ (prefixWord ++ tailWord_3711407).sum := by decide
  have hdescent : baseEnd_3711407 < baseStart_3711407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711477 : List Nat := [1, 3, 5, 1, 2, 1, 3, 1, 2, 3]
def baseStart_3711477 : Nat := 118140960795 + 3711477 * 2 ^ 59
def prefixEnd_3711477 : Nat := 4983230072969 + 3 ^ 40 * 3711477 * 2
def baseEnd_3711477 : Nat := 1270514426071520375245823

theorem tailTrace_3711477 : CollatzResearch.WordTrace tailWord_3711477 prefixEnd_3711477 1270514426071520375245823 := by
  unfold tailWord_3711477
  simp only [CollatzResearch.WordTrace]
  refine ⟨135368687174960173651756685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90245791449973449101171123 135368687174960173651756685)
  ·
    refine ⟨50763257690610065119408757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135368687174960173651756685 50763257690610065119408757)
    ·
      refine ⟨4759055408494693604944571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50763257690610065119408757 4759055408494693604944571)
      ·
        refine ⟨7138583112742040407416857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4759055408494693604944571 7138583112742040407416857)
        ·
          refine ⟨5353937334556530305562643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7138583112742040407416857 5353937334556530305562643)
          ·
            refine ⟨8030906001834795458343965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5353937334556530305562643 8030906001834795458343965)
            ·
              refine ⟨3011589750688048296878987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8030906001834795458343965 3011589750688048296878987)
              ·
                refine ⟨4517384626032072445318481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3011589750688048296878987 4517384626032072445318481)
                ·
                  refine ⟨3388038469524054333988861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4517384626032072445318481 3388038469524054333988861)
                  ·
                    refine ⟨1270514426071520375245823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3388038469524054333988861 1270514426071520375245823)
                    ·
                      rfl

theorem cell22_3711477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_3711477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711477 prefixEnd_3711477 := by exact prefixLift 3711477
  have htrace : WordTrace (prefixWord ++ tailWord_3711477) baseStart_3711477 baseEnd_3711477 := by
    simpa [prefixWord, tailWord_3711477, baseEnd_3711477] using wordTrace_append hprefix tailTrace_3711477
  have hstable : (prefixWord ++ tailWord_3711477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711477).length < 2 ^ (prefixWord ++ tailWord_3711477).sum := by decide
  have hdescent : baseEnd_3711477 < baseStart_3711477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711490 : List Nat := [3, 4, 1, 2, 2, 2, 2, 6]
def baseStart_3711490 : Nat := 118140960795 + 3711490 * 2 ^ 59
def prefixEnd_3711490 : Nat := 4983230072969 + 3 ^ 40 * 3711490 * 2
def baseEnd_3711490 : Nat := 141168764026354741630087

theorem tailTrace_3711490 : CollatzResearch.WordTrace tailWord_3711490 prefixEnd_3711490 141168764026354741630087 := by
  unfold tailWord_3711490
  simp only [CollatzResearch.WordTrace]
  refine ⟨33842290330978269217994981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90246107549275384581319949 33842290330978269217994981)
  ·
    refine ⟨6345429437058425478374059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33842290330978269217994981 6345429437058425478374059)
    ·
      refine ⟨9518144155587638217561089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6345429437058425478374059 9518144155587638217561089)
      ·
        refine ⟨7138608116690728663170817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9518144155587638217561089 7138608116690728663170817)
        ·
          refine ⟨5353956087518046497378113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7138608116690728663170817 5353956087518046497378113)
          ·
            refine ⟨4015467065638534873033585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5353956087518046497378113 4015467065638534873033585)
            ·
              refine ⟨3011600299228901154775189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4015467065638534873033585 3011600299228901154775189)
              ·
                refine ⟨141168764026354741630087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3011600299228901154775189 141168764026354741630087)
                ·
                  rfl

theorem cell22_3711490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 6].length) (baseStart_3711490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711490 prefixEnd_3711490 := by exact prefixLift 3711490
  have htrace : WordTrace (prefixWord ++ tailWord_3711490) baseStart_3711490 baseEnd_3711490 := by
    simpa [prefixWord, tailWord_3711490, baseEnd_3711490] using wordTrace_append hprefix tailTrace_3711490
  have hstable : (prefixWord ++ tailWord_3711490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711490).length < 2 ^ (prefixWord ++ tailWord_3711490).sum := by decide
  have hdescent : baseEnd_3711490 < baseStart_3711490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711548 : List Nat := [2, 2, 2, 2, 3, 1, 3, 2, 1, 4]
def baseStart_3711548 : Nat := 118140960795 + 3711548 * 2 ^ 59
def prefixEnd_3711548 : Nat := 4983230072969 + 3 ^ 40 * 3711548 * 2
def baseEnd_3711548 : Nat := 1270538730822499856720605

theorem tailTrace_3711548 : CollatzResearch.WordTrace tailWord_3711548 prefixEnd_3711548 1270538730822499856720605 := by
  unfold tailWord_3711548
  simp only [CollatzResearch.WordTrace]
  refine ⟨67685638378851476388795649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90247517838468635185060865 67685638378851476388795649)
  ·
    refine ⟨50764228784138607291596737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67685638378851476388795649 50764228784138607291596737)
    ·
      refine ⟨38073171588103955468697553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50764228784138607291596737 38073171588103955468697553)
      ·
        refine ⟨28554878691077966601523165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38073171588103955468697553 28554878691077966601523165)
        ·
          refine ⟨10708079509154237475571187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28554878691077966601523165 10708079509154237475571187)
          ·
            refine ⟨16062119263731356213356781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10708079509154237475571187 16062119263731356213356781)
            ·
              refine ⟨6023294723899258580008793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16062119263731356213356781 6023294723899258580008793)
              ·
                refine ⟨4517471042924443935006595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6023294723899258580008793 4517471042924443935006595)
                ·
                  refine ⟨6776206564386665902509893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4517471042924443935006595 6776206564386665902509893)
                  ·
                    refine ⟨1270538730822499856720605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6776206564386665902509893 1270538730822499856720605)
                    ·
                      rfl

theorem cell22_3711548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_3711548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711548 prefixEnd_3711548 := by exact prefixLift 3711548
  have htrace : WordTrace (prefixWord ++ tailWord_3711548) baseStart_3711548 baseEnd_3711548 := by
    simpa [prefixWord, tailWord_3711548, baseEnd_3711548] using wordTrace_append hprefix tailTrace_3711548
  have hstable : (prefixWord ++ tailWord_3711548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711548).length < 2 ^ (prefixWord ++ tailWord_3711548).sum := by decide
  have hdescent : baseEnd_3711548 < baseStart_3711548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711576 : List Nat := [2, 1, 2, 2, 1, 2, 4, 2, 2, 4]
def baseStart_3711576 : Nat := 118140960795 + 3711576 * 2 ^ 59
def prefixEnd_3711576 : Nat := 4983230072969 + 3 ^ 40 * 3711576 * 2
def baseEnd_3711576 : Nat := 1270548315794717117020519

theorem tailTrace_3711576 : CollatzResearch.WordTrace tailWord_3711576 prefixEnd_3711576 1270548315794717117020519 := by
  unfold tailWord_3711576
  simp only [CollatzResearch.WordTrace]
  refine ⟨67686149000800756779805291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90248198667734342373073721 67686149000800756779805291)
  ·
    refine ⟨101529223501201135169707937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67686149000800756779805291 101529223501201135169707937)
    ·
      refine ⟨76146917625900851377280953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101529223501201135169707937 76146917625900851377280953)
      ·
        refine ⟨57110188219425638532960715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76146917625900851377280953 57110188219425638532960715)
        ·
          refine ⟨85665282329138457799441073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57110188219425638532960715 85665282329138457799441073)
          ·
            refine ⟨64248961746853843349580805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85665282329138457799441073 64248961746853843349580805)
            ·
              refine ⟨12046680327535095628046401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64248961746853843349580805 12046680327535095628046401)
              ·
                refine ⟨9035010245651321721034801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12046680327535095628046401 9035010245651321721034801)
                ·
                  refine ⟨6776257684238491290776101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9035010245651321721034801 6776257684238491290776101)
                  ·
                    refine ⟨1270548315794717117020519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6776257684238491290776101 1270548315794717117020519)
                    ·
                      rfl

theorem cell22_3711576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_3711576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711576 prefixEnd_3711576 := by exact prefixLift 3711576
  have htrace : WordTrace (prefixWord ++ tailWord_3711576) baseStart_3711576 baseEnd_3711576 := by
    simpa [prefixWord, tailWord_3711576, baseEnd_3711576] using wordTrace_append hprefix tailTrace_3711576
  have hstable : (prefixWord ++ tailWord_3711576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711576).length < 2 ^ (prefixWord ++ tailWord_3711576).sum := by decide
  have hdescent : baseEnd_3711576 < baseStart_3711576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711580 : List Nat := [2, 2, 4, 1, 3, 1, 1, 4, 4]
def baseStart_3711580 : Nat := 118140960795 + 3711580 * 2 ^ 59
def prefixEnd_3711580 : Nat := 4983230072969 + 3 ^ 40 * 3711580 * 2
def baseEnd_3711580 : Nat := 423516561692154146640169

theorem tailTrace_3711580 : CollatzResearch.WordTrace tailWord_3711580 prefixEnd_3711580 423516561692154146640169 := by
  unfold tailWord_3711580
  simp only [CollatzResearch.WordTrace]
  refine ⟨67686221946793511121378097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90248295929058014828504129 67686221946793511121378097)
  ·
    refine ⟨50764666460095133341033573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67686221946793511121378097 50764666460095133341033573)
    ·
      refine ⟨9518374961267837501443795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50764666460095133341033573 9518374961267837501443795)
      ·
        refine ⟨14277562441901756252165693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9518374961267837501443795 14277562441901756252165693)
        ·
          refine ⟨5354085915713158594562135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14277562441901756252165693 5354085915713158594562135)
          ·
            refine ⟨8031128873569737891843203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5354085915713158594562135 8031128873569737891843203)
            ·
              refine ⟨12046693310354606837764805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8031128873569737891843203 12046693310354606837764805)
              ·
                refine ⟨2258754995691488782080901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12046693310354606837764805 2258754995691488782080901)
                ·
                  refine ⟨423516561692154146640169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2258754995691488782080901 423516561692154146640169)
                  ·
                    rfl

theorem cell22_3711580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_3711580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711580 prefixEnd_3711580 := by exact prefixLift 3711580
  have htrace : WordTrace (prefixWord ++ tailWord_3711580) baseStart_3711580 baseEnd_3711580 := by
    simpa [prefixWord, tailWord_3711580, baseEnd_3711580] using wordTrace_append hprefix tailTrace_3711580
  have hstable : (prefixWord ++ tailWord_3711580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711580).length < 2 ^ (prefixWord ++ tailWord_3711580).sum := by decide
  have hdescent : baseEnd_3711580 < baseStart_3711580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711640 : List Nat := [2, 1, 2, 4, 1, 1, 1, 6, 1, 3]
def baseStart_3711640 : Nat := 118140960795 + 3711640 * 2 ^ 59
def prefixEnd_3711640 : Nat := 4983230072969 + 3 ^ 40 * 3711640 * 2
def baseEnd_3711640 : Nat := 1270570224302642283420323

theorem tailTrace_3711640 : CollatzResearch.WordTrace tailWord_3711640 prefixEnd_3711640 1270570224302642283420323 := by
  unfold tailWord_3711640
  simp only [CollatzResearch.WordTrace]
  refine ⟨67687316136684826244970187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90249754848913101659960249 67687316136684826244970187)
  ·
    refine ⟨101530974205027239367455281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67687316136684826244970187 101530974205027239367455281)
    ·
      refine ⟨76148230653770429525591461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101530974205027239367455281 76148230653770429525591461)
      ·
        refine ⟨14277793247581955536048399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76148230653770429525591461 14277793247581955536048399)
        ·
          refine ⟨21416689871372933304072599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14277793247581955536048399 21416689871372933304072599)
          ·
            refine ⟨32125034807059399956108899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21416689871372933304072599 32125034807059399956108899)
            ·
              refine ⟨48187552210589099934163349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32125034807059399956108899 48187552210589099934163349)
              ·
                refine ⟨2258791509871364059413907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48187552210589099934163349 2258791509871364059413907)
                ·
                  refine ⟨3388187264807046089120861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2258791509871364059413907 3388187264807046089120861)
                  ·
                    refine ⟨1270570224302642283420323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3388187264807046089120861 1270570224302642283420323)
                    ·
                      rfl

theorem cell22_3711640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 1, 3].length) (baseStart_3711640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711640 prefixEnd_3711640 := by exact prefixLift 3711640
  have htrace : WordTrace (prefixWord ++ tailWord_3711640) baseStart_3711640 baseEnd_3711640 := by
    simpa [prefixWord, tailWord_3711640, baseEnd_3711640] using wordTrace_append hprefix tailTrace_3711640
  have hstable : (prefixWord ++ tailWord_3711640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711640).length < 2 ^ (prefixWord ++ tailWord_3711640).sum := by decide
  have hdescent : baseEnd_3711640 < baseStart_3711640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711728 : List Nat := [2, 1, 1, 1, 3, 1, 6, 1, 2, 4]
def baseStart_3711728 : Nat := 118140960795 + 3711728 * 2 ^ 59
def prefixEnd_3711728 : Nat := 4983230072969 + 3 ^ 40 * 3711728 * 2
def baseEnd_3711728 : Nat := 1270600348501039387220053

theorem tailTrace_3711728 : CollatzResearch.WordTrace tailWord_3711728 prefixEnd_3711728 1270600348501039387220053 := by
  unfold tailWord_3711728
  simp only [CollatzResearch.WordTrace]
  refine ⟨67688920948525421759571919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90251894598033895679429225 67688920948525421759571919)
  ·
    refine ⟨101533381422788132639357879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67688920948525421759571919 101533381422788132639357879)
    ·
      refine ⟨152300072134182198959036819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101533381422788132639357879 152300072134182198959036819)
      ·
        refine ⟨228450108201273298438555229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152300072134182198959036819 228450108201273298438555229)
        ·
          refine ⟨85668790575477486914458211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228450108201273298438555229 85668790575477486914458211)
          ·
            refine ⟨128503185863216230371687317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85668790575477486914458211 128503185863216230371687317)
            ·
              refine ⟨6023586837338260798672843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128503185863216230371687317 6023586837338260798672843)
              ·
                refine ⟨9035380256007391198009265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6023586837338260798672843 9035380256007391198009265)
                ·
                  refine ⟨6776535192005543398506949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9035380256007391198009265 6776535192005543398506949)
                  ·
                    refine ⟨1270600348501039387220053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6776535192005543398506949 1270600348501039387220053)
                    ·
                      rfl

theorem cell22_3711728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 2, 4].length) (baseStart_3711728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711728 prefixEnd_3711728 := by exact prefixLift 3711728
  have htrace : WordTrace (prefixWord ++ tailWord_3711728) baseStart_3711728 baseEnd_3711728 := by
    simpa [prefixWord, tailWord_3711728, baseEnd_3711728] using wordTrace_append hprefix tailTrace_3711728
  have hstable : (prefixWord ++ tailWord_3711728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711728).length < 2 ^ (prefixWord ++ tailWord_3711728).sum := by decide
  have hdescent : baseEnd_3711728 < baseStart_3711728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711775 : List Nat := [1, 1, 2, 4, 2, 3, 1, 2, 3, 3]
def baseStart_3711775 : Nat := 118140960795 + 3711775 * 2 ^ 59
def prefixEnd_3711775 : Nat := 4983230072969 + 3 ^ 40 * 3711775 * 2
def baseEnd_3711775 : Nat := 1270616437561546931294909

theorem tailTrace_3711775 : CollatzResearch.WordTrace tailWord_3711775 prefixEnd_3711775 1270616437561546931294909 := by
  unfold tailWord_3711775
  simp only [CollatzResearch.WordTrace]
  refine ⟨135379556127880570546104779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90253037418587047030736519 135379556127880570546104779)
  ·
    refine ⟨203069334191820855819157169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135379556127880570546104779 203069334191820855819157169)
    ·
      refine ⟨152302000643865641864367877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203069334191820855819157169 152302000643865641864367877)
      ·
        refine ⟨28556625120724807849568977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152302000643865641864367877 28556625120724807849568977)
        ·
          refine ⟨21417468840543605887176733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28556625120724807849568977 21417468840543605887176733)
          ·
            refine ⟨8031550815203852207691275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21417468840543605887176733 8031550815203852207691275)
            ·
              refine ⟨12047326222805778311536913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8031550815203852207691275 12047326222805778311536913)
              ·
                refine ⟨9035494667104333733652685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12047326222805778311536913 9035494667104333733652685)
                ·
                  refine ⟨3388310500164125150119757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9035494667104333733652685 3388310500164125150119757)
                  ·
                    refine ⟨1270616437561546931294909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3388310500164125150119757 1270616437561546931294909)
                    ·
                      rfl

theorem cell22_3711775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 3].length) (baseStart_3711775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711775 prefixEnd_3711775 := by exact prefixLift 3711775
  have htrace : WordTrace (prefixWord ++ tailWord_3711775) baseStart_3711775 baseEnd_3711775 := by
    simpa [prefixWord, tailWord_3711775, baseEnd_3711775] using wordTrace_append hprefix tailTrace_3711775
  have hstable : (prefixWord ++ tailWord_3711775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711775).length < 2 ^ (prefixWord ++ tailWord_3711775).sum := by decide
  have hdescent : baseEnd_3711775 < baseStart_3711775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711805 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 7]
def baseStart_3711805 : Nat := 118140960795 + 3711805 * 2 ^ 59
def prefixEnd_3711805 : Nat := 4983230072969 + 3 ^ 40 * 3711805 * 2
def baseEnd_3711805 : Nat := 423542235724878951014939

theorem tailTrace_3711805 : CollatzResearch.WordTrace tailWord_3711805 prefixEnd_3711805 423542235724878951014939 := by
  unfold tailWord_3711805
  simp only [CollatzResearch.WordTrace]
  refine ⟨135380650317771885669696869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90253766878514590446464579 135380650317771885669696869)
  ·
    refine ⟨25383871934582228563068163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135380650317771885669696869 25383871934582228563068163)
    ·
      refine ⟨38075807901873342844602245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25383871934582228563068163 38075807901873342844602245)
      ·
        refine ⟨7139213981601251783362921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38075807901873342844602245 7139213981601251783362921)
        ·
          refine ⟨5354410486200938837522191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7139213981601251783362921 5354410486200938837522191)
          ·
            refine ⟨8031615729301408256283287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5354410486200938837522191 8031615729301408256283287)
            ·
              refine ⟨12047423593952112384424931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8031615729301408256283287 12047423593952112384424931)
              ·
                refine ⟨18071135390928168576637397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12047423593952112384424931 18071135390928168576637397)
                ·
                  refine ⟨423542235724878951014939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18071135390928168576637397 423542235724878951014939)
                  ·
                    rfl

theorem cell22_3711805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_3711805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711805 prefixEnd_3711805 := by exact prefixLift 3711805
  have htrace : WordTrace (prefixWord ++ tailWord_3711805) baseStart_3711805 baseEnd_3711805 := by
    simpa [prefixWord, tailWord_3711805, baseEnd_3711805] using wordTrace_append hprefix tailTrace_3711805
  have hstable : (prefixWord ++ tailWord_3711805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711805).length < 2 ^ (prefixWord ++ tailWord_3711805).sum := by decide
  have hdescent : baseEnd_3711805 < baseStart_3711805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711809 : List Nat := [1, 2, 5, 3, 1, 1, 2, 1, 3, 3]
def baseStart_3711809 : Nat := 118140960795 + 3711809 * 2 ^ 59
def prefixEnd_3711809 : Nat := 4983230072969 + 3 ^ 40 * 3711809 * 2
def baseEnd_3711809 : Nat := 1270628076456382175944805

theorem tailTrace_3711809 : CollatzResearch.WordTrace tailWord_3711809 prefixEnd_3711809 1270628076456382175944805 := by
  unfold tailWord_3711809
  simp only [CollatzResearch.WordTrace]
  refine ⟨135380796209757394352842481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90253864139838262901894987 135380796209757394352842481)
  ·
    refine ⟨101535597157318045764631861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135380796209757394352842481 101535597157318045764631861)
    ·
      refine ⟨9518962233498566790434237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101535597157318045764631861 9518962233498566790434237)
      ·
        refine ⟨3569610837561962546412839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9518962233498566790434237 3569610837561962546412839)
        ·
          refine ⟨5354416256342943819619259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3569610837561962546412839 5354416256342943819619259)
          ·
            refine ⟨8031624384514415729428889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5354416256342943819619259 8031624384514415729428889)
            ·
              refine ⟨6023718288385811797071667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8031624384514415729428889 6023718288385811797071667)
              ·
                refine ⟨9035577432578717695607501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6023718288385811797071667 9035577432578717695607501)
                ·
                  refine ⟨3388341537217019135852813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9035577432578717695607501 3388341537217019135852813)
                  ·
                    refine ⟨1270628076456382175944805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3388341537217019135852813 1270628076456382175944805)
                    ·
                      rfl

theorem cell22_3711809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_3711809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711809 prefixEnd_3711809 := by exact prefixLift 3711809
  have htrace : WordTrace (prefixWord ++ tailWord_3711809) baseStart_3711809 baseEnd_3711809 := by
    simpa [prefixWord, tailWord_3711809, baseEnd_3711809] using wordTrace_append hprefix tailTrace_3711809
  have hstable : (prefixWord ++ tailWord_3711809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711809).length < 2 ^ (prefixWord ++ tailWord_3711809).sum := by decide
  have hdescent : baseEnd_3711809 < baseStart_3711809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711818 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 3, 4]
def baseStart_3711818 : Nat := 118140960795 + 3711818 * 2 ^ 59
def prefixEnd_3711818 : Nat := 4983230072969 + 3 ^ 40 * 3711818 * 2
def baseEnd_3711818 : Nat := 1270631157340309152469777

theorem tailTrace_3711818 : CollatzResearch.WordTrace tailWord_3711818 prefixEnd_3711818 1270631157340309152469777 := by
  unfold tailWord_3711818
  simp only [CollatzResearch.WordTrace]
  refine ⟨33845281116681197222480027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90254082977816525926613405 33845281116681197222480027)
  ·
    refine ⟨50767921675021795833720041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33845281116681197222480027 50767921675021795833720041)
    ·
      refine ⟨38075941256266346875290031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50767921675021795833720041 38075941256266346875290031)
      ·
        refine ⟨57113911884399520312935047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38075941256266346875290031 57113911884399520312935047)
        ·
          refine ⟨85670867826599280469402571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57113911884399520312935047 85670867826599280469402571)
          ·
            refine ⟨128506301739898920704103857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85670867826599280469402571 128506301739898920704103857)
            ·
              refine ⟨96379726304924190528077893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128506301739898920704103857 96379726304924190528077893)
              ·
                refine ⟨18071198682173285724014605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96379726304924190528077893 18071198682173285724014605)
                ·
                  refine ⟨6776699505814982146505477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18071198682173285724014605 6776699505814982146505477)
                  ·
                    refine ⟨1270631157340309152469777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6776699505814982146505477 1270631157340309152469777)
                    ·
                      rfl

theorem cell22_3711818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_3711818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711818 prefixEnd_3711818 := by exact prefixLift 3711818
  have htrace : WordTrace (prefixWord ++ tailWord_3711818) baseStart_3711818 baseEnd_3711818 := by
    simpa [prefixWord, tailWord_3711818, baseEnd_3711818] using wordTrace_append hprefix tailTrace_3711818
  have hstable : (prefixWord ++ tailWord_3711818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711818).length < 2 ^ (prefixWord ++ tailWord_3711818).sum := by decide
  have hdescent : baseEnd_3711818 < baseStart_3711818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711833 : List Nat := [1, 2, 1, 2, 2, 4, 2, 2, 6]
def baseStart_3711833 : Nat := 118140960795 + 3711833 * 2 ^ 59
def prefixEnd_3711833 : Nat := 4983230072969 + 3 ^ 40 * 3711833 * 2
def baseEnd_3711833 : Nat := 423545430715618037781577

theorem tailTrace_3711833 : CollatzResearch.WordTrace tailWord_3711833 prefixEnd_3711833 423545430715618037781577 := by
  unfold tailWord_3711833
  simp only [CollatzResearch.WordTrace]
  refine ⟨135381671561670446451716153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90254447707780297634477435 135381671561670446451716153)
  ·
    refine ⟨101536253671252834838787115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135381671561670446451716153 101536253671252834838787115)
    ·
      refine ⟨152304380506879252258180673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101536253671252834838787115 152304380506879252258180673)
      ·
        refine ⟨114228285380159439193635505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152304380506879252258180673 114228285380159439193635505)
        ·
          refine ⟨85671214035119579395226629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114228285380159439193635505 85671214035119579395226629)
          ·
            refine ⟨16063352631584921136604993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85671214035119579395226629 16063352631584921136604993)
            ·
              refine ⟨12047514473688690852453745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16063352631584921136604993 12047514473688690852453745)
              ·
                refine ⟨9035635855266518139340309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12047514473688690852453745 9035635855266518139340309)
                ·
                  refine ⟨423545430715618037781577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9035635855266518139340309 423545430715618037781577)
                  ·
                    rfl

theorem cell22_3711833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 6].length) (baseStart_3711833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711833 prefixEnd_3711833 := by exact prefixLift 3711833
  have htrace : WordTrace (prefixWord ++ tailWord_3711833) baseStart_3711833 baseEnd_3711833 := by
    simpa [prefixWord, tailWord_3711833, baseEnd_3711833] using wordTrace_append hprefix tailTrace_3711833
  have hstable : (prefixWord ++ tailWord_3711833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711833).length < 2 ^ (prefixWord ++ tailWord_3711833).sum := by decide
  have hdescent : baseEnd_3711833 < baseStart_3711833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711865 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 4, 3]
def baseStart_3711865 : Nat := 118140960795 + 3711865 * 2 ^ 59
def prefixEnd_3711865 : Nat := 4983230072969 + 3 ^ 40 * 3711865 * 2
def baseEnd_3711865 : Nat := 1270647246400816696544633

theorem tailTrace_3711865 : CollatzResearch.WordTrace tailWord_3711865 prefixEnd_3711865 1270647246400816696544633 := by
  unfold tailWord_3711865
  simp only [CollatzResearch.WordTrace]
  refine ⟨135382838697554515916881049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90255225798369677277920699 135382838697554515916881049)
  ·
    refine ⟨101537129023165886937660787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135382838697554515916881049 101537129023165886937660787)
    ·
      refine ⟨152305693534748830406491181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101537129023165886937660787 152305693534748830406491181)
      ·
        refine ⟨57114635075530811402434193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152305693534748830406491181 57114635075530811402434193)
        ·
          refine ⟨42835976306648108551825645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57114635075530811402434193 42835976306648108551825645)
          ·
            refine ⟨16063491114993040706934617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42835976306648108551825645 16063491114993040706934617)
            ·
              refine ⟨12047618336244780530200963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16063491114993040706934617 12047618336244780530200963)
              ·
                refine ⟨18071427504367170795301445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12047618336244780530200963 18071427504367170795301445)
                ·
                  refine ⟨3388392657068844524119021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18071427504367170795301445 3388392657068844524119021)
                  ·
                    refine ⟨1270647246400816696544633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3388392657068844524119021 1270647246400816696544633)
                    ·
                      rfl

theorem cell22_3711865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 3].length) (baseStart_3711865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711865 prefixEnd_3711865 := by exact prefixLift 3711865
  have htrace : WordTrace (prefixWord ++ tailWord_3711865) baseStart_3711865 baseEnd_3711865 := by
    simpa [prefixWord, tailWord_3711865, baseEnd_3711865] using wordTrace_append hprefix tailTrace_3711865
  have hstable : (prefixWord ++ tailWord_3711865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711865).length < 2 ^ (prefixWord ++ tailWord_3711865).sum := by decide
  have hdescent : baseEnd_3711865 < baseStart_3711865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711985 : List Nat := [1, 2, 2, 2, 4, 1, 1, 3, 6]
def baseStart_3711985 : Nat := 118140960795 + 3711985 * 2 ^ 59
def prefixEnd_3711985 : Nat := 4983230072969 + 3 ^ 40 * 3711985 * 2
def baseEnd_3711985 : Nat := 423562774951058794514755

theorem tailTrace_3711985 : CollatzResearch.WordTrace tailWord_3711985 prefixEnd_3711985 423562774951058794514755 := by
  unfold tailWord_3711985
  simp only [CollatzResearch.WordTrace]
  refine ⟨135387215457119776411249409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90258143638079850940832939 135387215457119776411249409)
  ·
    refine ⟨101540411592839832308437057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135387215457119776411249409 101540411592839832308437057)
    ·
      refine ⟨76155308694629874231327793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101540411592839832308437057 76155308694629874231327793)
      ·
        refine ⟨57116481520972405673495845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76155308694629874231327793 57116481520972405673495845)
        ·
          refine ⟨10709340285182326063780471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57116481520972405673495845 10709340285182326063780471)
          ·
            refine ⟨16064010427773489095670707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10709340285182326063780471 16064010427773489095670707)
            ·
              refine ⟨24096015641660233643506061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16064010427773489095670707 24096015641660233643506061)
              ·
                refine ⟨9036005865622587616314773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24096015641660233643506061 9036005865622587616314773)
                ·
                  refine ⟨423562774951058794514755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9036005865622587616314773 423562774951058794514755)
                  ·
                    rfl

theorem cell22_3711985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 6].length) (baseStart_3711985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3711985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3711985 prefixEnd_3711985 := by exact prefixLift 3711985
  have htrace : WordTrace (prefixWord ++ tailWord_3711985) baseStart_3711985 baseEnd_3711985 := by
    simpa [prefixWord, tailWord_3711985, baseEnd_3711985] using wordTrace_append hprefix tailTrace_3711985
  have hstable : (prefixWord ++ tailWord_3711985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711985).length < 2 ^ (prefixWord ++ tailWord_3711985).sum := by decide
  have hdescent : baseEnd_3711985 < baseStart_3711985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712036 : List Nat := [2, 3, 1, 4, 1, 2, 3, 2, 4]
def baseStart_3712036 : Nat := 118140960795 + 3712036 * 2 ^ 59
def prefixEnd_3712036 : Nat := 4983230072969 + 3 ^ 40 * 3712036 * 2
def baseEnd_3712036 : Nat := 423568594398476416839703

theorem tailTrace_3712036 : CollatzResearch.WordTrace tailWord_3712036 prefixEnd_3712036 423568594398476416839703 := by
  unfold tailWord_3712036
  simp only [CollatzResearch.WordTrace]
  refine ⟨67694537789967506060677981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90259383719956674747570641 67694537789967506060677981)
  ·
    refine ⟨25385451671237814772754243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67694537789967506060677981 25385451671237814772754243)
    ·
      refine ⟨38078177506856722159131365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25385451671237814772754243 38078177506856722159131365)
      ·
        refine ⟨7139658282535635404837131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38078177506856722159131365 7139658282535635404837131)
        ·
          refine ⟨10709487423803453107255697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7139658282535635404837131 10709487423803453107255697)
          ·
            refine ⟨8032115567852589830441773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10709487423803453107255697 8032115567852589830441773)
            ·
              refine ⟨3012043337944721186415665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8032115567852589830441773 3012043337944721186415665)
              ·
                refine ⟨2259032503458540889811749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3012043337944721186415665 2259032503458540889811749)
                ·
                  refine ⟨423568594398476416839703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2259032503458540889811749 423568594398476416839703)
                  ·
                    rfl

theorem cell22_3712036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_3712036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712036 prefixEnd_3712036 := by exact prefixLift 3712036
  have htrace : WordTrace (prefixWord ++ tailWord_3712036) baseStart_3712036 baseEnd_3712036 := by
    simpa [prefixWord, tailWord_3712036, baseEnd_3712036] using wordTrace_append hprefix tailTrace_3712036
  have hstable : (prefixWord ++ tailWord_3712036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712036).length < 2 ^ (prefixWord ++ tailWord_3712036).sum := by decide
  have hdescent : baseEnd_3712036 < baseStart_3712036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712120 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 8]
def baseStart_3712120 : Nat := 118140960795 + 3712120 * 2 ^ 59
def prefixEnd_3712120 : Nat := 4983230072969 + 3 ^ 40 * 3712120 * 2
def baseEnd_3712120 : Nat := 423578179370693677139617

theorem tailTrace_3712120 : CollatzResearch.WordTrace tailWord_3712120 prefixEnd_3712120 423578179370693677139617 := by
  unfold tailWord_3712120
  simp only [CollatzResearch.WordTrace]
  refine ⟨67696069655815347233706907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90261426207753796311609209 67696069655815347233706907)
  ·
    refine ⟨101544104483723020850560361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67696069655815347233706907 101544104483723020850560361)
    ·
      refine ⟨76158078362792265637920271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101544104483723020850560361 76158078362792265637920271)
      ·
        refine ⟨114237117544188398456880407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76158078362792265637920271 114237117544188398456880407)
        ·
          refine ⟨171355676316282597685320611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114237117544188398456880407 171355676316282597685320611)
          ·
            refine ⟨257033514474423896527980917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171355676316282597685320611 257033514474423896527980917)
            ·
              refine ⟨24096891981977240299498211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 257033514474423896527980917 24096891981977240299498211)
              ·
                refine ⟨36145337972965860449247317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24096891981977240299498211 36145337972965860449247317)
                ·
                  refine ⟨423578179370693677139617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36145337972965860449247317 423578179370693677139617)
                  ·
                    rfl

theorem cell22_3712120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 8].length) (baseStart_3712120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712120 prefixEnd_3712120 := by exact prefixLift 3712120
  have htrace : WordTrace (prefixWord ++ tailWord_3712120) baseStart_3712120 baseEnd_3712120 := by
    simpa [prefixWord, tailWord_3712120, baseEnd_3712120] using wordTrace_append hprefix tailTrace_3712120
  have hstable : (prefixWord ++ tailWord_3712120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712120).length < 2 ^ (prefixWord ++ tailWord_3712120).sum := by decide
  have hdescent : baseEnd_3712120 < baseStart_3712120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712154 : List Nat := [3, 1, 1, 5, 1, 2, 2, 1, 6]
def baseStart_3712154 : Nat := 118140960795 + 3712154 * 2 ^ 59
def prefixEnd_3712154 : Nat := 4983230072969 + 3 ^ 40 * 3712154 * 2
def baseEnd_3712154 : Nat := 423582059002305425356249

theorem tailTrace_3712154 : CollatzResearch.WordTrace tailWord_3712154 prefixEnd_3712154 423582059002305425356249 := by
  unfold tailWord_3712154
  simp only [CollatzResearch.WordTrace]
  refine ⟨33848344848376879568537879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90262252929005012182767677 33848344848376879568537879)
  ·
    refine ⟨50772517272565319352806819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33848344848376879568537879 50772517272565319352806819)
    ·
      refine ⟨76158775908847979029210229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50772517272565319352806819 76158775908847979029210229)
      ·
        refine ⟨7139885241454498033988459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76158775908847979029210229 7139885241454498033988459)
        ·
          refine ⟨10709827862181747050982689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7139885241454498033988459 10709827862181747050982689)
          ·
            refine ⟨8032370896636310288237017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10709827862181747050982689 8032370896636310288237017)
            ·
              refine ⟨6024278172477232716177763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8032370896636310288237017 6024278172477232716177763)
              ·
                refine ⟨9036417258715849074266645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6024278172477232716177763 9036417258715849074266645)
                ·
                  refine ⟨423582059002305425356249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9036417258715849074266645 423582059002305425356249)
                  ·
                    rfl

theorem cell22_3712154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_3712154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712154 prefixEnd_3712154 := by exact prefixLift 3712154
  have htrace : WordTrace (prefixWord ++ tailWord_3712154) baseStart_3712154 baseEnd_3712154 := by
    simpa [prefixWord, tailWord_3712154, baseEnd_3712154] using wordTrace_append hprefix tailTrace_3712154
  have hstable : (prefixWord ++ tailWord_3712154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712154).length < 2 ^ (prefixWord ++ tailWord_3712154).sum := by decide
  have hdescent : baseEnd_3712154 < baseStart_3712154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712205 : List Nat := [1, 6, 2, 2, 2, 1, 1, 1, 6]
def baseStart_3712205 : Nat := 118140960795 + 3712205 * 2 ^ 59
def prefixEnd_3712205 : Nat := 4983230072969 + 3 ^ 40 * 3712205 * 2
def baseEnd_3712205 : Nat := 423587878449723047681197

theorem tailTrace_3712205 : CollatzResearch.WordTrace tailWord_3712205 prefixEnd_3712205 423587878449723047681197 := by
  unfold tailWord_3712205
  simp only [CollatzResearch.WordTrace]
  refine ⟨135395239516322753984258069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90263493010881835989505379 135395239516322753984258069)
  ·
    refine ⟨6346651852327629093012097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 135395239516322753984258069 6346651852327629093012097)
    ·
      refine ⟨4759988889245721819759073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6346651852327629093012097 4759988889245721819759073)
      ·
        refine ⟨3569991666934291364819305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4759988889245721819759073 3569991666934291364819305)
        ·
          refine ⟨2677493750200718523614479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3569991666934291364819305 2677493750200718523614479)
          ·
            refine ⟨4016240625301077785421719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2677493750200718523614479 4016240625301077785421719)
            ·
              refine ⟨6024360937951616678132579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4016240625301077785421719 6024360937951616678132579)
              ·
                refine ⟨9036541406927425017198869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6024360937951616678132579 9036541406927425017198869)
                ·
                  refine ⟨423587878449723047681197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9036541406927425017198869 423587878449723047681197)
                  ·
                    rfl

theorem cell22_3712205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_3712205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712205 prefixEnd_3712205 := by exact prefixLift 3712205
  have htrace : WordTrace (prefixWord ++ tailWord_3712205) baseStart_3712205 baseEnd_3712205 := by
    simpa [prefixWord, tailWord_3712205, baseEnd_3712205] using wordTrace_append hprefix tailTrace_3712205
  have hstable : (prefixWord ++ tailWord_3712205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712205).length < 2 ^ (prefixWord ++ tailWord_3712205).sum := by decide
  have hdescent : baseEnd_3712205 < baseStart_3712205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712304 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 4, 3]
def baseStart_3712304 : Nat := 118140960795 + 3712304 * 2 ^ 59
def prefixEnd_3712304 : Nat := 4983230072969 + 3 ^ 40 * 3712304 * 2
def baseEnd_3712304 : Nat := 1270797525072365884818287

theorem tailTrace_3712304 : CollatzResearch.WordTrace tailWord_3712304 prefixEnd_3712304 1270797525072365884818287 := by
  unfold tailWord_3712304
  simp only [CollatzResearch.WordTrace]
  refine ⟨67699425171482046946055983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90265900228642729261407977 67699425171482046946055983)
  ·
    refine ⟨101549137757223070419083975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67699425171482046946055983 101549137757223070419083975)
    ·
      refine ⟨152323706635834605628625963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101549137757223070419083975 152323706635834605628625963)
      ·
        refine ⟨228485559953751908442938945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152323706635834605628625963 228485559953751908442938945)
        ·
          refine ⟨171364169965313931332204209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228485559953751908442938945 171364169965313931332204209)
          ·
            refine ⟨128523127473985448499153157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171364169965313931332204209 128523127473985448499153157)
            ·
              refine ⟨24098086401372271593591217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128523127473985448499153157 24098086401372271593591217)
              ·
                refine ⟨18073564801029203695193413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24098086401372271593591217 18073564801029203695193413)
                ·
                  refine ⟨3388793400192975692848765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18073564801029203695193413 3388793400192975692848765)
                  ·
                    refine ⟨1270797525072365884818287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3388793400192975692848765 1270797525072365884818287)
                    ·
                      rfl

theorem cell22_3712304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 4, 3].length) (baseStart_3712304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712304 prefixEnd_3712304 := by exact prefixLift 3712304
  have htrace : WordTrace (prefixWord ++ tailWord_3712304) baseStart_3712304 baseEnd_3712304 := by
    simpa [prefixWord, tailWord_3712304, baseEnd_3712304] using wordTrace_append hprefix tailTrace_3712304
  have hstable : (prefixWord ++ tailWord_3712304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712304).length < 2 ^ (prefixWord ++ tailWord_3712304).sum := by decide
  have hdescent : baseEnd_3712304 < baseStart_3712304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712306 : List Nat := [3, 2, 1, 1, 4, 1, 1, 5, 4]
def baseStart_3712306 : Nat := 118140960795 + 3712306 * 2 ^ 59
def prefixEnd_3712306 : Nat := 4983230072969 + 3 ^ 40 * 3712306 * 2
def baseEnd_3712306 : Nat := 423599403237746182089427

theorem tailTrace_3712306 : CollatzResearch.WordTrace tailWord_3712306 prefixEnd_3712306 423599403237746182089427 := by
  unfold tailWord_3712306
  simp only [CollatzResearch.WordTrace]
  refine ⟨33849730822239212058421193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90265948859304565489123181 33849730822239212058421193)
  ·
    refine ⟨25387298116679409043815895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33849730822239212058421193 25387298116679409043815895)
    ·
      refine ⟨38080947175019113565723843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25387298116679409043815895 38080947175019113565723843)
      ·
        refine ⟨57121420762528670348585765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38080947175019113565723843 57121420762528670348585765)
        ·
          refine ⟨10710266392974125690359831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57121420762528670348585765 10710266392974125690359831)
          ·
            refine ⟨16065399589461188535539747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10710266392974125690359831 16065399589461188535539747)
            ·
              refine ⟨24098099384191782803309621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16065399589461188535539747 24098099384191782803309621)
              ·
                refine ⟨2259196817267979637810277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24098099384191782803309621 2259196817267979637810277)
                ·
                  refine ⟨423599403237746182089427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2259196817267979637810277 423599403237746182089427)
                  ·
                    rfl

theorem cell22_3712306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_3712306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712306 prefixEnd_3712306 := by exact prefixLift 3712306
  have htrace : WordTrace (prefixWord ++ tailWord_3712306) baseStart_3712306 baseEnd_3712306 := by
    simpa [prefixWord, tailWord_3712306, baseEnd_3712306] using wordTrace_append hprefix tailTrace_3712306
  have hstable : (prefixWord ++ tailWord_3712306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712306).length < 2 ^ (prefixWord ++ tailWord_3712306).sum := by decide
  have hdescent : baseEnd_3712306 < baseStart_3712306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712379 : List Nat := [1, 1, 1, 1, 1, 6, 2, 4, 5]
def baseStart_3712379 : Nat := 118140960795 + 3712379 * 2 ^ 59
def prefixEnd_3712379 : Nat := 4983230072969 + 3 ^ 40 * 3712379 * 2
def baseEnd_3712379 : Nat := 423607733035030229731019

theorem tailTrace_3712379 : CollatzResearch.WordTrace tailWord_3712379 prefixEnd_3712379 423607733035030229731019 := by
  unfold tailWord_3712379
  simp only [CollatzResearch.WordTrace]
  refine ⟨135401585817692381701092191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90267723878461587800728127 135401585817692381701092191)
  ·
    refine ⟨203102378726538572551638287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135401585817692381701092191 203102378726538572551638287)
    ·
      refine ⟨304653568089807858827457431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203102378726538572551638287 304653568089807858827457431)
      ·
        refine ⟨456980352134711788241186147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304653568089807858827457431 456980352134711788241186147)
        ·
          refine ⟨685470528202067682361779221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456980352134711788241186147 685470528202067682361779221)
          ·
            refine ⟨32131431009471922610708401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 685470528202067682361779221 32131431009471922610708401)
            ·
              refine ⟨24098573257103941958031301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32131431009471922610708401 24098573257103941958031301)
              ·
                refine ⟨4518482485706989117130869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24098573257103941958031301 4518482485706989117130869)
                ·
                  refine ⟨423607733035030229731019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4518482485706989117130869 423607733035030229731019)
                  ·
                    rfl

theorem cell22_3712379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 5].length) (baseStart_3712379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712379 prefixEnd_3712379 := by exact prefixLift 3712379
  have htrace : WordTrace (prefixWord ++ tailWord_3712379) baseStart_3712379 baseEnd_3712379 := by
    simpa [prefixWord, tailWord_3712379, baseEnd_3712379] using wordTrace_append hprefix tailTrace_3712379
  have hstable : (prefixWord ++ tailWord_3712379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712379).length < 2 ^ (prefixWord ++ tailWord_3712379).sum := by decide
  have hdescent : baseEnd_3712379 < baseStart_3712379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712439 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 3, 5]
def baseStart_3712439 : Nat := 118140960795 + 3712439 * 2 ^ 59
def prefixEnd_3712439 : Nat := 4983230072969 + 3 ^ 40 * 3712439 * 2
def baseEnd_3712439 : Nat := 1270843738331270532692873

theorem tailTrace_3712439 : CollatzResearch.WordTrace tailWord_3712439 prefixEnd_3712439 1270843738331270532692873 := by
  unfold tailWord_3712439
  simp only [CollatzResearch.WordTrace]
  refine ⟨135403774197475011948276371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90269182798316674632184247 135403774197475011948276371)
  ·
    refine ⟨203105661296212517922414557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135403774197475011948276371 203105661296212517922414557)
    ·
      refine ⟨76164622986079694220905459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203105661296212517922414557 76164622986079694220905459)
      ·
        refine ⟨114246934479119541331358189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76164622986079694220905459 114246934479119541331358189)
        ·
          refine ⟨42842600429669827999259321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114246934479119541331358189 42842600429669827999259321)
          ·
            refine ⟨32131950322252370999444491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42842600429669827999259321 32131950322252370999444491)
            ·
              refine ⟨48197925483378556499166737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32131950322252370999444491 48197925483378556499166737)
              ·
                refine ⟨36148444112533917374375053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48197925483378556499166737 36148444112533917374375053)
                ·
                  refine ⟨13555666542200219015390645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36148444112533917374375053 13555666542200219015390645)
                  ·
                    refine ⟨1270843738331270532692873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13555666542200219015390645 1270843738331270532692873)
                    ·
                      rfl

theorem cell22_3712439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_3712439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712439 prefixEnd_3712439 := by exact prefixLift 3712439
  have htrace : WordTrace (prefixWord ++ tailWord_3712439) baseStart_3712439 baseEnd_3712439 := by
    simpa [prefixWord, tailWord_3712439, baseEnd_3712439] using wordTrace_append hprefix tailTrace_3712439
  have hstable : (prefixWord ++ tailWord_3712439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712439).length < 2 ^ (prefixWord ++ tailWord_3712439).sum := by decide
  have hdescent : baseEnd_3712439 < baseStart_3712439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712456 : List Nat := [2, 1, 3, 1, 3, 1, 4, 1, 1, 5]
def baseStart_3712456 : Nat := 118140960795 + 3712456 * 2 ^ 59
def prefixEnd_3712456 : Nat := 4983230072969 + 3 ^ 40 * 3712456 * 2
def baseEnd_3712456 : Nat := 1270849557778688155017821

theorem tailTrace_3712456 : CollatzResearch.WordTrace tailWord_3712456 prefixEnd_3712456 1270849557778688155017821 := by
  unfold tailWord_3712456
  simp only [CollatzResearch.WordTrace]
  refine ⟨67702197119206711925822611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90269596158942282567763481 67702197119206711925822611)
  ·
    refine ⟨101553295678810067888733917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67702197119206711925822611 101553295678810067888733917)
    ·
      refine ⟨38082485879553775458275219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101553295678810067888733917 38082485879553775458275219)
      ·
        refine ⟨57123728819330663187412829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38082485879553775458275219 57123728819330663187412829)
        ·
          refine ⟨21421398307248998695279811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57123728819330663187412829 21421398307248998695279811)
          ·
            refine ⟨32132097460873498042919717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21421398307248998695279811 32132097460873498042919717)
            ·
              refine ⟨6024768273913780883047447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32132097460873498042919717 6024768273913780883047447)
              ·
                refine ⟨9037152410870671324571171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6024768273913780883047447 9037152410870671324571171)
                ·
                  refine ⟨13555728616306006986856757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9037152410870671324571171 13555728616306006986856757)
                  ·
                    refine ⟨1270849557778688155017821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13555728616306006986856757 1270849557778688155017821)
                    ·
                      rfl

theorem cell22_3712456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_3712456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712456 prefixEnd_3712456 := by exact prefixLift 3712456
  have htrace : WordTrace (prefixWord ++ tailWord_3712456) baseStart_3712456 baseEnd_3712456 := by
    simpa [prefixWord, tailWord_3712456, baseEnd_3712456] using wordTrace_append hprefix tailTrace_3712456
  have hstable : (prefixWord ++ tailWord_3712456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712456).length < 2 ^ (prefixWord ++ tailWord_3712456).sum := by decide
  have hdescent : baseEnd_3712456 < baseStart_3712456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712484 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_3712484 : Nat := 118140960795 + 3712484 * 2 ^ 59
def prefixEnd_3712484 : Nat := 4983230072969 + 3 ^ 40 * 3712484 * 2
def baseEnd_3712484 : Nat := 1270859142750905415317735

theorem tailTrace_3712484 : CollatzResearch.WordTrace tailWord_3712484 prefixEnd_3712484 1270859142750905415317735 := by
  unfold tailWord_3712484
  simp only [CollatzResearch.WordTrace]
  refine ⟨67702707741155992316832253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90270276988207989755776337 67702707741155992316832253)
  ·
    refine ⟨25388515402933497118812095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67702707741155992316832253 25388515402933497118812095)
    ·
      refine ⟨38082773104400245678218143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25388515402933497118812095 38082773104400245678218143)
      ·
        refine ⟨57124159656600368517327215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38082773104400245678218143 57124159656600368517327215)
        ·
          refine ⟨85686239484900552775990823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57124159656600368517327215 85686239484900552775990823)
          ·
            refine ⟨128529359227350829163986235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85686239484900552775990823 128529359227350829163986235)
            ·
              refine ⟨192794038841026243745979353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128529359227350829163986235 192794038841026243745979353)
              ·
                refine ⟨144595529130769682809484515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192794038841026243745979353 144595529130769682809484515)
                ·
                  refine ⟨216893293696154524214226773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144595529130769682809484515 216893293696154524214226773)
                  ·
                    refine ⟨1270859142750905415317735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 216893293696154524214226773 1270859142750905415317735)
                    ·
                      rfl

theorem cell22_3712484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_3712484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712484 prefixEnd_3712484 := by exact prefixLift 3712484
  have htrace : WordTrace (prefixWord ++ tailWord_3712484) baseStart_3712484 baseEnd_3712484 := by
    simpa [prefixWord, tailWord_3712484, baseEnd_3712484] using wordTrace_append hprefix tailTrace_3712484
  have hstable : (prefixWord ++ tailWord_3712484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712484).length < 2 ^ (prefixWord ++ tailWord_3712484).sum := by decide
  have hdescent : baseEnd_3712484 < baseStart_3712484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712499 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 2, 6]
def baseStart_3712499 : Nat := 118140960795 + 3712499 * 2 ^ 59
def prefixEnd_3712499 : Nat := 4983230072969 + 3 ^ 40 * 3712499 * 2
def baseEnd_3712499 : Nat := 1270864277557450376192689

theorem tailTrace_3712499 : CollatzResearch.WordTrace tailWord_3712499 prefixEnd_3712499 1270864277557450376192689 := by
  unfold tailWord_3712499
  simp only [CollatzResearch.WordTrace]
  refine ⟨135405962577257642195460551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90270641718171761463640367 135405962577257642195460551)
  ·
    refine ⟨203108943865886463293190827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135405962577257642195460551 203108943865886463293190827)
    ·
      refine ⟨304663415798829694939786241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203108943865886463293190827 304663415798829694939786241)
      ·
        refine ⟨228497561849122271204839681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304663415798829694939786241 228497561849122271204839681)
        ·
          refine ⟨171373171386841703403629761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228497561849122271204839681 171373171386841703403629761)
          ·
            refine ⟨128529878540131277552722321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171373171386841703403629761 128529878540131277552722321)
            ·
              refine ⟨96397408905098458164541741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128529878540131277552722321 96397408905098458164541741)
              ·
                refine ⟨36149028339411921811703153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96397408905098458164541741 36149028339411921811703153)
                ·
                  refine ⟨27111771254558941358777365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36149028339411921811703153 27111771254558941358777365)
                  ·
                    refine ⟨1270864277557450376192689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27111771254558941358777365 1270864277557450376192689)
                    ·
                      rfl

theorem cell22_3712499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 6].length) (baseStart_3712499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712499 prefixEnd_3712499 := by exact prefixLift 3712499
  have htrace : WordTrace (prefixWord ++ tailWord_3712499) baseStart_3712499 baseEnd_3712499 := by
    simpa [prefixWord, tailWord_3712499, baseEnd_3712499] using wordTrace_append hprefix tailTrace_3712499
  have hstable : (prefixWord ++ tailWord_3712499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712499).length < 2 ^ (prefixWord ++ tailWord_3712499).sum := by decide
  have hdescent : baseEnd_3712499 < baseStart_3712499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712546 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_3712546 : Nat := 118140960795 + 3712546 * 2 ^ 59
def prefixEnd_3712546 : Nat := 4983230072969 + 3 ^ 40 * 3712546 * 2
def baseEnd_3712546 : Nat := 1270880366617957920267545

theorem tailTrace_3712546 : CollatzResearch.WordTrace tailWord_3712546 prefixEnd_3712546 1270880366617957920267545 := by
  unfold tailWord_3712546
  simp only [CollatzResearch.WordTrace]
  refine ⟨33851919202021842305605373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90271784538724912814947661 33851919202021842305605373)
  ·
    refine ⟨12694469700758190864602015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33851919202021842305605373 12694469700758190864602015)
    ·
      refine ⟨19041704551137286296903023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12694469700758190864602015 19041704551137286296903023)
      ·
        refine ⟨28562556826705929445354535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19041704551137286296903023 28562556826705929445354535)
        ·
          refine ⟨42843835240058894168031803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28562556826705929445354535 42843835240058894168031803)
          ·
            refine ⟨64265752860088341252047705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42843835240058894168031803 64265752860088341252047705)
            ·
              refine ⟨48199314645066255939035779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64265752860088341252047705 48199314645066255939035779)
              ·
                refine ⟨72298971967599383908553669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48199314645066255939035779 72298971967599383908553669)
                ·
                  refine ⟨13556057243924884482853813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72298971967599383908553669 13556057243924884482853813)
                  ·
                    refine ⟨1270880366617957920267545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13556057243924884482853813 1270880366617957920267545)
                    ·
                      rfl

theorem cell22_3712546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_3712546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712546 prefixEnd_3712546 := by exact prefixLift 3712546
  have htrace : WordTrace (prefixWord ++ tailWord_3712546) baseStart_3712546 baseEnd_3712546 := by
    simpa [prefixWord, tailWord_3712546, baseEnd_3712546] using wordTrace_append hprefix tailTrace_3712546
  have hstable : (prefixWord ++ tailWord_3712546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712546).length < 2 ^ (prefixWord ++ tailWord_3712546).sum := by decide
  have hdescent : baseEnd_3712546 < baseStart_3712546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712552 : List Nat := [2, 1, 5, 2, 2, 2, 1, 1, 3, 3]
def baseStart_3712552 : Nat := 118140960795 + 3712552 * 2 ^ 59
def prefixEnd_3712552 : Nat := 4983230072969 + 3 ^ 40 * 3712552 * 2
def baseEnd_3712552 : Nat := 1270882420540575904617527

theorem tailTrace_3712552 : CollatzResearch.WordTrace tailWord_3712552 prefixEnd_3712552 1270882420540575904617527 := by
  unfold tailWord_3712552
  simp only [CollatzResearch.WordTrace]
  refine ⟨67703947823032816123569955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90271930430710421498093273 67703947823032816123569955)
  ·
    refine ⟨101555921734549224185354933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67703947823032816123569955 101555921734549224185354933)
    ·
      refine ⟨9520867662613989767377025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101555921734549224185354933 9520867662613989767377025)
      ·
        refine ⟨7140650746960492325532769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9520867662613989767377025 7140650746960492325532769)
        ·
          refine ⟨5355488060220369244149577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7140650746960492325532769 5355488060220369244149577)
          ·
            refine ⟨4016616045165276933112183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5355488060220369244149577 4016616045165276933112183)
            ·
              refine ⟨6024924067747915399668275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4016616045165276933112183 6024924067747915399668275)
              ·
                refine ⟨9037386101621873099502413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6024924067747915399668275 9037386101621873099502413)
                ·
                  refine ⟨3389019788108202412313405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9037386101621873099502413 3389019788108202412313405)
                  ·
                    refine ⟨1270882420540575904617527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3389019788108202412313405 1270882420540575904617527)
                    ·
                      rfl

theorem cell22_3712552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_3712552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712552 prefixEnd_3712552 := by exact prefixLift 3712552
  have htrace : WordTrace (prefixWord ++ tailWord_3712552) baseStart_3712552 baseEnd_3712552 := by
    simpa [prefixWord, tailWord_3712552, baseEnd_3712552] using wordTrace_append hprefix tailTrace_3712552
  have hstable : (prefixWord ++ tailWord_3712552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712552).length < 2 ^ (prefixWord ++ tailWord_3712552).sum := by decide
  have hdescent : baseEnd_3712552 < baseStart_3712552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712561 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 3, 4]
def baseStart_3712561 : Nat := 118140960795 + 3712561 * 2 ^ 59
def prefixEnd_3712561 : Nat := 4983230072969 + 3 ^ 40 * 3712561 * 2
def baseEnd_3712561 : Nat := 1270885501424502881142499

theorem tailTrace_3712561 : CollatzResearch.WordTrace tailWord_3712561 prefixEnd_3712561 1270885501424502881142499 := by
  unfold tailWord_3712561
  simp only [CollatzResearch.WordTrace]
  refine ⟨135408223903033026784217537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90272149268688684522811691 135408223903033026784217537)
  ·
    refine ⟨101556167927274770088163153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135408223903033026784217537 101556167927274770088163153)
    ·
      refine ⟨76167125945456077566122365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101556167927274770088163153 76167125945456077566122365)
      ·
        refine ⟨28562672229546029087295887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76167125945456077566122365 28562672229546029087295887)
        ·
          refine ⟨42844008344319043630943831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28562672229546029087295887 42844008344319043630943831)
          ·
            refine ⟨64266012516478565446415747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42844008344319043630943831 64266012516478565446415747)
            ·
              refine ⟨96399018774717848169623621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64266012516478565446415747 96399018774717848169623621)
              ·
                refine ⟨18074816020259596531804429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96399018774717848169623621 18074816020259596531804429)
                ·
                  refine ⟨6778056007597348699426661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18074816020259596531804429 6778056007597348699426661)
                  ·
                    refine ⟨1270885501424502881142499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6778056007597348699426661 1270885501424502881142499)
                    ·
                      rfl

theorem cell22_3712561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_3712561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712561 prefixEnd_3712561 := by exact prefixLift 3712561
  have htrace : WordTrace (prefixWord ++ tailWord_3712561) baseStart_3712561 baseEnd_3712561 := by
    simpa [prefixWord, tailWord_3712561, baseEnd_3712561] using wordTrace_append hprefix tailTrace_3712561
  have hstable : (prefixWord ++ tailWord_3712561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712561).length < 2 ^ (prefixWord ++ tailWord_3712561).sum := by decide
  have hdescent : baseEnd_3712561 < baseStart_3712561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712565 : List Nat := [1, 3, 3, 1, 1, 5, 2, 1, 5]
def baseStart_3712565 : Nat := 118140960795 + 3712565 * 2 ^ 59
def prefixEnd_3712565 : Nat := 4983230072969 + 3 ^ 40 * 3712565 * 2
def baseEnd_3712565 : Nat := 423628956902082734680829

theorem tailTrace_3712565 : CollatzResearch.WordTrace tailWord_3712565 prefixEnd_3712565 423628956902082734680829 := by
  unfold tailWord_3712565
  simp only [CollatzResearch.WordTrace]
  refine ⟨135408369795018535467363149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90272246530012356978242099 135408369795018535467363149)
  ·
    refine ⟨50778138673131950800261181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135408369795018535467363149 50778138673131950800261181)
    ·
      refine ⟨19041802002424481550097943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50778138673131950800261181 19041802002424481550097943)
      ·
        refine ⟨28562703003636722325146915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19041802002424481550097943 28562703003636722325146915)
        ·
          refine ⟨42844054505455083487720373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28562703003636722325146915 42844054505455083487720373)
          ·
            refine ⟨4016630109886414076973785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42844054505455083487720373 4016630109886414076973785)
            ·
              refine ⟨3012472582414810557730339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4016630109886414076973785 3012472582414810557730339)
              ·
                refine ⟨4518708873622215836595509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012472582414810557730339 4518708873622215836595509)
                ·
                  refine ⟨423628956902082734680829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4518708873622215836595509 423628956902082734680829)
                  ·
                    rfl

theorem cell22_3712565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_3712565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712565 prefixEnd_3712565 := by exact prefixLift 3712565
  have htrace : WordTrace (prefixWord ++ tailWord_3712565) baseStart_3712565 baseEnd_3712565 := by
    simpa [prefixWord, tailWord_3712565, baseEnd_3712565] using wordTrace_append hprefix tailTrace_3712565
  have hstable : (prefixWord ++ tailWord_3712565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712565).length < 2 ^ (prefixWord ++ tailWord_3712565).sum := by decide
  have hdescent : baseEnd_3712565 < baseStart_3712565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712593 : List Nat := [1, 2, 2, 1, 3, 2, 2, 5, 4]
def baseStart_3712593 : Nat := 118140960795 + 3712593 * 2 ^ 59
def prefixEnd_3712593 : Nat := 4983230072969 + 3 ^ 40 * 3712593 * 2
def baseEnd_3712593 : Nat := 423632151892821821447467

theorem tailTrace_3712593 : CollatzResearch.WordTrace tailWord_3712593 prefixEnd_3712593 423632151892821821447467 := by
  unfold tailWord_3712593
  simp only [CollatzResearch.WordTrace]
  refine ⟨135409391038917096249382433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90272927359278064166254955 135409391038917096249382433)
  ·
    refine ⟨101557043279187822187036825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135409391038917096249382433 101557043279187822187036825)
    ·
      refine ⟨76167782459390866640277619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101557043279187822187036825 76167782459390866640277619)
      ·
        refine ⟨114251673689086299960416429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76167782459390866640277619 114251673689086299960416429)
        ·
          refine ⟨42844377633407362485156161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114251673689086299960416429 42844377633407362485156161)
          ·
            refine ⟨32133283225055521863867121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42844377633407362485156161 32133283225055521863867121)
            ·
              refine ⟨24099962418791641397900341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32133283225055521863867121 24099962418791641397900341)
              ·
                refine ⟨2259371476761716381053157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24099962418791641397900341 2259371476761716381053157)
                ·
                  refine ⟨423632151892821821447467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2259371476761716381053157 423632151892821821447467)
                  ·
                    rfl

theorem cell22_3712593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 4].length) (baseStart_3712593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712593 prefixEnd_3712593 := by exact prefixLift 3712593
  have htrace : WordTrace (prefixWord ++ tailWord_3712593) baseStart_3712593 baseEnd_3712593 := by
    simpa [prefixWord, tailWord_3712593, baseEnd_3712593] using wordTrace_append hprefix tailTrace_3712593
  have hstable : (prefixWord ++ tailWord_3712593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712593).length < 2 ^ (prefixWord ++ tailWord_3712593).sum := by decide
  have hdescent : baseEnd_3712593 < baseStart_3712593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712681 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 6, 5]
def baseStart_3712681 : Nat := 118140960795 + 3712681 * 2 ^ 59
def prefixEnd_3712681 : Nat := 4983230072969 + 3 ^ 40 * 3712681 * 2
def baseEnd_3712681 : Nat := 1270926579876862568142131

theorem tailTrace_3712681 : CollatzResearch.WordTrace tailWord_3712681 prefixEnd_3712681 1270926579876862568142131 := by
  unfold tailWord_3712681
  simp only [CollatzResearch.WordTrace]
  refine ⟨135412600662598287278585897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90275067108398858185723931 135412600662598287278585897)
  ·
    refine ⟨101559450496948715458939423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135412600662598287278585897 101559450496948715458939423)
    ·
      refine ⟨152339175745423073188409135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101559450496948715458939423 152339175745423073188409135)
      ·
        refine ⟨228508763618134609782613703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152339175745423073188409135 228508763618134609782613703)
        ·
          refine ⟨342763145427201914673920555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228508763618134609782613703 342763145427201914673920555)
          ·
            refine ⟨514144718140802872010880833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342763145427201914673920555 514144718140802872010880833)
            ·
              refine ⟨385608538605602154008160625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514144718140802872010880833 385608538605602154008160625)
              ·
                refine ⟨289206403954201615506120469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385608538605602154008160625 289206403954201615506120469)
                ·
                  refine ⟨13556550185353200726849397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 289206403954201615506120469 13556550185353200726849397)
                  ·
                    refine ⟨1270926579876862568142131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13556550185353200726849397 1270926579876862568142131)
                    ·
                      rfl

theorem cell22_3712681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_3712681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712681 prefixEnd_3712681 := by exact prefixLift 3712681
  have htrace : WordTrace (prefixWord ++ tailWord_3712681) baseStart_3712681 baseEnd_3712681 := by
    simpa [prefixWord, tailWord_3712681, baseEnd_3712681] using wordTrace_append hprefix tailTrace_3712681
  have hstable : (prefixWord ++ tailWord_3712681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712681).length < 2 ^ (prefixWord ++ tailWord_3712681).sum := by decide
  have hdescent : baseEnd_3712681 < baseStart_3712681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712696 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 2, 8]
def baseStart_3712696 : Nat := 118140960795 + 3712696 * 2 ^ 59
def prefixEnd_3712696 : Nat := 4983230072969 + 3 ^ 40 * 3712696 * 2
def baseEnd_3712696 : Nat := 1270931714683407529017085

theorem tailTrace_3712696 : CollatzResearch.WordTrace tailWord_3712696 prefixEnd_3712696 1270931714683407529017085 := by
  unfold tailWord_3712696
  simp only [CollatzResearch.WordTrace]
  refine ⟨67706573878771972420190971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90275431838362629893587961 67706573878771972420190971)
  ·
    refine ⟨101559860818157958630286457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67706573878771972420190971 101559860818157958630286457)
    ·
      refine ⟨76169895613618468972714843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101559860818157958630286457 76169895613618468972714843)
      ·
        refine ⟨114254843420427703459072265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76169895613618468972714843 114254843420427703459072265)
        ·
          refine ⟨85691132565320777594304199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114254843420427703459072265 85691132565320777594304199)
          ·
            refine ⟨128536698847981166391456299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85691132565320777594304199 128536698847981166391456299)
            ·
              refine ⟨192805048271971749587184449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128536698847981166391456299 192805048271971749587184449)
              ·
                refine ⟨144603786203978812190388337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192805048271971749587184449 144603786203978812190388337)
                ·
                  refine ⟨108452839652984109142791253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144603786203978812190388337 108452839652984109142791253)
                  ·
                    refine ⟨1270931714683407529017085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108452839652984109142791253 1270931714683407529017085)
                    ·
                      rfl

theorem cell22_3712696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_3712696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712696 prefixEnd_3712696 := by exact prefixLift 3712696
  have htrace : WordTrace (prefixWord ++ tailWord_3712696) baseStart_3712696 baseEnd_3712696 := by
    simpa [prefixWord, tailWord_3712696, baseEnd_3712696] using wordTrace_append hprefix tailTrace_3712696
  have hstable : (prefixWord ++ tailWord_3712696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712696).length < 2 ^ (prefixWord ++ tailWord_3712696).sum := by decide
  have hdescent : baseEnd_3712696 < baseStart_3712696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712805 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 5, 3]
def baseStart_3712805 : Nat := 118140960795 + 3712805 * 2 ^ 59
def prefixEnd_3712805 : Nat := 4983230072969 + 3 ^ 40 * 3712805 * 2
def baseEnd_3712805 : Nat := 1270969027610967578041751

theorem tailTrace_3712805 : CollatzResearch.WordTrace tailWord_3712805 prefixEnd_3712805 1270969027610967578041751 := by
  unfold tailWord_3712805
  simp only [CollatzResearch.WordTrace]
  refine ⟨135417123314149056456099869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90278082209432704304066579 135417123314149056456099869)
  ·
    refine ⟨50781421242805896171037451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135417123314149056456099869 50781421242805896171037451)
    ·
      refine ⟨76172131864208844256556177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50781421242805896171037451 76172131864208844256556177)
      ·
        refine ⟨57129098898156633192417133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76172131864208844256556177 57129098898156633192417133)
        ·
          refine ⟨21423412086808737447156425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57129098898156633192417133 21423412086808737447156425)
          ·
            refine ⟨16067559065106553085367319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21423412086808737447156425 16067559065106553085367319)
            ·
              refine ⟨24101338597659829628050979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16067559065106553085367319 24101338597659829628050979)
              ·
                refine ⟨36152007896489744442076469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24101338597659829628050979 36152007896489744442076469)
                ·
                  refine ⟨3389250740295913541444669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36152007896489744442076469 3389250740295913541444669)
                  ·
                    refine ⟨1270969027610967578041751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3389250740295913541444669 1270969027610967578041751)
                    ·
                      rfl

theorem cell22_3712805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_3712805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712805 prefixEnd_3712805 := by exact prefixLift 3712805
  have htrace : WordTrace (prefixWord ++ tailWord_3712805) baseStart_3712805 baseEnd_3712805 := by
    simpa [prefixWord, tailWord_3712805, baseEnd_3712805] using wordTrace_append hprefix tailTrace_3712805
  have hstable : (prefixWord ++ tailWord_3712805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712805).length < 2 ^ (prefixWord ++ tailWord_3712805).sum := by decide
  have hdescent : baseEnd_3712805 < baseStart_3712805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712835 : List Nat := [1, 1, 1, 3, 1, 5, 3, 2, 5]
def baseStart_3712835 : Nat := 118140960795 + 3712835 * 2 ^ 59
def prefixEnd_3712835 : Nat := 4983230072969 + 3 ^ 40 * 3712835 * 2
def baseEnd_3712835 : Nat := 423659765741352499930553

theorem tailTrace_3712835 : CollatzResearch.WordTrace tailWord_3712835 prefixEnd_3712835 423659765741352499930553 := by
  unfold tailWord_3712835
  simp only [CollatzResearch.WordTrace]
  refine ⟨135418217504040371579691959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90278811669360247719794639 135418217504040371579691959)
  ·
    refine ⟨203127326256060557369537939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135418217504040371579691959 203127326256060557369537939)
    ·
      refine ⟨304690989384090836054306909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203127326256060557369537939 304690989384090836054306909)
      ·
        refine ⟨114259121019034063520365091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304690989384090836054306909 114259121019034063520365091)
        ·
          refine ⟨171388681528551095280547637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114259121019034063520365091 171388681528551095280547637)
          ·
            refine ⟨16067688893301665182551341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171388681528551095280547637 16067688893301665182551341)
            ·
              refine ⟨6025383334988124443456753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16067688893301665182551341 6025383334988124443456753)
              ·
                refine ⟨4519037501241093332592565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6025383334988124443456753 4519037501241093332592565)
                ·
                  refine ⟨423659765741352499930553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4519037501241093332592565 423659765741352499930553)
                  ·
                    rfl

theorem cell22_3712835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 5].length) (baseStart_3712835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712835 prefixEnd_3712835 := by exact prefixLift 3712835
  have htrace : WordTrace (prefixWord ++ tailWord_3712835) baseStart_3712835 baseEnd_3712835 := by
    simpa [prefixWord, tailWord_3712835, baseEnd_3712835] using wordTrace_append hprefix tailTrace_3712835
  have hstable : (prefixWord ++ tailWord_3712835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712835).length < 2 ^ (prefixWord ++ tailWord_3712835).sum := by decide
  have hdescent : baseEnd_3712835 < baseStart_3712835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712850 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_3712850 : Nat := 118140960795 + 3712850 * 2 ^ 59
def prefixEnd_3712850 : Nat := 4983230072969 + 3 ^ 40 * 3712850 * 2
def baseEnd_3712850 : Nat := 1270984432030602460666613

theorem tailTrace_3712850 : CollatzResearch.WordTrace tailWord_3712850 prefixEnd_3712850 1270984432030602460666613 := by
  unfold tailWord_3712850
  simp only [CollatzResearch.WordTrace]
  refine ⟨33854691149746507285372001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90279176399324019427658669 33854691149746507285372001)
  ·
    refine ⟨25391018362309880464029001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33854691149746507285372001 25391018362309880464029001)
    ·
      refine ⟨19043263771732410348021751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25391018362309880464029001 19043263771732410348021751)
      ·
        refine ⟨28564895657598615522032627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19043263771732410348021751 28564895657598615522032627)
        ·
          refine ⟨42847343486397923283048941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28564895657598615522032627 42847343486397923283048941)
          ·
            refine ⟨16067753807399221231143353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42847343486397923283048941 16067753807399221231143353)
            ·
              refine ⟨12050815355549415923357515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16067753807399221231143353 12050815355549415923357515)
              ·
                refine ⟨18076223033324123885036273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12050815355549415923357515 18076223033324123885036273)
                ·
                  refine ⟨13557167274993092913777205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18076223033324123885036273 13557167274993092913777205)
                  ·
                    refine ⟨1270984432030602460666613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13557167274993092913777205 1270984432030602460666613)
                    ·
                      rfl

theorem cell22_3712850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_3712850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712850 prefixEnd_3712850 := by exact prefixLift 3712850
  have htrace : WordTrace (prefixWord ++ tailWord_3712850) baseStart_3712850 baseEnd_3712850 := by
    simpa [prefixWord, tailWord_3712850, baseEnd_3712850] using wordTrace_append hprefix tailTrace_3712850
  have hstable : (prefixWord ++ tailWord_3712850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712850).length < 2 ^ (prefixWord ++ tailWord_3712850).sum := by decide
  have hdescent : baseEnd_3712850 < baseStart_3712850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712925 : List Nat := [1, 4, 2, 1, 2, 2, 2, 8]
def baseStart_3712925 : Nat := 118140960795 + 3712925 * 2 ^ 59
def prefixEnd_3712925 : Nat := 4983230072969 + 3 ^ 40 * 3712925 * 2
def baseEnd_3712925 : Nat := 141223345118147473893487

theorem tailTrace_3712925 : CollatzResearch.WordTrace tailWord_3712925 prefixEnd_3712925 141223345118147473893487 := by
  unfold tailWord_3712925
  simp only [CollatzResearch.WordTrace]
  refine ⟨135421500073714316950468229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90281000049142877966978819 135421500073714316950468229)
  ·
    refine ⟨25391531263821434428212793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135421500073714316950468229 25391531263821434428212793)
    ·
      refine ⟨19043648447866075821159595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25391531263821434428212793 19043648447866075821159595)
      ·
        refine ⟨28565472671799113731739393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19043648447866075821159595 28565472671799113731739393)
        ·
          refine ⟨21424104503849335298804545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28565472671799113731739393 21424104503849335298804545)
          ·
            refine ⟨16068078377887001474103409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21424104503849335298804545 16068078377887001474103409)
            ·
              refine ⟨12051058783415251105577557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16068078377887001474103409 12051058783415251105577557)
              ·
                refine ⟨141223345118147473893487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12051058783415251105577557 141223345118147473893487)
                ·
                  rfl

theorem cell22_3712925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 8].length) (baseStart_3712925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712925 prefixEnd_3712925 := by exact prefixLift 3712925
  have htrace : WordTrace (prefixWord ++ tailWord_3712925) baseStart_3712925 baseEnd_3712925 := by
    simpa [prefixWord, tailWord_3712925, baseEnd_3712925] using wordTrace_append hprefix tailTrace_3712925
  have hstable : (prefixWord ++ tailWord_3712925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712925).length < 2 ^ (prefixWord ++ tailWord_3712925).sum := by decide
  have hdescent : baseEnd_3712925 < baseStart_3712925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712991 : List Nat := [1, 1, 2, 3, 4, 2, 2, 3, 1, 3]
def baseStart_3712991 : Nat := 118140960795 + 3712991 * 2 ^ 59
def prefixEnd_3712991 : Nat := 4983230072969 + 3 ^ 40 * 3712991 * 2
def baseEnd_3712991 : Nat := 1271032699212125092891181

theorem tailTrace_3712991 : CollatzResearch.WordTrace tailWord_3712991 prefixEnd_3712991 1271032699212125092891181 := by
  unfold tailWord_3712991
  simp only [CollatzResearch.WordTrace]
  refine ⟨135423907291475210222370827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90282604860983473481580551 135423907291475210222370827)
  ·
    refine ⟨203135860937212815333556241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135423907291475210222370827 203135860937212815333556241)
    ·
      refine ⟨152351895702909611500167181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203135860937212815333556241 152351895702909611500167181)
      ·
        refine ⟨57131960888591104312562693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152351895702909611500167181 57131960888591104312562693)
        ·
          refine ⟨10712242666610832058605505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57131960888591104312562693 10712242666610832058605505)
          ·
            refine ⟨8034181999958124043954129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10712242666610832058605505 8034181999958124043954129)
            ·
              refine ⟨6025636499968593032965597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8034181999958124043954129 6025636499968593032965597)
              ·
                refine ⟨2259613687488222387362099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6025636499968593032965597 2259613687488222387362099)
                ·
                  refine ⟨3389420531232333581043149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2259613687488222387362099 3389420531232333581043149)
                  ·
                    refine ⟨1271032699212125092891181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3389420531232333581043149 1271032699212125092891181)
                    ·
                      rfl

theorem cell22_3712991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 1, 3].length) (baseStart_3712991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3712991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3712991 prefixEnd_3712991 := by exact prefixLift 3712991
  have htrace : WordTrace (prefixWord ++ tailWord_3712991) baseStart_3712991 baseEnd_3712991 := by
    simpa [prefixWord, tailWord_3712991, baseEnd_3712991] using wordTrace_append hprefix tailTrace_3712991
  have hstable : (prefixWord ++ tailWord_3712991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712991).length < 2 ^ (prefixWord ++ tailWord_3712991).sum := by decide
  have hdescent : baseEnd_3712991 < baseStart_3712991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713081 : List Nat := [1, 2, 1, 5, 3, 1, 1, 3, 2, 3]
def baseStart_3713081 : Nat := 118140960795 + 3713081 * 2 ^ 59
def prefixEnd_3713081 : Nat := 4983230072969 + 3 ^ 40 * 3713081 * 2
def baseEnd_3713081 : Nat := 1271063508051394858140905

theorem tailTrace_3713081 : CollatzResearch.WordTrace tailWord_3713081 prefixEnd_3713081 1271063508051394858140905 := by
  unfold tailWord_3713081
  simp only [CollatzResearch.WordTrace]
  refine ⟨135427189861149155593147097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90284793240766103728764731 135427189861149155593147097)
  ·
    refine ⟨101570392395861866694860323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135427189861149155593147097 101570392395861866694860323)
    ·
      refine ⟨152355588593792800042290485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101570392395861866694860323 152355588593792800042290485)
      ·
        refine ⟨14283336430668075003964733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152355588593792800042290485 14283336430668075003964733)
        ·
          refine ⟨5356251161500528126486775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14283336430668075003964733 5356251161500528126486775)
          ·
            refine ⟨8034376742250792189730163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5356251161500528126486775 8034376742250792189730163)
            ·
              refine ⟨12051565113376188284595245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8034376742250792189730163 12051565113376188284595245)
              ·
                refine ⟨4519336917516070606723217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12051565113376188284595245 4519336917516070606723217)
                ·
                  refine ⟨3389502688137052955042413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4519336917516070606723217 3389502688137052955042413)
                  ·
                    refine ⟨1271063508051394858140905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3389502688137052955042413 1271063508051394858140905)
                    ·
                      rfl

theorem cell22_3713081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 3].length) (baseStart_3713081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713081 prefixEnd_3713081 := by exact prefixLift 3713081
  have htrace : WordTrace (prefixWord ++ tailWord_3713081) baseStart_3713081 baseEnd_3713081 := by
    simpa [prefixWord, tailWord_3713081, baseEnd_3713081] using wordTrace_append hprefix tailTrace_3713081
  have hstable : (prefixWord ++ tailWord_3713081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713081).length < 2 ^ (prefixWord ++ tailWord_3713081).sum := by decide
  have hdescent : baseEnd_3713081 < baseStart_3713081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713094 : List Nat := [6, 1, 1, 1, 1, 1, 1, 10]
def baseStart_3713094 : Nat := 118140960795 + 3713094 * 2 ^ 59
def prefixEnd_3713094 : Nat := 4983230072969 + 3 ^ 40 * 3713094 * 2
def baseEnd_3713094 : Nat := 141229773135229684173985

theorem tailTrace_3713094 : CollatzResearch.WordTrace tailWord_3713094 prefixEnd_3713094 141229773135229684173985 := by
  unfold tailWord_3713094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4232114500315689337917823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90285109340068039208913557 4232114500315689337917823)
  ·
    refine ⟨6348171750473534006876735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4232114500315689337917823 6348171750473534006876735)
    ·
      refine ⟨9522257625710301010315103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6348171750473534006876735 9522257625710301010315103)
      ·
        refine ⟨14283386438565451515472655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9522257625710301010315103 14283386438565451515472655)
        ·
          refine ⟨21425079657848177273208983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14283386438565451515472655 21425079657848177273208983)
          ·
            refine ⟨32137619486772265909813475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21425079657848177273208983 32137619486772265909813475)
            ·
              refine ⟨48206429230158398864720213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32137619486772265909813475 48206429230158398864720213)
              ·
                refine ⟨141229773135229684173985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48206429230158398864720213 141229773135229684173985)
                ·
                  rfl

theorem cell22_3713094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_3713094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713094 prefixEnd_3713094 := by exact prefixLift 3713094
  have htrace : WordTrace (prefixWord ++ tailWord_3713094) baseStart_3713094 baseEnd_3713094 := by
    simpa [prefixWord, tailWord_3713094, baseEnd_3713094] using wordTrace_append hprefix tailTrace_3713094
  have hstable : (prefixWord ++ tailWord_3713094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713094).length < 2 ^ (prefixWord ++ tailWord_3713094).sum := by decide
  have hdescent : baseEnd_3713094 < baseStart_3713094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713137 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 2, 5]
def baseStart_3713137 : Nat := 118140960795 + 3713137 * 2 ^ 59
def prefixEnd_3713137 : Nat := 4983230072969 + 3 ^ 40 * 3713137 * 2
def baseEnd_3713137 : Nat := 1271082677995829378740733

theorem tailTrace_3713137 : CollatzResearch.WordTrace tailWord_3713137 prefixEnd_3713137 1271082677995829378740733 := by
  unfold tailWord_3713137
  simp only [CollatzResearch.WordTrace]
  refine ⟨135429232348946277157185665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90286154899297518104790443 135429232348946277157185665)
  ·
    refine ⟨101571924261709707867889249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135429232348946277157185665 101571924261709707867889249)
    ·
      refine ⟨76178943196282280900916937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101571924261709707867889249 76178943196282280900916937)
      ·
        refine ⟨57134207397211710675687703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76178943196282280900916937 57134207397211710675687703)
        ·
          refine ⟨85701311095817566013531555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57134207397211710675687703 85701311095817566013531555)
          ·
            refine ⟨128551966643726349020297333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85701311095817566013531555 128551966643726349020297333)
            ·
              refine ⟨12051746872849345220652875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128551966643726349020297333 12051746872849345220652875)
              ·
                refine ⟨18077620309274017830979313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12051746872849345220652875 18077620309274017830979313)
                ·
                  refine ⟨13558215231955513373234485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18077620309274017830979313 13558215231955513373234485)
                  ·
                    refine ⟨1271082677995829378740733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13558215231955513373234485 1271082677995829378740733)
                    ·
                      rfl

theorem cell22_3713137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_3713137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713137 prefixEnd_3713137 := by exact prefixLift 3713137
  have htrace : WordTrace (prefixWord ++ tailWord_3713137) baseStart_3713137 baseEnd_3713137 := by
    simpa [prefixWord, tailWord_3713137, baseEnd_3713137] using wordTrace_append hprefix tailTrace_3713137
  have hstable : (prefixWord ++ tailWord_3713137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713137).length < 2 ^ (prefixWord ++ tailWord_3713137).sum := by decide
  have hdescent : baseEnd_3713137 < baseStart_3713137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713184 : List Nat := [2, 1, 1, 4, 2, 3, 2, 1, 6]
def baseStart_3713184 : Nat := 118140960795 + 3713184 * 2 ^ 59
def prefixEnd_3713184 : Nat := 4983230072969 + 3 ^ 40 * 3713184 * 2
def baseEnd_3713184 : Nat := 423699589018778974271863

theorem tailTrace_3713184 : CollatzResearch.WordTrace tailWord_3713184 prefixEnd_3713184 423699589018778974271863 := by
  unfold tailWord_3713184
  simp only [CollatzResearch.WordTrace]
  refine ⟨67715473289888002092073303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90287297719850669456097737 67715473289888002092073303)
  ·
    refine ⟨101573209934832003138109955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67715473289888002092073303 101573209934832003138109955)
    ·
      refine ⟨152359814902248004707164933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101573209934832003138109955 152359814902248004707164933)
      ·
        refine ⟨28567465294171500882593425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152359814902248004707164933 28567465294171500882593425)
        ·
          refine ⟨21425598970628625661945069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28567465294171500882593425 21425598970628625661945069)
          ·
            refine ⟨8034599613985734623229401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21425598970628625661945069 8034599613985734623229401)
            ·
              refine ⟨6025949710489300967422051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8034599613985734623229401 6025949710489300967422051)
              ·
                refine ⟨9038924565733951451133077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6025949710489300967422051 9038924565733951451133077)
                ·
                  refine ⟨423699589018778974271863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9038924565733951451133077 423699589018778974271863)
                  ·
                    rfl

theorem cell22_3713184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 6].length) (baseStart_3713184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713184 prefixEnd_3713184 := by exact prefixLift 3713184
  have htrace : WordTrace (prefixWord ++ tailWord_3713184) baseStart_3713184 baseEnd_3713184 := by
    simpa [prefixWord, tailWord_3713184, baseEnd_3713184] using wordTrace_append hprefix tailTrace_3713184
  have hstable : (prefixWord ++ tailWord_3713184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713184).length < 2 ^ (prefixWord ++ tailWord_3713184).sum := by decide
  have hdescent : baseEnd_3713184 < baseStart_3713184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713304 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 5, 4]
def baseStart_3713304 : Nat := 118140960795 + 3713304 * 2 ^ 59
def prefixEnd_3713304 : Nat := 4983230072969 + 3 ^ 40 * 3713304 * 2
def baseEnd_3713304 : Nat := 1271139845508696609815221

theorem tailTrace_3713304 : CollatzResearch.WordTrace tailWord_3713304 prefixEnd_3713304 1271139845508696609815221 := by
  unfold tailWord_3713304
  simp only [CollatzResearch.WordTrace]
  refine ⟨67717661669670632339257483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90290215559560843119009977 67717661669670632339257483)
  ·
    refine ⟨101576492504505948508886225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67717661669670632339257483 101576492504505948508886225)
    ·
      refine ⟨76182369378379461381664669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101576492504505948508886225 76182369378379461381664669)
      ·
        refine ⟨28568388516892298018124251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76182369378379461381664669 28568388516892298018124251)
        ·
          refine ⟨42852582775338447027186377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28568388516892298018124251 42852582775338447027186377)
          ·
            refine ⟨32139437081503835270389783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42852582775338447027186377 32139437081503835270389783)
            ·
              refine ⟨48209155622255752905584675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32139437081503835270389783 48209155622255752905584675)
              ·
                refine ⟨72313733433383629358377013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48209155622255752905584675 72313733433383629358377013)
                ·
                  refine ⟨6779412509379715252347845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72313733433383629358377013 6779412509379715252347845)
                  ·
                    refine ⟨1271139845508696609815221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6779412509379715252347845 1271139845508696609815221)
                    ·
                      rfl

theorem cell22_3713304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_3713304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713304 prefixEnd_3713304 := by exact prefixLift 3713304
  have htrace : WordTrace (prefixWord ++ tailWord_3713304) baseStart_3713304 baseEnd_3713304 := by
    simpa [prefixWord, tailWord_3713304, baseEnd_3713304] using wordTrace_append hprefix tailTrace_3713304
  have hstable : (prefixWord ++ tailWord_3713304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713304).length < 2 ^ (prefixWord ++ tailWord_3713304).sum := by decide
  have hdescent : baseEnd_3713304 < baseStart_3713304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713306 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 2, 5]
def baseStart_3713306 : Nat := 118140960795 + 3713306 * 2 ^ 59
def prefixEnd_3713306 : Nat := 4983230072969 + 3 ^ 40 * 3713306 * 2
def baseEnd_3713306 : Nat := 1271140530149569271265215

theorem tailTrace_3713306 : CollatzResearch.WordTrace tailWord_3713306 prefixEnd_3713306 1271140530149569271265215 := by
  unfold tailWord_3713306
  simp only [CollatzResearch.WordTrace]
  refine ⟨33858849071333504755021943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90290264190222679346725181 33858849071333504755021943)
  ·
    refine ⟨50788273607000257132532915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33858849071333504755021943 50788273607000257132532915)
    ·
      refine ⟨76182410410500385698799373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50788273607000257132532915 76182410410500385698799373)
      ·
        refine ⟨28568403903937644637049765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76182410410500385698799373 28568403903937644637049765)
        ·
          refine ⟨5356575731988308369446831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28568403903937644637049765 5356575731988308369446831)
          ·
            refine ⟨8034863597982462554170247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5356575731988308369446831 8034863597982462554170247)
            ·
              refine ⟨12052295396973693831255371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8034863597982462554170247 12052295396973693831255371)
              ·
                refine ⟨18078443095460540746883057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12052295396973693831255371 18078443095460540746883057)
                ·
                  refine ⟨13558832321595405560162293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18078443095460540746883057 13558832321595405560162293)
                  ·
                    refine ⟨1271140530149569271265215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13558832321595405560162293 1271140530149569271265215)
                    ·
                      rfl

theorem cell22_3713306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_3713306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713306 prefixEnd_3713306 := by exact prefixLift 3713306
  have htrace : WordTrace (prefixWord ++ tailWord_3713306) baseStart_3713306 baseEnd_3713306 := by
    simpa [prefixWord, tailWord_3713306, baseEnd_3713306] using wordTrace_append hprefix tailTrace_3713306
  have hstable : (prefixWord ++ tailWord_3713306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713306).length < 2 ^ (prefixWord ++ tailWord_3713306).sum := by decide
  have hdescent : baseEnd_3713306 < baseStart_3713306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713336 : List Nat := [2, 1, 2, 1, 3, 1, 3, 5, 4]
def baseStart_3713336 : Nat := 118140960795 + 3713336 * 2 ^ 59
def prefixEnd_3713336 : Nat := 4983230072969 + 3 ^ 40 * 3713336 * 2
def baseEnd_3713336 : Nat := 423716933254219731005041

theorem tailTrace_3713336 : CollatzResearch.WordTrace tailWord_3713336 prefixEnd_3713336 423716933254219731005041 := by
  unfold tailWord_3713336
  simp only [CollatzResearch.WordTrace]
  refine ⟨67718245237612667071839931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90290993650150222762453241 67718245237612667071839931)
  ·
    refine ⟨101577367856419000607759897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67718245237612667071839931 101577367856419000607759897)
    ·
      refine ⟨76183025892314250455819923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101577367856419000607759897 76183025892314250455819923)
      ·
        refine ⟨114274538838471375683729885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76183025892314250455819923 114274538838471375683729885)
        ·
          refine ⟨42852952064426765881398707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114274538838471375683729885 42852952064426765881398707)
          ·
            refine ⟨64279428096640148822098061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42852952064426765881398707 64279428096640148822098061)
            ·
              refine ⟨24104785536240055808286773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64279428096640148822098061 24104785536240055808286773)
              ·
                refine ⟨2259823644022505232026885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24104785536240055808286773 2259823644022505232026885)
                ·
                  refine ⟨423716933254219731005041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2259823644022505232026885 423716933254219731005041)
                  ·
                    rfl

theorem cell22_3713336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 4].length) (baseStart_3713336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713336 prefixEnd_3713336 := by exact prefixLift 3713336
  have htrace : WordTrace (prefixWord ++ tailWord_3713336) baseStart_3713336 baseEnd_3713336 := by
    simpa [prefixWord, tailWord_3713336, baseEnd_3713336] using wordTrace_append hprefix tailTrace_3713336
  have hstable : (prefixWord ++ tailWord_3713336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713336).length < 2 ^ (prefixWord ++ tailWord_3713336).sum := by decide
  have hdescent : baseEnd_3713336 < baseStart_3713336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713338 : List Nat := [3, 1, 1, 1, 4, 2, 4, 1, 1, 4]
def baseStart_3713338 : Nat := 118140960795 + 3713338 * 2 ^ 59
def prefixEnd_3713338 : Nat := 4983230072969 + 3 ^ 40 * 3713338 * 2
def baseEnd_3713338 : Nat := 1271151484403531854465117

theorem tailTrace_3713338 : CollatzResearch.WordTrace tailWord_3713338 prefixEnd_3713338 1271151484403531854465117 := by
  unfold tailWord_3713338
  simp only [CollatzResearch.WordTrace]
  refine ⟨33859140855304522121313167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90291042280812058990168445 33859140855304522121313167)
  ·
    refine ⟨50788711282956783181969751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33859140855304522121313167 50788711282956783181969751)
    ·
      refine ⟨76183066924435174772954627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50788711282956783181969751 76183066924435174772954627)
      ·
        refine ⟨114274600386652762159431941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76183066924435174772954627 114274600386652762159431941)
        ·
          refine ⟨21426487572497392904893489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114274600386652762159431941 21426487572497392904893489)
          ·
            refine ⟨16069865679373044678670117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21426487572497392904893489 16069865679373044678670117)
            ·
              refine ⟨3013099814882445877250647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16069865679373044678670117 3013099814882445877250647)
              ·
                refine ⟨4519649722323668815875971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3013099814882445877250647 4519649722323668815875971)
                ·
                  refine ⟨6779474583485503223813957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4519649722323668815875971 6779474583485503223813957)
                  ·
                    refine ⟨1271151484403531854465117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6779474583485503223813957 1271151484403531854465117)
                    ·
                      rfl

theorem cell22_3713338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 1, 4].length) (baseStart_3713338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713338 prefixEnd_3713338 := by exact prefixLift 3713338
  have htrace : WordTrace (prefixWord ++ tailWord_3713338) baseStart_3713338 baseEnd_3713338 := by
    simpa [prefixWord, tailWord_3713338, baseEnd_3713338] using wordTrace_append hprefix tailTrace_3713338
  have hstable : (prefixWord ++ tailWord_3713338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713338).length < 2 ^ (prefixWord ++ tailWord_3713338).sum := by decide
  have hdescent : baseEnd_3713338 < baseStart_3713338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713351 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 4, 3]
def baseStart_3713351 : Nat := 118140960795 + 3713351 * 2 ^ 59
def prefixEnd_3713351 : Nat := 4983230072969 + 3 ^ 40 * 3713351 * 2
def baseEnd_3713351 : Nat := 1271155934569204153890077

theorem tailTrace_3713351 : CollatzResearch.WordTrace tailWord_3713351 prefixEnd_3713351 1271155934569204153890077 := by
  unfold tailWord_3713351
  simp only [CollatzResearch.WordTrace]
  refine ⟨135437037570170991705475907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90291358380113994470317271 135437037570170991705475907)
  ·
    refine ⟨203155556355256487558213861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135437037570170991705475907 203155556355256487558213861)
    ·
      refine ⟨38091666816610591417165099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203155556355256487558213861 38091666816610591417165099)
      ·
        refine ⟨57137500224915887125747649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38091666816610591417165099 57137500224915887125747649)
        ·
          refine ⟨42853125168686915344310737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57137500224915887125747649 42853125168686915344310737)
          ·
            refine ⟨32139843876515186508233053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42853125168686915344310737 32139843876515186508233053)
            ·
              refine ⟨12052441453693194940587395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32139843876515186508233053 12052441453693194940587395)
              ·
                refine ⟨18078662180539792410881093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12052441453693194940587395 18078662180539792410881093)
                ·
                  refine ⟨3389749158851211077040205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18078662180539792410881093 3389749158851211077040205)
                  ·
                    refine ⟨1271155934569204153890077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3389749158851211077040205 1271155934569204153890077)
                    ·
                      rfl

theorem cell22_3713351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_3713351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713351 prefixEnd_3713351 := by exact prefixLift 3713351
  have htrace : WordTrace (prefixWord ++ tailWord_3713351) baseStart_3713351 baseEnd_3713351 := by
    simpa [prefixWord, tailWord_3713351, baseEnd_3713351] using wordTrace_append hprefix tailTrace_3713351
  have hstable : (prefixWord ++ tailWord_3713351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713351).length < 2 ^ (prefixWord ++ tailWord_3713351).sum := by decide
  have hdescent : baseEnd_3713351 < baseStart_3713351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713379 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 2, 7]
def baseStart_3713379 : Nat := 118140960795 + 3713379 * 2 ^ 59
def prefixEnd_3713379 : Nat := 4983230072969 + 3 ^ 40 * 3713379 * 2
def baseEnd_3713379 : Nat := 1271165519541421414189991

theorem tailTrace_3713379 : CollatzResearch.WordTrace tailWord_3713379 prefixEnd_3713379 1271165519541421414189991 := by
  unfold tailWord_3713379
  simp only [CollatzResearch.WordTrace]
  refine ⟨135438058814069552487495191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90292039209379701658330127 135438058814069552487495191)
  ·
    refine ⟨203157088221104328731242787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135438058814069552487495191 203157088221104328731242787)
    ·
      refine ⟨304735632331656493096864181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203157088221104328731242787 304735632331656493096864181)
      ·
        refine ⟨28568965531092796227831017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 304735632331656493096864181 28568965531092796227831017)
        ·
          refine ⟨21426724148319597170873263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28568965531092796227831017 21426724148319597170873263)
          ·
            refine ⟨32140086222479395756309895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21426724148319597170873263 32140086222479395756309895)
            ·
              refine ⟨48210129333719093634464843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32140086222479395756309895 48210129333719093634464843)
              ·
                refine ⟨72315194000578640451697265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48210129333719093634464843 72315194000578640451697265)
                ·
                  refine ⟨54236395500433980338772949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72315194000578640451697265 54236395500433980338772949)
                  ·
                    refine ⟨1271165519541421414189991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54236395500433980338772949 1271165519541421414189991)
                    ·
                      rfl

theorem cell22_3713379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 7].length) (baseStart_3713379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713379 prefixEnd_3713379 := by exact prefixLift 3713379
  have htrace : WordTrace (prefixWord ++ tailWord_3713379) baseStart_3713379 baseEnd_3713379 := by
    simpa [prefixWord, tailWord_3713379, baseEnd_3713379] using wordTrace_append hprefix tailTrace_3713379
  have hstable : (prefixWord ++ tailWord_3713379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713379).length < 2 ^ (prefixWord ++ tailWord_3713379).sum := by decide
  have hdescent : baseEnd_3713379 < baseStart_3713379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713381 : List Nat := [1, 3, 1, 3, 1, 3, 4, 6]
def baseStart_3713381 : Nat := 118140960795 + 3713381 * 2 ^ 59
def prefixEnd_3713381 : Nat := 4983230072969 + 3 ^ 40 * 3713381 * 2
def baseEnd_3713381 : Nat := 141240689353588230626665

theorem tailTrace_3713381 : CollatzResearch.WordTrace tailWord_3713381 prefixEnd_3713381 141240689353588230626665 := by
  unfold tailWord_3713381
  simp only [CollatzResearch.WordTrace]
  refine ⟨135438131760062306829067997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90292087840041537886045331 135438131760062306829067997)
  ·
    refine ⟨50789299410023365060900499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135438131760062306829067997 50789299410023365060900499)
    ·
      refine ⟨76183949115035047591350749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50789299410023365060900499 76183949115035047591350749)
      ·
        refine ⟨28568980918138142846756531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76183949115035047591350749 28568980918138142846756531)
        ·
          refine ⟨42853471377207214270134797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28568980918138142846756531 42853471377207214270134797)
          ·
            refine ⟨16070051766452705351300549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42853471377207214270134797 16070051766452705351300549)
            ·
              refine ⟨3013134706209882253368853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16070051766452705351300549 3013134706209882253368853)
              ·
                refine ⟨141240689353588230626665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3013134706209882253368853 141240689353588230626665)
                ·
                  rfl

theorem cell22_3713381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 6].length) (baseStart_3713381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713381 prefixEnd_3713381 := by exact prefixLift 3713381
  have htrace : WordTrace (prefixWord ++ tailWord_3713381) baseStart_3713381 baseEnd_3713381 := by
    simpa [prefixWord, tailWord_3713381, baseEnd_3713381] using wordTrace_append hprefix tailTrace_3713381
  have hstable : (prefixWord ++ tailWord_3713381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713381).length < 2 ^ (prefixWord ++ tailWord_3713381).sum := by decide
  have hdescent : baseEnd_3713381 < baseStart_3713381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713507 : List Nat := [1, 1, 1, 6, 3, 2, 2, 1, 1, 4]
def baseStart_3713507 : Nat := 118140960795 + 3713507 * 2 ^ 59
def prefixEnd_3713507 : Nat := 4983230072969 + 3 ^ 40 * 3713507 * 2
def baseEnd_3713507 : Nat := 1271209336557271746989599

theorem tailTrace_3713507 : CollatzResearch.WordTrace tailWord_3713507 prefixEnd_3713507 1271209336557271746989599 := by
  unfold tailWord_3713507
  simp only [CollatzResearch.WordTrace]
  refine ⟨135442727357605830348154775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90295151571737220232103183 135442727357605830348154775)
  ·
    refine ⟨203164091036408745522232163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135442727357605830348154775 203164091036408745522232163)
    ·
      refine ⟨304746136554613118283348245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203164091036408745522232163 304746136554613118283348245)
      ·
        refine ⟨14284975150997489919531949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 304746136554613118283348245 14284975150997489919531949)
        ·
          refine ⟨5356865681624058719824481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14284975150997489919531949 5356865681624058719824481)
          ·
            refine ⟨4017649261218044039868361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5356865681624058719824481 4017649261218044039868361)
            ·
              refine ⟨3013236945913533029901271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4017649261218044039868361 3013236945913533029901271)
              ·
                refine ⟨4519855418870299544851907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3013236945913533029901271 4519855418870299544851907)
                ·
                  refine ⟨6779783128305449317277861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4519855418870299544851907 6779783128305449317277861)
                  ·
                    refine ⟨1271209336557271746989599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6779783128305449317277861 1271209336557271746989599)
                    ·
                      rfl

theorem cell22_3713507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 1, 4].length) (baseStart_3713507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713507 prefixEnd_3713507 := by exact prefixLift 3713507
  have htrace : WordTrace (prefixWord ++ tailWord_3713507) baseStart_3713507 baseEnd_3713507 := by
    simpa [prefixWord, tailWord_3713507, baseEnd_3713507] using wordTrace_append hprefix tailTrace_3713507
  have hstable : (prefixWord ++ tailWord_3713507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713507).length < 2 ^ (prefixWord ++ tailWord_3713507).sum := by decide
  have hdescent : baseEnd_3713507 < baseStart_3713507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713537 : List Nat := [1, 2, 4, 1, 3, 2, 3, 1, 2, 3]
def baseStart_3713537 : Nat := 118140960795 + 3713537 * 2 ^ 59
def prefixEnd_3713537 : Nat := 4983230072969 + 3 ^ 40 * 3713537 * 2
def baseEnd_3713537 : Nat := 1271219606170361668739507

theorem tailTrace_3713537 : CollatzResearch.WordTrace tailWord_3713537 prefixEnd_3713537 1271219606170361668739507 := by
  unfold tailWord_3713537
  simp only [CollatzResearch.WordTrace]
  refine ⟨135443821547497145471746865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90295881031664763647831243 135443821547497145471746865)
  ·
    refine ⟨101582866160622859103810149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135443821547497145471746865 101582866160622859103810149)
    ·
      refine ⟨19046787405116786081964403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101582866160622859103810149 19046787405116786081964403)
      ·
        refine ⟨28570181107675179122946605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19046787405116786081964403 28570181107675179122946605)
        ·
          refine ⟨10713817915378192171104977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28570181107675179122946605 10713817915378192171104977)
          ·
            refine ⟨8035363436533644128328733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10713817915378192171104977 8035363436533644128328733)
            ·
              refine ⟨3013261288700116548123275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8035363436533644128328733 3013261288700116548123275)
              ·
                refine ⟨4519891933050174822184913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3013261288700116548123275 4519891933050174822184913)
                ·
                  refine ⟨3389918949787631116638685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4519891933050174822184913 3389918949787631116638685)
                  ·
                    refine ⟨1271219606170361668739507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3389918949787631116638685 1271219606170361668739507)
                    ·
                      rfl

theorem cell22_3713537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_3713537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713537 prefixEnd_3713537 := by exact prefixLift 3713537
  have htrace : WordTrace (prefixWord ++ tailWord_3713537) baseStart_3713537 baseEnd_3713537 := by
    simpa [prefixWord, tailWord_3713537, baseEnd_3713537] using wordTrace_append hprefix tailTrace_3713537
  have hstable : (prefixWord ++ tailWord_3713537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713537).length < 2 ^ (prefixWord ++ tailWord_3713537).sum := by decide
  have hdescent : baseEnd_3713537 < baseStart_3713537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713550 : List Nat := [4, 1, 1, 2, 3, 3, 2, 6]
def baseStart_3713550 : Nat := 118140960795 + 3713550 * 2 ^ 59
def prefixEnd_3713550 : Nat := 4983230072969 + 3 ^ 40 * 3713550 * 2
def baseEnd_3713550 : Nat := 141247117370670440907163

theorem tailTrace_3713550 : CollatzResearch.WordTrace tailWord_3713550 prefixEnd_3713550 141247117370670440907163 := by
  unfold tailWord_3713550
  simp only [CollatzResearch.WordTrace]
  refine ⟨16930536962056256086496263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90296197130966699127980069 16930536962056256086496263)
  ·
    refine ⟨25395805443084384129744395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16930536962056256086496263 25395805443084384129744395)
    ·
      refine ⟨38093708164626576194616593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25395805443084384129744395 38093708164626576194616593)
      ·
        refine ⟨28570281123469932145962445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38093708164626576194616593 28570281123469932145962445)
        ·
          refine ⟨10713855421301224554735917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28570281123469932145962445 10713855421301224554735917)
          ·
            refine ⟨4017695782987959208025969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10713855421301224554735917 4017695782987959208025969)
            ·
              refine ⟨3013271837240969406019477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4017695782987959208025969 3013271837240969406019477)
              ·
                refine ⟨141247117370670440907163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3013271837240969406019477 141247117370670440907163)
                ·
                  rfl

theorem cell22_3713550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_3713550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713550 prefixEnd_3713550 := by exact prefixLift 3713550
  have htrace : WordTrace (prefixWord ++ tailWord_3713550) baseStart_3713550 baseEnd_3713550 := by
    simpa [prefixWord, tailWord_3713550, baseEnd_3713550] using wordTrace_append hprefix tailTrace_3713550
  have hstable : (prefixWord ++ tailWord_3713550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713550).length < 2 ^ (prefixWord ++ tailWord_3713550).sum := by decide
  have hdescent : baseEnd_3713550 < baseStart_3713550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713578 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 7]
def baseStart_3713578 : Nat := 118140960795 + 3713578 * 2 ^ 59
def prefixEnd_3713578 : Nat := 4983230072969 + 3 ^ 40 * 3713578 * 2
def baseEnd_3713578 : Nat := 423744547102750409488127

theorem tailTrace_3713578 : CollatzResearch.WordTrace tailWord_3713578 prefixEnd_3713578 423744547102750409488127 := by
  unfold tailWord_3713578
  simp only [CollatzResearch.WordTrace]
  refine ⟨33861329235087152368497347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90296877960232406315992925 33861329235087152368497347)
  ·
    refine ⟨50791993852630728552746021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33861329235087152368497347 50791993852630728552746021)
    ·
      refine ⟨9523498847368261603639879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50791993852630728552746021 9523498847368261603639879)
      ·
        refine ⟨14285248271052392405459819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9523498847368261603639879 14285248271052392405459819)
        ·
          refine ⟨21427872406578588608189729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14285248271052392405459819 21427872406578588608189729)
          ·
            refine ⟨16070904304933941456142297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21427872406578588608189729 16070904304933941456142297)
            ·
              refine ⟨12053178228700456092106723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16070904304933941456142297 12053178228700456092106723)
              ·
                refine ⟨18079767343050684138160085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12053178228700456092106723 18079767343050684138160085)
                ·
                  refine ⟨423744547102750409488127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18079767343050684138160085 423744547102750409488127)
                  ·
                    rfl

theorem cell22_3713578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_3713578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713578 prefixEnd_3713578 := by exact prefixLift 3713578
  have htrace : WordTrace (prefixWord ++ tailWord_3713578) baseStart_3713578 baseEnd_3713578 := by
    simpa [prefixWord, tailWord_3713578, baseEnd_3713578] using wordTrace_append hprefix tailTrace_3713578
  have hstable : (prefixWord ++ tailWord_3713578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713578).length < 2 ^ (prefixWord ++ tailWord_3713578).sum := by decide
  have hdescent : baseEnd_3713578 < baseStart_3713578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713588 : List Nat := [2, 5, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_3713588 : Nat := 118140960795 + 3713588 * 2 ^ 59
def prefixEnd_3713588 : Nat := 4983230072969 + 3 ^ 40 * 3713588 * 2
def baseEnd_3713588 : Nat := 1271237064512614535714351

theorem tailTrace_3713588 : CollatzResearch.WordTrace tailWord_3713588 prefixEnd_3713588 1271237064512614535714351 := by
  unfold tailWord_3713588
  simp only [CollatzResearch.WordTrace]
  refine ⟨67722840835156190590926709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90297121113541587454568945 67722840835156190590926709)
  ·
    refine ⟨6349016328295892867899379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67722840835156190590926709 6349016328295892867899379)
    ·
      refine ⟨9523524492443839301849069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6349016328295892867899379 9523524492443839301849069)
      ·
        refine ⟨3571321684666439738193401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9523524492443839301849069 3571321684666439738193401)
        ·
          refine ⟨2678491263499829803645051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3571321684666439738193401 2678491263499829803645051)
          ·
            refine ⟨4017736895249744705467577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2678491263499829803645051 4017736895249744705467577)
            ·
              refine ⟨3013302671437308529100683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4017736895249744705467577 3013302671437308529100683)
              ·
                refine ⟨4519954007155962793651025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3013302671437308529100683 4519954007155962793651025)
                ·
                  refine ⟨3389965505366972095238269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4519954007155962793651025 3389965505366972095238269)
                  ·
                    refine ⟨1271237064512614535714351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3389965505366972095238269 1271237064512614535714351)
                    ·
                      rfl

theorem cell22_3713588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_3713588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713588 prefixEnd_3713588 := by exact prefixLift 3713588
  have htrace : WordTrace (prefixWord ++ tailWord_3713588) baseStart_3713588 baseEnd_3713588 := by
    simpa [prefixWord, tailWord_3713588, baseEnd_3713588] using wordTrace_append hprefix tailTrace_3713588
  have hstable : (prefixWord ++ tailWord_3713588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713588).length < 2 ^ (prefixWord ++ tailWord_3713588).sum := by decide
  have hdescent : baseEnd_3713588 < baseStart_3713588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713651 : List Nat := [1, 1, 1, 2, 2, 1, 1, 13]
def baseStart_3713651 : Nat := 118140960795 + 3713651 * 2 ^ 59
def prefixEnd_3713651 : Nat := 4983230072969 + 3 ^ 40 * 3713651 * 2
def baseEnd_3713651 : Nat := 141250958966678152376573

theorem tailTrace_3713651 : CollatzResearch.WordTrace tailWord_3713651 prefixEnd_3713651 141250958966678152376573 := by
  unfold tailWord_3713651
  simp only [CollatzResearch.WordTrace]
  refine ⟨135447979469084142941396807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90298652979389428627597871 135447979469084142941396807)
  ·
    refine ⟨203171969203626214412095211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135447979469084142941396807 203171969203626214412095211)
    ·
      refine ⟨304757953805439321618142817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203171969203626214412095211 304757953805439321618142817)
      ·
        refine ⟨228568465354079491213607113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304757953805439321618142817 228568465354079491213607113)
        ·
          refine ⟨171426349015559618410205335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228568465354079491213607113 171426349015559618410205335)
          ·
            refine ⟨257139523523339427615308003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171426349015559618410205335 257139523523339427615308003)
            ·
              refine ⟨385709285285009141422962005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257139523523339427615308003 385709285285009141422962005)
              ·
                refine ⟨141250958966678152376573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 385709285285009141422962005 141250958966678152376573)
                ·
                  rfl

theorem cell22_3713651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 13].length) (baseStart_3713651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713651 prefixEnd_3713651 := by exact prefixLift 3713651
  have htrace : WordTrace (prefixWord ++ tailWord_3713651) baseStart_3713651 baseEnd_3713651 := by
    simpa [prefixWord, tailWord_3713651, baseEnd_3713651] using wordTrace_append hprefix tailTrace_3713651
  have hstable : (prefixWord ++ tailWord_3713651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713651).length < 2 ^ (prefixWord ++ tailWord_3713651).sum := by decide
  have hdescent : baseEnd_3713651 < baseStart_3713651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713655 : List Nat := [1, 1, 3, 1, 1, 3, 4, 3, 2, 3]
def baseStart_3713655 : Nat := 118140960795 + 3713655 * 2 ^ 59
def prefixEnd_3713655 : Nat := 4983230072969 + 3 ^ 40 * 3713655 * 2
def baseEnd_3713655 : Nat := 1271259999981848694289145

theorem tailTrace_3713655 : CollatzResearch.WordTrace tailWord_3713655 prefixEnd_3713655 1271259999981848694289145 := by
  unfold tailWord_3713655
  simp only [CollatzResearch.WordTrace]
  refine ⟨135448125361069651624542419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90298750240713101083028279 135448125361069651624542419)
  ·
    refine ⟨203172188041604477436813629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135448125361069651624542419 203172188041604477436813629)
    ·
      refine ⟨76189570515601679038805111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203172188041604477436813629 76189570515601679038805111)
      ·
        refine ⟨114284355773402518558207667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76189570515601679038805111 114284355773402518558207667)
        ·
          refine ⟨171426533660103777837311501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114284355773402518558207667 171426533660103777837311501)
          ·
            refine ⟨64284950122538916688991813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171426533660103777837311501 64284950122538916688991813)
            ·
              refine ⟨12053428147976046879185965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64284950122538916688991813 12053428147976046879185965)
              ·
                refine ⟨4520035555491017579694737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12053428147976046879185965 4520035555491017579694737)
                ·
                  refine ⟨3390026666618263184771053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4520035555491017579694737 3390026666618263184771053)
                  ·
                    refine ⟨1271259999981848694289145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3390026666618263184771053 1271259999981848694289145)
                    ·
                      rfl

theorem cell22_3713655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_3713655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713655 prefixEnd_3713655 := by exact prefixLift 3713655
  have htrace : WordTrace (prefixWord ++ tailWord_3713655) baseStart_3713655 baseEnd_3713655 := by
    simpa [prefixWord, tailWord_3713655, baseEnd_3713655] using wordTrace_append hprefix tailTrace_3713655
  have hstable : (prefixWord ++ tailWord_3713655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713655).length < 2 ^ (prefixWord ++ tailWord_3713655).sum := by decide
  have hdescent : baseEnd_3713655 < baseStart_3713655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713706 : List Nat := [3, 1, 5, 2, 2, 1, 1, 1, 1, 5]
def baseStart_3713706 : Nat := 118140960795 + 3713706 * 2 ^ 59
def prefixEnd_3713706 : Nat := 4983230072969 + 3 ^ 40 * 3713706 * 2
def baseEnd_3713706 : Nat := 1271277458324101561263989

theorem tailTrace_3713706 : CollatzResearch.WordTrace tailWord_3713706 prefixEnd_3713706 1271277458324101561263989 := by
  unfold tailWord_3713706
  simp only [CollatzResearch.WordTrace]
  refine ⟨33862496370971221833662243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90299990322589924889765981 33862496370971221833662243)
  ·
    refine ⟨50793744556456832750493365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33862496370971221833662243 50793744556456832750493365)
    ·
      refine ⟨4761913552167828070358753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50793744556456832750493365 4761913552167828070358753)
      ·
        refine ⟨3571435164125871052769065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4761913552167828070358753 3571435164125871052769065)
        ·
          refine ⟨2678576373094403289576799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3571435164125871052769065 2678576373094403289576799)
          ·
            refine ⟨4017864559641604934365199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2678576373094403289576799 4017864559641604934365199)
            ·
              refine ⟨6026796839462407401547799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4017864559641604934365199 6026796839462407401547799)
              ·
                refine ⟨9040195259193611102321699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6026796839462407401547799 9040195259193611102321699)
                ·
                  refine ⟨13560292888790416653482549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9040195259193611102321699 13560292888790416653482549)
                  ·
                    refine ⟨1271277458324101561263989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13560292888790416653482549 1271277458324101561263989)
                    ·
                      rfl

theorem cell22_3713706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_3713706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713706 prefixEnd_3713706 := by exact prefixLift 3713706
  have htrace : WordTrace (prefixWord ++ tailWord_3713706) baseStart_3713706 baseEnd_3713706 := by
    simpa [prefixWord, tailWord_3713706, baseEnd_3713706] using wordTrace_append hprefix tailTrace_3713706
  have hstable : (prefixWord ++ tailWord_3713706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713706).length < 2 ^ (prefixWord ++ tailWord_3713706).sum := by decide
  have hdescent : baseEnd_3713706 < baseStart_3713706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713717 : List Nat := [1, 3, 3, 3, 1, 1, 2, 2, 3, 3]
def baseStart_3713717 : Nat := 118140960795 + 3713717 * 2 ^ 59
def prefixEnd_3713717 : Nat := 4983230072969 + 3 ^ 40 * 3713717 * 2
def baseEnd_3713717 : Nat := 1271281223848901199238955

theorem tailTrace_3713717 : CollatzResearch.WordTrace tailWord_3713717 prefixEnd_3713717 1271281223848901199238955 := by
  unfold tailWord_3713717
  simp only [CollatzResearch.WordTrace]
  refine ⟨135450386686845036213299405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90300257791230024142199603 135450386686845036213299405)
  ·
    refine ⟨50793895007566888579987277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135450386686845036213299405 50793895007566888579987277)
    ·
      refine ⟨19047710627837583217495229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50793895007566888579987277 19047710627837583217495229)
      ·
        refine ⟨7142891485439093706560711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19047710627837583217495229 7142891485439093706560711)
        ·
          refine ⟨10714337228158640559841067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7142891485439093706560711 10714337228158640559841067)
          ·
            refine ⟨16071505842237960839761601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10714337228158640559841067 16071505842237960839761601)
            ·
              refine ⟨12053629381678470629821201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16071505842237960839761601 12053629381678470629821201)
              ·
                refine ⟨9040222036258852972365901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12053629381678470629821201 9040222036258852972365901)
                ·
                  refine ⟨3390083263597069864637213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9040222036258852972365901 3390083263597069864637213)
                  ·
                    refine ⟨1271281223848901199238955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3390083263597069864637213 1271281223848901199238955)
                    ·
                      rfl

theorem cell22_3713717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_3713717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713717 prefixEnd_3713717 := by exact prefixLift 3713717
  have htrace : WordTrace (prefixWord ++ tailWord_3713717) baseStart_3713717 baseEnd_3713717 := by
    simpa [prefixWord, tailWord_3713717, baseEnd_3713717] using wordTrace_append hprefix tailTrace_3713717
  have hstable : (prefixWord ++ tailWord_3713717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713717).length < 2 ^ (prefixWord ++ tailWord_3713717).sum := by decide
  have hdescent : baseEnd_3713717 < baseStart_3713717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713743 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 7, 4]
def baseStart_3713743 : Nat := 118140960795 + 3713743 * 2 ^ 59
def prefixEnd_3713743 : Nat := 4983230072969 + 3 ^ 40 * 3713743 * 2
def baseEnd_3713743 : Nat := 1271290124180245798088875

theorem tailTrace_3713743 : CollatzResearch.WordTrace tailWord_3713743 prefixEnd_3713743 1271290124180245798088875 := by
  unfold tailWord_3713743
  simp only [CollatzResearch.WordTrace]
  refine ⟨135451334984750842653745883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90300889989833895102497255 135451334984750842653745883)
  ·
    refine ⟨203177002477126263980618825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135451334984750842653745883 203177002477126263980618825)
    ·
      refine ⟨152382751857844697985464119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203177002477126263980618825 152382751857844697985464119)
      ·
        refine ⟨228574127786767046978196179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152382751857844697985464119 228574127786767046978196179)
        ·
          refine ⟨342861191680150570467294269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228574127786767046978196179 342861191680150570467294269)
          ·
            refine ⟨128572946880056463925235351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342861191680150570467294269 128572946880056463925235351)
            ·
              refine ⟨192859420320084695887853027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128572946880056463925235351 192859420320084695887853027)
              ·
                refine ⟨289289130480127043831779541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192859420320084695887853027 289289130480127043831779541)
                ·
                  refine ⟨6780213995627977589807333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 289289130480127043831779541 6780213995627977589807333)
                  ·
                    refine ⟨1271290124180245798088875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6780213995627977589807333 1271290124180245798088875)
                    ·
                      rfl

theorem cell22_3713743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_3713743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713743 prefixEnd_3713743 := by exact prefixLift 3713743
  have htrace : WordTrace (prefixWord ++ tailWord_3713743) baseStart_3713743 baseEnd_3713743 := by
    simpa [prefixWord, tailWord_3713743, baseEnd_3713743] using wordTrace_append hprefix tailTrace_3713743
  have hstable : (prefixWord ++ tailWord_3713743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713743).length < 2 ^ (prefixWord ++ tailWord_3713743).sum := by decide
  have hdescent : baseEnd_3713743 < baseStart_3713743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713807 : List Nat := [1, 1, 2, 1, 1, 1, 8, 2, 2, 3]
def baseStart_3713807 : Nat := 118140960795 + 3713807 * 2 ^ 59
def prefixEnd_3713807 : Nat := 4983230072969 + 3 ^ 40 * 3713807 * 2
def baseEnd_3713807 : Nat := 1271312032688170964488679

theorem tailTrace_3713807 : CollatzResearch.WordTrace tailWord_3713807 prefixEnd_3713807 1271312032688170964488679 := by
  unfold tailWord_3713807
  simp only [CollatzResearch.WordTrace]
  refine ⟨135453669256518981584075675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90302446171012654389383783 135453669256518981584075675)
  ·
    refine ⟨203180503884778472376113513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135453669256518981584075675 203180503884778472376113513)
    ·
      refine ⟨152385377913583854282085135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203180503884778472376113513 152385377913583854282085135)
      ·
        refine ⟨228578066870375781423127703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152385377913583854282085135 228578066870375781423127703)
        ·
          refine ⟨342867100305563672134691555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228578066870375781423127703 342867100305563672134691555)
          ·
            refine ⟨514300650458345508202037333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342867100305563672134691555 514300650458345508202037333)
            ·
              refine ⟨6026960747558736424242625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 514300650458345508202037333 6026960747558736424242625)
              ·
                refine ⟨4520220560669052318181969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6026960747558736424242625 4520220560669052318181969)
                ·
                  refine ⟨3390165420501789238636477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4520220560669052318181969 3390165420501789238636477)
                  ·
                    refine ⟨1271312032688170964488679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3390165420501789238636477 1271312032688170964488679)
                    ·
                      rfl

theorem cell22_3713807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 3].length) (baseStart_3713807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713807 prefixEnd_3713807 := by exact prefixLift 3713807
  have htrace : WordTrace (prefixWord ++ tailWord_3713807) baseStart_3713807 baseEnd_3713807 := by
    simpa [prefixWord, tailWord_3713807, baseEnd_3713807] using wordTrace_append hprefix tailTrace_3713807
  have hstable : (prefixWord ++ tailWord_3713807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713807).length < 2 ^ (prefixWord ++ tailWord_3713807).sum := by decide
  have hdescent : baseEnd_3713807 < baseStart_3713807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713820 : List Nat := [2, 2, 3, 1, 1, 3, 3, 7]
def baseStart_3713820 : Nat := 118140960795 + 3713820 * 2 ^ 59
def prefixEnd_3713820 : Nat := 4983230072969 + 3 ^ 40 * 3713820 * 2
def baseEnd_3713820 : Nat := 141257386983760362657071

theorem tailTrace_3713820 : CollatzResearch.WordTrace tailWord_3713820 prefixEnd_3713820 141257386983760362657071 := by
  unfold tailWord_3713820
  simp only [CollatzResearch.WordTrace]
  refine ⟨67727071702735942402149457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90302762270314589869532609 67727071702735942402149457)
  ·
    refine ⟨50795303777051956801612093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67727071702735942402149457 50795303777051956801612093)
    ·
      refine ⟨19048238916394483800604535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50795303777051956801612093 19048238916394483800604535)
      ·
        refine ⟨28572358374591725700906803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19048238916394483800604535 28572358374591725700906803)
        ·
          refine ⟨42858537561887588551360205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28572358374591725700906803 42858537561887588551360205)
          ·
            refine ⟨16071951585707845706760077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42858537561887588551360205 16071951585707845706760077)
            ·
              refine ⟨6026981844640442140035029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16071951585707845706760077 6026981844640442140035029)
              ·
                refine ⟨141257386983760362657071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6026981844640442140035029 141257386983760362657071)
                ·
                  rfl

theorem cell22_3713820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 7].length) (baseStart_3713820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713820 prefixEnd_3713820 := by exact prefixLift 3713820
  have htrace : WordTrace (prefixWord ++ tailWord_3713820) baseStart_3713820 baseEnd_3713820 := by
    simpa [prefixWord, tailWord_3713820, baseEnd_3713820] using wordTrace_append hprefix tailTrace_3713820
  have hstable : (prefixWord ++ tailWord_3713820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713820).length < 2 ^ (prefixWord ++ tailWord_3713820).sum := by decide
  have hdescent : baseEnd_3713820 < baseStart_3713820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713835 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 5, 3]
def baseStart_3713835 : Nat := 118140960795 + 3713835 * 2 ^ 59
def prefixEnd_3713835 : Nat := 4983230072969 + 3 ^ 40 * 3713835 * 2
def baseEnd_3713835 : Nat := 1271321617660388224788593

theorem tailTrace_3713835 : CollatzResearch.WordTrace tailWord_3713835 prefixEnd_3713835 1271321617660388224788593 := by
  unfold tailWord_3713835
  simp only [CollatzResearch.WordTrace]
  refine ⟨135454690500417542366094959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90303127000278361577396639 135454690500417542366094959)
  ·
    refine ⟨203182035750626313549142439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135454690500417542366094959 203182035750626313549142439)
    ·
      refine ⟨304773053625939470323713659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203182035750626313549142439 304773053625939470323713659)
      ·
        refine ⟨457159580438909205485570489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304773053625939470323713659 457159580438909205485570489)
        ·
          refine ⟨342869685329181904114177867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457159580438909205485570489 342869685329181904114177867)
          ·
            refine ⟨514304527993772856171266801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342869685329181904114177867 514304527993772856171266801)
            ·
              refine ⟨385728395995329642128450101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514304527993772856171266801 385728395995329642128450101)
              ·
                refine ⟨36162037124562153949542197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 385728395995329642128450101 36162037124562153949542197)
                ·
                  refine ⟨3390190980427701932769581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36162037124562153949542197 3390190980427701932769581)
                  ·
                    refine ⟨1271321617660388224788593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3390190980427701932769581 1271321617660388224788593)
                    ·
                      rfl

theorem cell22_3713835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 3].length) (baseStart_3713835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713835 prefixEnd_3713835 := by exact prefixLift 3713835
  have htrace : WordTrace (prefixWord ++ tailWord_3713835) baseStart_3713835 baseEnd_3713835 := by
    simpa [prefixWord, tailWord_3713835, baseEnd_3713835] using wordTrace_append hprefix tailTrace_3713835
  have hstable : (prefixWord ++ tailWord_3713835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713835).length < 2 ^ (prefixWord ++ tailWord_3713835).sum := by decide
  have hdescent : baseEnd_3713835 < baseStart_3713835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713865 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 7]
def baseStart_3713865 : Nat := 118140960795 + 3713865 * 2 ^ 59
def prefixEnd_3713865 : Nat := 4983230072969 + 3 ^ 40 * 3713865 * 2
def baseEnd_3713865 : Nat := 423777295757826048846167

theorem tailTrace_3713865 : CollatzResearch.WordTrace tailWord_3713865 prefixEnd_3713865 423777295757826048846167 := by
  unfold tailWord_3713865
  simp only [CollatzResearch.WordTrace]
  refine ⟨135455784690308857489687049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90303856460205904993124699 135455784690308857489687049)
  ·
    refine ⟨101591838517731643117265287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135455784690308857489687049 101591838517731643117265287)
    ·
      refine ⟨152387757776597464675897931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101591838517731643117265287 152387757776597464675897931)
      ·
        refine ⟨228581636664896197013846897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152387757776597464675897931 228581636664896197013846897)
        ·
          refine ⟨171436227498672147760385173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228581636664896197013846897 171436227498672147760385173)
          ·
            refine ⟨8036073164000256926268055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 171436227498672147760385173 8036073164000256926268055)
            ·
              refine ⟨12054109746000385389402083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8036073164000256926268055 12054109746000385389402083)
              ·
                refine ⟨18081164619000578084103125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12054109746000385389402083 18081164619000578084103125)
                ·
                  refine ⟨423777295757826048846167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18081164619000578084103125 423777295757826048846167)
                  ·
                    rfl

theorem cell22_3713865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 7].length) (baseStart_3713865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713865 prefixEnd_3713865 := by exact prefixLift 3713865
  have htrace : WordTrace (prefixWord ++ tailWord_3713865) baseStart_3713865 baseEnd_3713865 := by
    simpa [prefixWord, tailWord_3713865, baseEnd_3713865] using wordTrace_append hprefix tailTrace_3713865
  have hstable : (prefixWord ++ tailWord_3713865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713865).length < 2 ^ (prefixWord ++ tailWord_3713865).sum := by decide
  have hdescent : baseEnd_3713865 < baseStart_3713865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713927 : List Nat := [1, 1, 4, 2, 3, 1, 3, 1, 6]
def baseStart_3713927 : Nat := 118140960795 + 3713927 * 2 ^ 59
def prefixEnd_3713927 : Nat := 4983230072969 + 3 ^ 40 * 3713927 * 2
def baseEnd_3713927 : Nat := 423784370380176883829437

theorem tailTrace_3713927 : CollatzResearch.WordTrace tailWord_3713927 prefixEnd_3713927 423784370380176883829437 := by
  unfold tailWord_3713927
  simp only [CollatzResearch.WordTrace]
  refine ⟨135458046016084242078444035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90305364010722828052296023 135458046016084242078444035)
  ·
    refine ⟨203187069024126363117666053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135458046016084242078444035 203187069024126363117666053)
    ·
      refine ⟨38097575442023693084562385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203187069024126363117666053 38097575442023693084562385)
      ·
        refine ⟨28573181581517769813421789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38097575442023693084562385 28573181581517769813421789)
        ·
          refine ⟨10714943093069163680033171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28573181581517769813421789 10714943093069163680033171)
          ·
            refine ⟨16072414639603745520049757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10714943093069163680033171 16072414639603745520049757)
            ·
              refine ⟨6027155489851404570018659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16072414639603745520049757 6027155489851404570018659)
              ·
                refine ⟨9040733234777106855027989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6027155489851404570018659 9040733234777106855027989)
                ·
                  refine ⟨423784370380176883829437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9040733234777106855027989 423784370380176883829437)
                  ·
                    rfl

theorem cell22_3713927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 6].length) (baseStart_3713927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713927 prefixEnd_3713927 := by exact prefixLift 3713927
  have htrace : WordTrace (prefixWord ++ tailWord_3713927) baseStart_3713927 baseEnd_3713927 := by
    simpa [prefixWord, tailWord_3713927, baseEnd_3713927] using wordTrace_append hprefix tailTrace_3713927
  have hstable : (prefixWord ++ tailWord_3713927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713927).length < 2 ^ (prefixWord ++ tailWord_3713927).sum := by decide
  have hdescent : baseEnd_3713927 < baseStart_3713927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713946 : List Nat := [3, 1, 1, 4, 3, 2, 1, 2, 1, 4]
def baseStart_3713946 : Nat := 118140960795 + 3713946 * 2 ^ 59
def prefixEnd_3713946 : Nat := 4983230072969 + 3 ^ 40 * 3713946 * 2
def baseEnd_3713946 : Nat := 1271359615228820935263253

theorem tailTrace_3713946 : CollatzResearch.WordTrace tailWord_3713946 prefixEnd_3713946 1271359615228820935263253 := by
  unfold tailWord_3713946
  simp only [CollatzResearch.WordTrace]
  refine ⟨33864684750753852080846423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90305826002010272215590461 33864684750753852080846423)
  ·
    refine ⟨50797027126130778121269635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33864684750753852080846423 50797027126130778121269635)
    ·
      refine ⟨76195540689196167181904453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50797027126130778121269635 76195540689196167181904453)
      ·
        refine ⟨14286663879224281346607085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76195540689196167181904453 14286663879224281346607085)
        ·
          refine ⟨5357498954709105504977657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14286663879224281346607085 5357498954709105504977657)
          ·
            refine ⟨4018124216031829128733243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5357498954709105504977657 4018124216031829128733243)
            ·
              refine ⟨6027186324047743693099865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4018124216031829128733243 6027186324047743693099865)
              ·
                refine ⟨4520389743035807769824899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6027186324047743693099865 4520389743035807769824899)
                ·
                  refine ⟨6780584614553711654737349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4520389743035807769824899 6780584614553711654737349)
                  ·
                    refine ⟨1271359615228820935263253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6780584614553711654737349 1271359615228820935263253)
                    ·
                      rfl

theorem cell22_3713946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_3713946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713946 prefixEnd_3713946 := by exact prefixLift 3713946
  have htrace : WordTrace (prefixWord ++ tailWord_3713946) baseStart_3713946 baseEnd_3713946 := by
    simpa [prefixWord, tailWord_3713946, baseEnd_3713946] using wordTrace_append hprefix tailTrace_3713946
  have hstable : (prefixWord ++ tailWord_3713946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713946).length < 2 ^ (prefixWord ++ tailWord_3713946).sum := by decide
  have hdescent : baseEnd_3713946 < baseStart_3713946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713955 : List Nat := [1, 1, 1, 4, 1, 2, 4, 8]
def baseStart_3713955 : Nat := 118140960795 + 3713955 * 2 ^ 59
def prefixEnd_3713955 : Nat := 4983230072969 + 3 ^ 40 * 3713955 * 2
def baseEnd_3713955 : Nat := 141262521790305323532025

theorem tailTrace_3713955 : CollatzResearch.WordTrace tailWord_3713955 prefixEnd_3713955 141262521790305323532025 := by
  unfold tailWord_3713955
  simp only [CollatzResearch.WordTrace]
  refine ⟨135459067259982802860463319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90306044839988535240308879 135459067259982802860463319)
  ·
    refine ⟨203188600889974204290694979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135459067259982802860463319 203188600889974204290694979)
    ·
      refine ⟨304782901334961306436042469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203188600889974204290694979 304782901334961306436042469)
      ·
        refine ⟨57146794000305244956757963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304782901334961306436042469 57146794000305244956757963)
        ·
          refine ⟨85720191000457867435136945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57146794000305244956757963 85720191000457867435136945)
          ·
            refine ⟨64290143250343400576352709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85720191000457867435136945 64290143250343400576352709)
            ·
              refine ⟨12054401859439387608066133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64290143250343400576352709 12054401859439387608066133)
              ·
                refine ⟨141262521790305323532025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12054401859439387608066133 141262521790305323532025)
                ·
                  rfl

theorem cell22_3713955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 8].length) (baseStart_3713955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713955 prefixEnd_3713955 := by exact prefixLift 3713955
  have htrace : WordTrace (prefixWord ++ tailWord_3713955) baseStart_3713955 baseEnd_3713955 := by
    simpa [prefixWord, tailWord_3713955, baseEnd_3713955] using wordTrace_append hprefix tailTrace_3713955
  have hstable : (prefixWord ++ tailWord_3713955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713955).length < 2 ^ (prefixWord ++ tailWord_3713955).sum := by decide
  have hdescent : baseEnd_3713955 < baseStart_3713955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713959 : List Nat := [1, 1, 6, 1, 3, 1, 1, 2, 1, 5]
def baseStart_3713959 : Nat := 118140960795 + 3713959 * 2 ^ 59
def prefixEnd_3713959 : Nat := 4983230072969 + 3 ^ 40 * 3713959 * 2
def baseEnd_3713959 : Nat := 1271364065394493234688213

theorem tailTrace_3713959 : CollatzResearch.WordTrace tailWord_3713959 prefixEnd_3713959 1271364065394493234688213 := by
  unfold tailWord_3713959
  simp only [CollatzResearch.WordTrace]
  refine ⟨135459213151968311543608931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90306142101312207695739287 135459213151968311543608931)
  ·
    refine ⟨203188819727952467315413397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135459213151968311543608931 203188819727952467315413397)
    ·
      refine ⟨9524475924747771905410003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 203188819727952467315413397 9524475924747771905410003)
      ·
        refine ⟨14286713887121657858115005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9524475924747771905410003 14286713887121657858115005)
        ·
          refine ⟨5357517707670621696793127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14286713887121657858115005 5357517707670621696793127)
          ·
            refine ⟨8036276561505932545189691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5357517707670621696793127 8036276561505932545189691)
            ·
              refine ⟨12054414842258898817784537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8036276561505932545189691 12054414842258898817784537)
              ·
                refine ⟨9040811131694174113338403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12054414842258898817784537 9040811131694174113338403)
                ·
                  refine ⟨13561216697541261170007605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9040811131694174113338403 13561216697541261170007605)
                  ·
                    refine ⟨1271364065394493234688213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13561216697541261170007605 1271364065394493234688213)
                    ·
                      rfl

theorem cell22_3713959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_3713959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3713959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3713959 prefixEnd_3713959 := by exact prefixLift 3713959
  have htrace : WordTrace (prefixWord ++ tailWord_3713959) baseStart_3713959 baseEnd_3713959 := by
    simpa [prefixWord, tailWord_3713959, baseEnd_3713959] using wordTrace_append hprefix tailTrace_3713959
  have hstable : (prefixWord ++ tailWord_3713959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713959).length < 2 ^ (prefixWord ++ tailWord_3713959).sum := by decide
  have hdescent : baseEnd_3713959 < baseStart_3713959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714000 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 9]
def baseStart_3714000 : Nat := 118140960795 + 3714000 * 2 ^ 59
def prefixEnd_3714000 : Nat := 4983230072969 + 3 ^ 40 * 3714000 * 2
def baseEnd_3714000 : Nat := 423792700177460931471029

theorem tailTrace_3714000 : CollatzResearch.WordTrace tailWord_3714000 prefixEnd_3714000 423792700177460931471029 := by
  unfold tailWord_3714000
  simp only [CollatzResearch.WordTrace]
  refine ⟨67730354272409887772925727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90307139029879850363900969 67730354272409887772925727)
  ·
    refine ⟨101595531408614831659388591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67730354272409887772925727 101595531408614831659388591)
    ·
      refine ⟨152393297112922247489082887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101595531408614831659388591 152393297112922247489082887)
      ·
        refine ⟨228589945669383371233624331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152393297112922247489082887 228589945669383371233624331)
        ·
          refine ⟨342884918504075056850436497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228589945669383371233624331 342884918504075056850436497)
          ·
            refine ⟨257163688878056292637827373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342884918504075056850436497 257163688878056292637827373)
            ·
              refine ⟨96436383329271109739185265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257163688878056292637827373 96436383329271109739185265)
              ·
                refine ⟨72327287496953332304388949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96436383329271109739185265 72327287496953332304388949)
                ·
                  refine ⟨423792700177460931471029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72327287496953332304388949 423792700177460931471029)
                  ·
                    rfl

theorem cell22_3714000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 9].length) (baseStart_3714000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714000 prefixEnd_3714000 := by exact prefixLift 3714000
  have htrace : WordTrace (prefixWord ++ tailWord_3714000) baseStart_3714000 baseEnd_3714000 := by
    simpa [prefixWord, tailWord_3714000, baseEnd_3714000] using wordTrace_append hprefix tailTrace_3714000
  have hstable : (prefixWord ++ tailWord_3714000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714000).length < 2 ^ (prefixWord ++ tailWord_3714000).sum := by decide
  have hdescent : baseEnd_3714000 < baseStart_3714000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714004 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_3714004 : Nat := 118140960795 + 3714004 * 2 ^ 59
def prefixEnd_3714004 : Nat := 4983230072969 + 3 ^ 40 * 3714004 * 2
def baseEnd_3714004 : Nat := 1271379469814128117313075

theorem tailTrace_3714004 : CollatzResearch.WordTrace tailWord_3714004 prefixEnd_3714004 1271379469814128117313075 := by
  unfold tailWord_3714004
  simp only [CollatzResearch.WordTrace]
  refine ⟨67730427218402642114498533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90307236291203522819331377 67730427218402642114498533)
  ·
    refine ⟨12699455103450495396468475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67730427218402642114498533 12699455103450495396468475)
    ·
      refine ⟨19049182655175743094702713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12699455103450495396468475 19049182655175743094702713)
      ·
        refine ⟨14286886991381807321027035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19049182655175743094702713 14286886991381807321027035)
        ·
          refine ⟨21430330487072710981540553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14286886991381807321027035 21430330487072710981540553)
          ·
            refine ⟨16072747865304533236155415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21430330487072710981540553 16072747865304533236155415)
            ·
              refine ⟨24109121797956799854233123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16072747865304533236155415 24109121797956799854233123)
              ·
                refine ⟨36163682696935199781349685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24109121797956799854233123 36163682696935199781349685)
                ·
                  refine ⟨3390345252837674979501533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36163682696935199781349685 3390345252837674979501533)
                  ·
                    refine ⟨1271379469814128117313075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3390345252837674979501533 1271379469814128117313075)
                    ·
                      rfl

theorem cell22_3714004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_3714004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714004 prefixEnd_3714004 := by exact prefixLift 3714004
  have htrace : WordTrace (prefixWord ++ tailWord_3714004) baseStart_3714004 baseEnd_3714004 := by
    simpa [prefixWord, tailWord_3714004, baseEnd_3714004] using wordTrace_append hprefix tailTrace_3714004
  have hstable : (prefixWord ++ tailWord_3714004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714004).length < 2 ^ (prefixWord ++ tailWord_3714004).sum := by decide
  have hdescent : baseEnd_3714004 < baseStart_3714004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714006 : List Nat := [5, 2, 1, 1, 2, 2, 3, 6]
def baseStart_3714006 : Nat := 118140960795 + 3714006 * 2 ^ 59
def prefixEnd_3714006 : Nat := 4983230072969 + 3 ^ 40 * 3714006 * 2
def baseEnd_3714006 : Nat := 141264461606111197640341

theorem tailTrace_3714006 : CollatzResearch.WordTrace tailWord_3714006 prefixEnd_3714006 141264461606111197640341 := by
  unfold tailWord_3714006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8466307961424877410660617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90307284921865359047046581 8466307961424877410660617)
  ·
    refine ⟨6349730971068658057995463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8466307961424877410660617 6349730971068658057995463)
    ·
      refine ⟨9524596456602987086993195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6349730971068658057995463 9524596456602987086993195)
      ·
        refine ⟨14286894684904480630489793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9524596456602987086993195 14286894684904480630489793)
        ·
          refine ⟨10715171013678360472867345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14286894684904480630489793 10715171013678360472867345)
          ·
            refine ⟨8036378260258770354650509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10715171013678360472867345 8036378260258770354650509)
            ·
              refine ⟨3013641847597038882993941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8036378260258770354650509 3013641847597038882993941)
              ·
                refine ⟨141264461606111197640341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3013641847597038882993941 141264461606111197640341)
                ·
                  rfl

theorem cell22_3714006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_3714006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714006 prefixEnd_3714006 := by exact prefixLift 3714006
  have htrace : WordTrace (prefixWord ++ tailWord_3714006) baseStart_3714006 baseEnd_3714006 := by
    simpa [prefixWord, tailWord_3714006, baseEnd_3714006] using wordTrace_append hprefix tailTrace_3714006
  have hstable : (prefixWord ++ tailWord_3714006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714006).length < 2 ^ (prefixWord ++ tailWord_3714006).sum := by decide
  have hdescent : baseEnd_3714006 < baseStart_3714006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714038 : List Nat := [5, 1, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_3714038 : Nat := 118140960795 + 3714038 * 2 ^ 59
def prefixEnd_3714038 : Nat := 4983230072969 + 3 ^ 40 * 3714038 * 2
def baseEnd_3714038 : Nat := 1271391108708963361962971

theorem tailTrace_3714038 : CollatzResearch.WordTrace tailWord_3714038 prefixEnd_3714038 1271391108708963361962971 := by
  unfold tailWord_3714038
  simp only [CollatzResearch.WordTrace]
  refine ⟨8466380907417631752233423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90308063012454738690489845 8466380907417631752233423)
  ·
    refine ⟨12699571361126447628350135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8466380907417631752233423 12699571361126447628350135)
    ·
      refine ⟨19049357041689671442525203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12699571361126447628350135 19049357041689671442525203)
      ·
        refine ⟨28574035562534507163787805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19049357041689671442525203 28574035562534507163787805)
        ·
          refine ⟨10715263335950440186420427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28574035562534507163787805 10715263335950440186420427)
          ·
            refine ⟨16072895003925660279630641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10715263335950440186420427 16072895003925660279630641)
            ·
              refine ⟨12054671252944245209722981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16072895003925660279630641 12054671252944245209722981)
              ·
                refine ⟨2260250859927045976823059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12054671252944245209722981 2260250859927045976823059)
                ·
                  refine ⟨3390376289890568965234589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2260250859927045976823059 3390376289890568965234589)
                  ·
                    refine ⟨1271391108708963361962971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3390376289890568965234589 1271391108708963361962971)
                    ·
                      rfl

theorem cell22_3714038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_3714038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714038 prefixEnd_3714038 := by exact prefixLift 3714038
  have htrace : WordTrace (prefixWord ++ tailWord_3714038) baseStart_3714038 baseEnd_3714038 := by
    simpa [prefixWord, tailWord_3714038, baseEnd_3714038] using wordTrace_append hprefix tailTrace_3714038
  have hstable : (prefixWord ++ tailWord_3714038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714038).length < 2 ^ (prefixWord ++ tailWord_3714038).sum := by decide
  have hdescent : baseEnd_3714038 < baseStart_3714038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714096 : List Nat := [2, 1, 1, 1, 2, 4, 5, 2, 4]
def baseStart_3714096 : Nat := 118140960795 + 3714096 * 2 ^ 59
def prefixEnd_3714096 : Nat := 4983230072969 + 3 ^ 40 * 3714096 * 2
def baseEnd_3714096 : Nat := 423803654431423514670931

theorem tailTrace_3714096 : CollatzResearch.WordTrace tailWord_3714096 prefixEnd_3714096 423803654431423514670931 := by
  unfold tailWord_3714096
  simp only [CollatzResearch.WordTrace]
  refine ⟨67732104976235991970673071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90309473301647989294230761 67732104976235991970673071)
  ·
    refine ⟨101598157464353987956009607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67732104976235991970673071 101598157464353987956009607)
    ·
      refine ⟨152397236196530981934014411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101598157464353987956009607 152397236196530981934014411)
      ·
        refine ⟨228595854294796472901021617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152397236196530981934014411 228595854294796472901021617)
        ·
          refine ⟨171446890721097354675766213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228595854294796472901021617 171446890721097354675766213)
          ·
            refine ⟨32146292010205754001706165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171446890721097354675766213 32146292010205754001706165)
            ·
              refine ⟨3013714875956789437659953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32146292010205754001706165 3013714875956789437659953)
              ·
                refine ⟨2260286156967592078244965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3013714875956789437659953 2260286156967592078244965)
                ·
                  refine ⟨423803654431423514670931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2260286156967592078244965 423803654431423514670931)
                  ·
                    rfl

theorem cell22_3714096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 4].length) (baseStart_3714096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714096 prefixEnd_3714096 := by exact prefixLift 3714096
  have htrace : WordTrace (prefixWord ++ tailWord_3714096) baseStart_3714096 baseEnd_3714096 := by
    simpa [prefixWord, tailWord_3714096, baseEnd_3714096] using wordTrace_append hprefix tailTrace_3714096
  have hstable : (prefixWord ++ tailWord_3714096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714096).length < 2 ^ (prefixWord ++ tailWord_3714096).sum := by decide
  have hdescent : baseEnd_3714096 < baseStart_3714096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714122 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 2, 7]
def baseStart_3714122 : Nat := 118140960795 + 3714122 * 2 ^ 59
def prefixEnd_3714122 : Nat := 4983230072969 + 3 ^ 40 * 3714122 * 2
def baseEnd_3714122 : Nat := 1271419863625615142862713

theorem tailTrace_3714122 : CollatzResearch.WordTrace tailWord_3714122 prefixEnd_3714122 1271419863625615142862713 := by
  unfold tailWord_3714122
  simp only [CollatzResearch.WordTrace]
  refine ⟨33866289562594447595448155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90310105500251860254528413 33866289562594447595448155)
  ·
    refine ⟨50799434343891671393172233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33866289562594447595448155 50799434343891671393172233)
    ·
      refine ⟨38099575757918753544879175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50799434343891671393172233 38099575757918753544879175)
      ·
        refine ⟨57149363636878130317318763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38099575757918753544879175 57149363636878130317318763)
        ·
          refine ⟨85724045455317195475978145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57149363636878130317318763 85724045455317195475978145)
          ·
            refine ⟨64293034091487896606983609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85724045455317195475978145 64293034091487896606983609)
            ·
              refine ⟨48219775568615922455237707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64293034091487896606983609 48219775568615922455237707)
              ·
                refine ⟨72329663352923883682856561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48219775568615922455237707 72329663352923883682856561)
                ·
                  refine ⟨54247247514692912762142421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72329663352923883682856561 54247247514692912762142421)
                  ·
                    refine ⟨1271419863625615142862713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54247247514692912762142421 1271419863625615142862713)
                    ·
                      rfl

theorem cell22_3714122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_3714122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714122 prefixEnd_3714122 := by exact prefixLift 3714122
  have htrace : WordTrace (prefixWord ++ tailWord_3714122) baseStart_3714122 baseEnd_3714122 := by
    simpa [prefixWord, tailWord_3714122, baseEnd_3714122] using wordTrace_append hprefix tailTrace_3714122
  have hstable : (prefixWord ++ tailWord_3714122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714122).length < 2 ^ (prefixWord ++ tailWord_3714122).sum := by decide
  have hdescent : baseEnd_3714122 < baseStart_3714122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714141 : List Nat := [1, 4, 4, 1, 3, 9]
def baseStart_3714141 : Nat := 118140960795 + 3714141 * 2 ^ 59
def prefixEnd_3714141 : Nat := 4983230072969 + 3 ^ 40 * 3714141 * 2
def baseEnd_3714141 : Nat := 15696621823628462057255

theorem tailTrace_3714141 : CollatzResearch.WordTrace tailWord_3714141 prefixEnd_3714141 15696621823628462057255 := by
  unfold tailWord_3714141
  simp only [CollatzResearch.WordTrace]
  refine ⟨135465851237308956626734277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90310567491539304417822851 135465851237308956626734277)
  ·
    refine ⟨25399847106995429367512677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135465851237308956626734277 25399847106995429367512677)
    ·
      refine ⟨4762471332561643006408627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25399847106995429367512677 4762471332561643006408627)
      ·
        refine ⟨7143706998842464509612941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4762471332561643006408627 7143706998842464509612941)
        ·
          refine ⟨2678890124565924191104853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7143706998842464509612941 2678890124565924191104853)
          ·
            refine ⟨15696621823628462057255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2678890124565924191104853 15696621823628462057255)
            ·
              rfl

theorem cell22_3714141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 9].length) (baseStart_3714141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714141 prefixEnd_3714141 := by exact prefixLift 3714141
  have htrace : WordTrace (prefixWord ++ tailWord_3714141) baseStart_3714141 baseEnd_3714141 := by
    simpa [prefixWord, tailWord_3714141, baseEnd_3714141] using wordTrace_append hprefix tailTrace_3714141
  have hstable : (prefixWord ++ tailWord_3714141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714141).length < 2 ^ (prefixWord ++ tailWord_3714141).sum := by decide
  have hdescent : baseEnd_3714141 < baseStart_3714141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714154 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 2, 6]
def baseStart_3714154 : Nat := 118140960795 + 3714154 * 2 ^ 59
def prefixEnd_3714154 : Nat := 4983230072969 + 3 ^ 40 * 3714154 * 2
def baseEnd_3714154 : Nat := 1271430817879577726062615

theorem tailTrace_3714154 : CollatzResearch.WordTrace tailWord_3714154 prefixEnd_3714154 1271430817879577726062615 := by
  unfold tailWord_3714154
  simp only [CollatzResearch.WordTrace]
  refine ⟨33866581346565464961739379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90310883590841239897971677 33866581346565464961739379)
  ·
    refine ⟨50799872019848197442609069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33866581346565464961739379 50799872019848197442609069)
    ·
      refine ⟨19049952007443074040978401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50799872019848197442609069 19049952007443074040978401)
      ·
        refine ⟨14287464005582305530733801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19049952007443074040978401 14287464005582305530733801)
        ·
          refine ⟨10715598004186729148050351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14287464005582305530733801 10715598004186729148050351)
          ·
            refine ⟨16073397006280093722075527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10715598004186729148050351 16073397006280093722075527)
            ·
              refine ⟨24110095509420140583113291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16073397006280093722075527 24110095509420140583113291)
              ·
                refine ⟨36165143264130210874669937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24110095509420140583113291 36165143264130210874669937)
                ·
                  refine ⟨27123857448097658156002453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36165143264130210874669937 27123857448097658156002453)
                  ·
                    refine ⟨1271430817879577726062615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27123857448097658156002453 1271430817879577726062615)
                    ·
                      rfl

theorem cell22_3714154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_3714154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714154 prefixEnd_3714154 := by exact prefixLift 3714154
  have htrace : WordTrace (prefixWord ++ tailWord_3714154) baseStart_3714154 baseEnd_3714154 := by
    simpa [prefixWord, tailWord_3714154, baseEnd_3714154] using wordTrace_append hprefix tailTrace_3714154
  have hstable : (prefixWord ++ tailWord_3714154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714154).length < 2 ^ (prefixWord ++ tailWord_3714154).sum := by decide
  have hdescent : baseEnd_3714154 < baseStart_3714154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714190 : List Nat := [4, 1, 1, 3, 2, 2, 2, 3, 1, 3]
def baseStart_3714190 : Nat := 118140960795 + 3714190 * 2 ^ 59
def prefixEnd_3714190 : Nat := 4983230072969 + 3 ^ 40 * 3714190 * 2
def baseEnd_3714190 : Nat := 1271443141415285632162505

theorem tailTrace_3714190 : CollatzResearch.WordTrace tailWord_3714190 prefixEnd_3714190 1271443141415285632162505 := by
  unfold tailWord_3714190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16933454801766429749408503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90311758942754291996845349 16933454801766429749408503)
  ·
    refine ⟨25400182202649644624112755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16933454801766429749408503 25400182202649644624112755)
    ·
      refine ⟨38100273303974466936169133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25400182202649644624112755 38100273303974466936169133)
      ·
        refine ⟨14287602488990425101063425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38100273303974466936169133 14287602488990425101063425)
        ·
          refine ⟨10715701866742818825797569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14287602488990425101063425 10715701866742818825797569)
          ·
            refine ⟨8036776400057114119348177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10715701866742818825797569 8036776400057114119348177)
            ·
              refine ⟨6027582300042835589511133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8036776400057114119348177 6027582300042835589511133)
              ·
                refine ⟨2260343362516063346066675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6027582300042835589511133 2260343362516063346066675)
                ·
                  refine ⟨3390515043774095019100013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2260343362516063346066675 3390515043774095019100013)
                  ·
                    refine ⟨1271443141415285632162505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3390515043774095019100013 1271443141415285632162505)
                    ·
                      rfl

theorem cell22_3714190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_3714190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714190 prefixEnd_3714190 := by exact prefixLift 3714190
  have htrace : WordTrace (prefixWord ++ tailWord_3714190) baseStart_3714190 baseEnd_3714190 := by
    simpa [prefixWord, tailWord_3714190, baseEnd_3714190] using wordTrace_append hprefix tailTrace_3714190
  have hstable : (prefixWord ++ tailWord_3714190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714190).length < 2 ^ (prefixWord ++ tailWord_3714190).sum := by decide
  have hdescent : baseEnd_3714190 < baseStart_3714190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714261 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 4, 4]
def baseStart_3714261 : Nat := 118140960795 + 3714261 * 2 ^ 59
def prefixEnd_3714261 : Nat := 4983230072969 + 3 ^ 40 * 3714261 * 2
def baseEnd_3714261 : Nat := 1271467446166265113637287

theorem tailTrace_3714261 : CollatzResearch.WordTrace tailWord_3714261 prefixEnd_3714261 1271467446166265113637287 := by
  unfold tailWord_3714261
  simp only [CollatzResearch.WordTrace]
  refine ⟨135470227996874217121102637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90313485331249478080735091 135470227996874217121102637)
  ·
    refine ⟨50801335498827831420413489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135470227996874217121102637 50801335498827831420413489)
    ·
      refine ⟨38101001624120873565310117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50801335498827831420413489 38101001624120873565310117)
      ·
        refine ⟨7143937804522663793495647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38101001624120873565310117 7143937804522663793495647)
        ·
          refine ⟨10715906706783995690243471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7143937804522663793495647 10715906706783995690243471)
          ·
            refine ⟨16073860060175993535365207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10715906706783995690243471 16073860060175993535365207)
            ·
              refine ⟨24110790090263990303047811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16073860060175993535365207 24110790090263990303047811)
              ·
                refine ⟨36166185135395985454571717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24110790090263990303047811 36166185135395985454571717)
                ·
                  refine ⟨6781159712886747272732197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36166185135395985454571717 6781159712886747272732197)
                  ·
                    refine ⟨1271467446166265113637287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6781159712886747272732197 1271467446166265113637287)
                    ·
                      rfl

theorem cell22_3714261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_3714261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714261 prefixEnd_3714261 := by exact prefixLift 3714261
  have htrace : WordTrace (prefixWord ++ tailWord_3714261) baseStart_3714261 baseEnd_3714261 := by
    simpa [prefixWord, tailWord_3714261, baseEnd_3714261] using wordTrace_append hprefix tailTrace_3714261
  have hstable : (prefixWord ++ tailWord_3714261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714261).length < 2 ^ (prefixWord ++ tailWord_3714261).sum := by decide
  have hdescent : baseEnd_3714261 < baseStart_3714261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714321 : List Nat := [1, 2, 2, 1, 1, 4, 4, 2, 5]
def baseStart_3714321 : Nat := 118140960795 + 3714321 * 2 ^ 59
def prefixEnd_3714321 : Nat := 4983230072969 + 3 ^ 40 * 3714321 * 2
def baseEnd_3714321 : Nat := 423829328464148319045701

theorem tailTrace_3714321 : CollatzResearch.WordTrace tailWord_3714321 prefixEnd_3714321 423829328464148319045701 := by
  unfold tailWord_3714321
  simp only [CollatzResearch.WordTrace]
  refine ⟨135472416376656847368286817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90314944251104564912191211 135472416376656847368286817)
  ·
    refine ⟨101604312282492635526215113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135472416376656847368286817 101604312282492635526215113)
    ·
      refine ⟨76203234211869476644661335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101604312282492635526215113 76203234211869476644661335)
      ·
        refine ⟨114304851317804214966992003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76203234211869476644661335 114304851317804214966992003)
        ·
          refine ⟨171457276976706322450488005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114304851317804214966992003 171457276976706322450488005)
          ·
            refine ⟨32148239433132435459466501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171457276976706322450488005 32148239433132435459466501)
            ·
              refine ⟨6027794893712331648649969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32148239433132435459466501 6027794893712331648649969)
              ·
                refine ⟨4520846170284248736487477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6027794893712331648649969 4520846170284248736487477)
                ·
                  refine ⟨423829328464148319045701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4520846170284248736487477 423829328464148319045701)
                  ·
                    rfl

theorem cell22_3714321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 5].length) (baseStart_3714321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714321 prefixEnd_3714321 := by exact prefixLift 3714321
  have htrace : WordTrace (prefixWord ++ tailWord_3714321) baseStart_3714321 baseEnd_3714321 := by
    simpa [prefixWord, tailWord_3714321, baseEnd_3714321] using wordTrace_append hprefix tailTrace_3714321
  have hstable : (prefixWord ++ tailWord_3714321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714321).length < 2 ^ (prefixWord ++ tailWord_3714321).sum := by decide
  have hdescent : baseEnd_3714321 < baseStart_3714321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714351 : List Nat := [1, 1, 2, 1, 2, 1, 3, 6, 1, 4]
def baseStart_3714351 : Nat := 118140960795 + 3714351 * 2 ^ 59
def prefixEnd_3714351 : Nat := 4983230072969 + 3 ^ 40 * 3714351 * 2
def baseEnd_3714351 : Nat := 1271498255005534878887011

theorem tailTrace_3714351 : CollatzResearch.WordTrace tailWord_3714351 prefixEnd_3714351 1271498255005534878887011 := by
  unfold tailWord_3714351
  simp only [CollatzResearch.WordTrace]
  refine ⟨135473510566548162491878907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90315673711032108327919271 135473510566548162491878907)
  ·
    refine ⟨203210265849822243737818361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135473510566548162491878907 203210265849822243737818361)
    ·
      refine ⟨152407699387366682803363771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203210265849822243737818361 152407699387366682803363771)
      ·
        refine ⟨228611549081050024205045657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152407699387366682803363771 228611549081050024205045657)
        ·
          refine ⟨171458661810787518153784243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228611549081050024205045657 171458661810787518153784243)
          ·
            refine ⟨257187992716181277230676365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171458661810787518153784243 257187992716181277230676365)
            ·
              refine ⟨96445497268567978961503637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257187992716181277230676365 96445497268567978961503637)
              ·
                refine ⟨4520882684464124013820483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96445497268567978961503637 4520882684464124013820483)
                ·
                  refine ⟨6781324026696186020730725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4520882684464124013820483 6781324026696186020730725)
                  ·
                    refine ⟨1271498255005534878887011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6781324026696186020730725 1271498255005534878887011)
                    ·
                      rfl

theorem cell22_3714351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 4].length) (baseStart_3714351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714351 prefixEnd_3714351 := by exact prefixLift 3714351
  have htrace : WordTrace (prefixWord ++ tailWord_3714351) baseStart_3714351 baseEnd_3714351 := by
    simpa [prefixWord, tailWord_3714351, baseEnd_3714351] using wordTrace_append hprefix tailTrace_3714351
  have hstable : (prefixWord ++ tailWord_3714351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714351).length < 2 ^ (prefixWord ++ tailWord_3714351).sum := by decide
  have hdescent : baseEnd_3714351 < baseStart_3714351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714366 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 8]
def baseStart_3714366 : Nat := 118140960795 + 3714366 * 2 ^ 59
def prefixEnd_3714366 : Nat := 4983230072969 + 3 ^ 40 * 3714366 * 2
def baseEnd_3714366 : Nat := 423834463270693279920655

theorem tailTrace_3714366 : CollatzResearch.WordTrace tailWord_3714366 prefixEnd_3714366 423834463270693279920655 := by
  unfold tailWord_3714366
  simp only [CollatzResearch.WordTrace]
  refine ⟨16934257207686727506709369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90316038440995880035783301 16934257207686727506709369)
  ·
    refine ⟨12700692905765045630032027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16934257207686727506709369 12700692905765045630032027)
    ·
      refine ⟨19051039358647568445048041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12700692905765045630032027 19051039358647568445048041)
      ·
        refine ⟨14288279518985676333786031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19051039358647568445048041 14288279518985676333786031)
        ·
          refine ⟨21432419278478514500679047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14288279518985676333786031 21432419278478514500679047)
          ·
            refine ⟨32148628917717771751018571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21432419278478514500679047 32148628917717771751018571)
            ·
              refine ⟨48222943376576657626527857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32148628917717771751018571 48222943376576657626527857)
              ·
                refine ⟨36167207532432493219895893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48222943376576657626527857 36167207532432493219895893)
                ·
                  refine ⟨423834463270693279920655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36167207532432493219895893 423834463270693279920655)
                  ·
                    rfl

theorem cell22_3714366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_3714366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714366 prefixEnd_3714366 := by exact prefixLift 3714366
  have htrace : WordTrace (prefixWord ++ tailWord_3714366) baseStart_3714366 baseEnd_3714366 := by
    simpa [prefixWord, tailWord_3714366, baseEnd_3714366] using wordTrace_append hprefix tailTrace_3714366
  have hstable : (prefixWord ++ tailWord_3714366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714366).length < 2 ^ (prefixWord ++ tailWord_3714366).sum := by decide
  have hdescent : baseEnd_3714366 < baseStart_3714366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714434 : List Nat := [3, 4, 2, 1, 1, 2, 3, 2, 4]
def baseStart_3714434 : Nat := 118140960795 + 3714434 * 2 ^ 59
def prefixEnd_3714434 : Nat := 4983230072969 + 3 ^ 40 * 3714434 * 2
def baseEnd_3714434 : Nat := 423842222533916776353919

theorem tailTrace_3714434 : CollatzResearch.WordTrace tailWord_3714434 prefixEnd_3714434 423842222533916776353919 := by
  unfold tailWord_3714434
  simp only [CollatzResearch.WordTrace]
  refine ⟨33869134456311866916787589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90317691883498311778100237 33869134456311866916787589)
  ·
    refine ⟨6350462710558475046897673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33869134456311866916787589 6350462710558475046897673)
    ·
      refine ⟨4762847032918856285173255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6350462710558475046897673 4762847032918856285173255)
      ·
        refine ⟨7144270549378284427759883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4762847032918856285173255 7144270549378284427759883)
        ·
          refine ⟨10716405824067426641639825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7144270549378284427759883 10716405824067426641639825)
          ·
            refine ⟨8037304368050569981229869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10716405824067426641639825 8037304368050569981229869)
            ·
              refine ⟨3013989138018963742961201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8037304368050569981229869 3013989138018963742961201)
              ·
                refine ⟨2260491853514222807220901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3013989138018963742961201 2260491853514222807220901)
                ·
                  refine ⟨423842222533916776353919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2260491853514222807220901 423842222533916776353919)
                  ·
                    rfl

theorem cell22_3714434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_3714434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714434 prefixEnd_3714434 := by exact prefixLift 3714434
  have htrace : WordTrace (prefixWord ++ tailWord_3714434) baseStart_3714434 baseEnd_3714434 := by
    simpa [prefixWord, tailWord_3714434, baseEnd_3714434] using wordTrace_append hprefix tailTrace_3714434
  have hstable : (prefixWord ++ tailWord_3714434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714434).length < 2 ^ (prefixWord ++ tailWord_3714434).sum := by decide
  have hdescent : baseEnd_3714434 < baseStart_3714434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714535 : List Nat := [1, 1, 5, 2, 1, 2, 1, 5, 4]
def baseStart_3714535 : Nat := 118140960795 + 3714535 * 2 ^ 59
def prefixEnd_3714535 : Nat := 4983230072969 + 3 ^ 40 * 3714535 * 2
def baseEnd_3714535 : Nat := 423853747321939910762149

theorem tailTrace_3714535 : CollatzResearch.WordTrace tailWord_3714535 prefixEnd_3714535 423853747321939910762149 := by
  unfold tailWord_3714535
  simp only [CollatzResearch.WordTrace]
  refine ⟨135480221597881561916577059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90320147731921041277718039 135480221597881561916577059)
  ·
    refine ⟨203220332396822342874865589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135480221597881561916577059 203220332396822342874865589)
    ·
      refine ⟨19051906162202094644518649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203220332396822342874865589 19051906162202094644518649)
      ·
        refine ⟨14288929621651570983388987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19051906162202094644518649 14288929621651570983388987)
        ·
          refine ⟨21433394432477356475083481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14288929621651570983388987 21433394432477356475083481)
          ·
            refine ⟨16075045824358017356312611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21433394432477356475083481 16075045824358017356312611)
            ·
              refine ⟨24112568736537026034468917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16075045824358017356312611 24112568736537026034468917)
              ·
                refine ⟨2260553319050346190731461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24112568736537026034468917 2260553319050346190731461)
                ·
                  refine ⟨423853747321939910762149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2260553319050346190731461 423853747321939910762149)
                  ·
                    rfl

theorem cell22_3714535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 4].length) (baseStart_3714535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714535 prefixEnd_3714535 := by exact prefixLift 3714535
  have htrace : WordTrace (prefixWord ++ tailWord_3714535) baseStart_3714535 baseEnd_3714535 := by
    simpa [prefixWord, tailWord_3714535, baseEnd_3714535] using wordTrace_append hprefix tailTrace_3714535
  have hstable : (prefixWord ++ tailWord_3714535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714535).length < 2 ^ (prefixWord ++ tailWord_3714535).sum := by decide
  have hdescent : baseEnd_3714535 < baseStart_3714535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714608 : List Nat := [2, 1, 1, 1, 2, 3, 1, 6, 5]
def baseStart_3714608 : Nat := 118140960795 + 3714608 * 2 ^ 59
def prefixEnd_3714608 : Nat := 4983230072969 + 3 ^ 40 * 3714608 * 2
def baseEnd_3714608 : Nat := 423862077119223958403741

theorem tailTrace_3714608 : CollatzResearch.WordTrace tailWord_3714608 prefixEnd_3714608 423862077119223958403741 := by
  unfold tailWord_3714608
  simp only [CollatzResearch.WordTrace]
  refine ⟨67741442063308547691992239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90321922751078063589322985 67741442063308547691992239)
  ·
    refine ⟨101612163094962821537988359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67741442063308547691992239 101612163094962821537988359)
    ·
      refine ⟨152418244642444232306982539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101612163094962821537988359 152418244642444232306982539)
      ·
        refine ⟨228627366963666348460473809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152418244642444232306982539 228627366963666348460473809)
        ·
          refine ⟨171470525222749761345355357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228627366963666348460473809 171470525222749761345355357)
          ·
            refine ⟨64301446958531160504508259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171470525222749761345355357 64301446958531160504508259)
            ·
              refine ⟨96452170437796740756762389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64301446958531160504508259 96452170437796740756762389)
              ·
                refine ⟨4521195489271722222973237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96452170437796740756762389 4521195489271722222973237)
                ·
                  refine ⟨423862077119223958403741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4521195489271722222973237 423862077119223958403741)
                  ·
                    rfl

theorem cell22_3714608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 5].length) (baseStart_3714608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714608 prefixEnd_3714608 := by exact prefixLift 3714608
  have htrace : WordTrace (prefixWord ++ tailWord_3714608) baseStart_3714608 baseEnd_3714608 := by
    simpa [prefixWord, tailWord_3714608, baseEnd_3714608] using wordTrace_append hprefix tailTrace_3714608
  have hstable : (prefixWord ++ tailWord_3714608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714608).length < 2 ^ (prefixWord ++ tailWord_3714608).sum := by decide
  have hdescent : baseEnd_3714608 < baseStart_3714608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714625 : List Nat := [1, 2, 5, 1, 1, 1, 3, 3, 5]
def baseStart_3714625 : Nat := 118140960795 + 3714625 * 2 ^ 59
def prefixEnd_3714625 : Nat := 4983230072969 + 3 ^ 40 * 3714625 * 2
def baseEnd_3714625 : Nat := 423864016935029832512057

theorem tailTrace_3714625 : CollatzResearch.WordTrace tailWord_3714625 prefixEnd_3714625 423864016935029832512057 := by
  unfold tailWord_3714625
  simp only [CollatzResearch.WordTrace]
  refine ⟨135483504167555507287353329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90322336111703671524902219 135483504167555507287353329)
  ·
    refine ⟨101612628125666630465514997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135483504167555507287353329 101612628125666630465514997)
    ·
      refine ⟨9526183886781246606142031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101612628125666630465514997 9526183886781246606142031)
      ·
        refine ⟨14289275830171869909213047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9526183886781246606142031 14289275830171869909213047)
        ·
          refine ⟨21433913745257804863819571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14289275830171869909213047 21433913745257804863819571)
          ·
            refine ⟨32150870617886707295729357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21433913745257804863819571 32150870617886707295729357)
            ·
              refine ⟨12056576481707515235898509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32150870617886707295729357 12056576481707515235898509)
              ·
                refine ⟨4521216180640318213461941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12056576481707515235898509 4521216180640318213461941)
                ·
                  refine ⟨423864016935029832512057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4521216180640318213461941 423864016935029832512057)
                  ·
                    rfl

theorem cell22_3714625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 5].length) (baseStart_3714625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714625 prefixEnd_3714625 := by exact prefixLift 3714625
  have htrace : WordTrace (prefixWord ++ tailWord_3714625) baseStart_3714625 baseEnd_3714625 := by
    simpa [prefixWord, tailWord_3714625, baseEnd_3714625] using wordTrace_append hprefix tailTrace_3714625
  have hstable : (prefixWord ++ tailWord_3714625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714625).length < 2 ^ (prefixWord ++ tailWord_3714625).sum := by decide
  have hdescent : baseEnd_3714625 < baseStart_3714625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714668 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 5, 5]
def baseStart_3714668 : Nat := 118140960795 + 3714668 * 2 ^ 59
def prefixEnd_3714668 : Nat := 4983230072969 + 3 ^ 40 * 3714668 * 2
def baseEnd_3714668 : Nat := 1271606770583851718711039

theorem tailTrace_3714668 : CollatzResearch.WordTrace tailWord_3714668 prefixEnd_3714668 1271606770583851718711039 := by
  unfold tailWord_3714668
  simp only [CollatzResearch.WordTrace]
  refine ⟨67742536253199862815584329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90323381670933150420779105 67742536253199862815584329)
  ·
    refine ⟨50806902189899897111688247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67742536253199862815584329 50806902189899897111688247)
    ·
      refine ⟨76210353284849845667532371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50806902189899897111688247 76210353284849845667532371)
      ·
        refine ⟨114315529927274768501298557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76210353284849845667532371 114315529927274768501298557)
        ·
          refine ⟨42868323722728038187986959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114315529927274768501298557 42868323722728038187986959)
          ·
            refine ⟨64302485584092057281980439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42868323722728038187986959 64302485584092057281980439)
            ·
              refine ⟨96453728376138085922970659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64302485584092057281980439 96453728376138085922970659)
              ·
                refine ⟨144680592564207128884455989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96453728376138085922970659 144680592564207128884455989)
                ·
                  refine ⟨13563805552894418332917749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144680592564207128884455989 13563805552894418332917749)
                  ·
                    refine ⟨1271606770583851718711039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13563805552894418332917749 1271606770583851718711039)
                    ·
                      rfl

theorem cell22_3714668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_3714668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714668 prefixEnd_3714668 := by exact prefixLift 3714668
  have htrace : WordTrace (prefixWord ++ tailWord_3714668) baseStart_3714668 baseEnd_3714668 := by
    simpa [prefixWord, tailWord_3714668, baseEnd_3714668] using wordTrace_append hprefix tailTrace_3714668
  have hstable : (prefixWord ++ tailWord_3714668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714668).length < 2 ^ (prefixWord ++ tailWord_3714668).sum := by decide
  have hdescent : baseEnd_3714668 < baseStart_3714668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714683 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 1, 6]
def baseStart_3714683 : Nat := 118140960795 + 3714683 * 2 ^ 59
def prefixEnd_3714683 : Nat := 4983230072969 + 3 ^ 40 * 3714683 * 2
def baseEnd_3714683 : Nat := 1271611905390396679585993

theorem tailTrace_3714683 : CollatzResearch.WordTrace tailWord_3714683 prefixEnd_3714683 1271611905390396679585993 := by
  unfold tailWord_3714683
  simp only [CollatzResearch.WordTrace]
  refine ⟨135485619601345383192964703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90323746400896922128643135 135485619601345383192964703)
  ·
    refine ⟨203228429402018074789447055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135485619601345383192964703 203228429402018074789447055)
    ·
      refine ⟨304842644103027112184170583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203228429402018074789447055 304842644103027112184170583)
      ·
        refine ⟨457263966154540668276255875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304842644103027112184170583 457263966154540668276255875)
        ·
          refine ⟨685895949231811002414383813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457263966154540668276255875 685895949231811002414383813)
          ·
            refine ⟨128605490480964562952696965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 685895949231811002414383813 128605490480964562952696965)
            ·
              refine ⟨24113529465180855553630681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128605490480964562952696965 24113529465180855553630681)
              ·
                refine ⟨18085147098885641665223011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24113529465180855553630681 18085147098885641665223011)
                ·
                  refine ⟨27127720648328462497834517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18085147098885641665223011 27127720648328462497834517)
                  ·
                    refine ⟨1271611905390396679585993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27127720648328462497834517 1271611905390396679585993)
                    ·
                      rfl

theorem cell22_3714683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 6].length) (baseStart_3714683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714683 prefixEnd_3714683 := by exact prefixLift 3714683
  have htrace : WordTrace (prefixWord ++ tailWord_3714683) baseStart_3714683 baseEnd_3714683 := by
    simpa [prefixWord, tailWord_3714683, baseEnd_3714683] using wordTrace_append hprefix tailTrace_3714683
  have hstable : (prefixWord ++ tailWord_3714683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714683).length < 2 ^ (prefixWord ++ tailWord_3714683).sum := by decide
  have hdescent : baseEnd_3714683 < baseStart_3714683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714685 : List Nat := [1, 4, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_3714685 : Nat := 118140960795 + 3714685 * 2 ^ 59
def prefixEnd_3714685 : Nat := 4983230072969 + 3 ^ 40 * 3714685 * 2
def baseEnd_3714685 : Nat := 1271612590031269341035987

theorem tailTrace_3714685 : CollatzResearch.WordTrace tailWord_3714685 prefixEnd_3714685 1271612590031269341035987 := by
  unfold tailWord_3714685
  simp only [CollatzResearch.WordTrace]
  refine ⟨135485692547338137534537509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90323795031558758356358339 135485692547338137534537509)
  ·
    refine ⟨25403567352625900787725783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135485692547338137534537509 25403567352625900787725783)
    ·
      refine ⟨38105351028938851181588675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25403567352625900787725783 38105351028938851181588675)
      ·
        refine ⟨57158026543408276772383013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38105351028938851181588675 57158026543408276772383013)
        ·
          refine ⟨10717129976889051894821815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57158026543408276772383013 10717129976889051894821815)
          ·
            refine ⟨16075694965333577842232723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10717129976889051894821815 16075694965333577842232723)
            ·
              refine ⟨24113542448000366763349085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16075694965333577842232723 24113542448000366763349085)
              ·
                refine ⟨9042578418000137536255907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24113542448000366763349085 9042578418000137536255907)
                ·
                  refine ⟨13563867627000206304383861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9042578418000137536255907 13563867627000206304383861)
                  ·
                    refine ⟨1271612590031269341035987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13563867627000206304383861 1271612590031269341035987)
                    ·
                      rfl

theorem cell22_3714685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_3714685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714685 prefixEnd_3714685 := by exact prefixLift 3714685
  have htrace : WordTrace (prefixWord ++ tailWord_3714685) baseStart_3714685 baseEnd_3714685 := by
    simpa [prefixWord, tailWord_3714685, baseEnd_3714685] using wordTrace_append hprefix tailTrace_3714685
  have hstable : (prefixWord ++ tailWord_3714685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714685).length < 2 ^ (prefixWord ++ tailWord_3714685).sum := by decide
  have hdescent : baseEnd_3714685 < baseStart_3714685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714706 : List Nat := [3, 2, 3, 1, 3, 2, 2, 1, 1, 4]
def baseStart_3714706 : Nat := 118140960795 + 3714706 * 2 ^ 59
def prefixEnd_3714706 : Nat := 4983230072969 + 3 ^ 40 * 3714706 * 2
def baseEnd_3714706 : Nat := 1271619778760432286260923

theorem tailTrace_3714706 : CollatzResearch.WordTrace tailWord_3714706 prefixEnd_3714706 1271619778760432286260923 := by
  unfold tailWord_3714706
  simp only [CollatzResearch.WordTrace]
  refine ⟨33871614620065514530262993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90324305653508038747367981 33871614620065514530262993)
  ·
    refine ⟨25403710965049135897697245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33871614620065514530262993 25403710965049135897697245)
    ·
      refine ⟨9526391611893425961636467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25403710965049135897697245 9526391611893425961636467)
      ·
        refine ⟨14289587417840138942454701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9526391611893425961636467 14289587417840138942454701)
        ·
          refine ⟨5358595281690052103420513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14289587417840138942454701 5358595281690052103420513)
          ·
            refine ⟨4018946461267539077565385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5358595281690052103420513 4018946461267539077565385)
            ·
              refine ⟨3014209845950654308174039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4018946461267539077565385 3014209845950654308174039)
              ·
                refine ⟨4521314768925981462261059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3014209845950654308174039 4521314768925981462261059)
                ·
                  refine ⟨6781972153388972193391589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4521314768925981462261059 6781972153388972193391589)
                  ·
                    refine ⟨1271619778760432286260923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6781972153388972193391589 1271619778760432286260923)
                    ·
                      rfl

theorem cell22_3714706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_3714706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714706 prefixEnd_3714706 := by exact prefixLift 3714706
  have htrace : WordTrace (prefixWord ++ tailWord_3714706) baseStart_3714706 baseEnd_3714706 := by
    simpa [prefixWord, tailWord_3714706, baseEnd_3714706] using wordTrace_append hprefix tailTrace_3714706
  have hstable : (prefixWord ++ tailWord_3714706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714706).length < 2 ^ (prefixWord ++ tailWord_3714706).sum := by decide
  have hdescent : baseEnd_3714706 < baseStart_3714706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714719 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 4, 3]
def baseStart_3714719 : Nat := 118140960795 + 3714719 * 2 ^ 59
def prefixEnd_3714719 : Nat := 4983230072969 + 3 ^ 40 * 3714719 * 2
def baseEnd_3714719 : Nat := 1271624228926104585685883

theorem tailTrace_3714719 : CollatzResearch.WordTrace tailWord_3714719 prefixEnd_3714719 1271624228926104585685883 := by
  unfold tailWord_3714719
  simp only [CollatzResearch.WordTrace]
  refine ⟨135486932629214961341275211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90324621752809974227516807 135486932629214961341275211)
  ·
    refine ⟨203230398943822442011912817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135486932629214961341275211 203230398943822442011912817)
    ·
      refine ⟨152422799207866831508934613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203230398943822442011912817 152422799207866831508934613)
      ·
        refine ⟨3572409356434378863490655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 152422799207866831508934613 3572409356434378863490655)
        ·
          refine ⟨5358614034651568295235983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3572409356434378863490655 5358614034651568295235983)
          ·
            refine ⟨8037921051977352442853975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5358614034651568295235983 8037921051977352442853975)
            ·
              refine ⟨12056881577966028664280963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8037921051977352442853975 12056881577966028664280963)
              ·
                refine ⟨18085322366949042996421445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12056881577966028664280963 18085322366949042996421445)
                ·
                  refine ⟨3390997943802945561829021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18085322366949042996421445 3390997943802945561829021)
                  ·
                    refine ⟨1271624228926104585685883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3390997943802945561829021 1271624228926104585685883)
                    ·
                      rfl

theorem cell22_3714719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 3].length) (baseStart_3714719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714719 prefixEnd_3714719 := by exact prefixLift 3714719
  have htrace : WordTrace (prefixWord ++ tailWord_3714719) baseStart_3714719 baseEnd_3714719 := by
    simpa [prefixWord, tailWord_3714719, baseEnd_3714719] using wordTrace_append hprefix tailTrace_3714719
  have hstable : (prefixWord ++ tailWord_3714719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714719).length < 2 ^ (prefixWord ++ tailWord_3714719).sum := by decide
  have hdescent : baseEnd_3714719 < baseStart_3714719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714807 : List Nat := [1, 1, 3, 1, 1, 1, 7, 2, 1, 4]
def baseStart_3714807 : Nat := 118140960795 + 3714807 * 2 ^ 59
def prefixEnd_3714807 : Nat := 4983230072969 + 3 ^ 40 * 3714807 * 2
def baseEnd_3714807 : Nat := 1271654353124501689485613

theorem tailTrace_3714807 : CollatzResearch.WordTrace tailWord_3714807 prefixEnd_3714807 1271654353124501689485613 := by
  unfold tailWord_3714807
  simp only [CollatzResearch.WordTrace]
  refine ⟨135490142252896152370478675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90326761501930768246985783 135490142252896152370478675)
  ·
    refine ⟨203235213379344228555718013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135490142252896152370478675 203235213379344228555718013)
    ·
      refine ⟨76213205017254085708394255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203235213379344228555718013 76213205017254085708394255)
      ·
        refine ⟨114319807525881128562591383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76213205017254085708394255 114319807525881128562591383)
        ·
          refine ⟨171479711288821692843887075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114319807525881128562591383 171479711288821692843887075)
          ·
            refine ⟨257219566933232539265830613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171479711288821692843887075 257219566933232539265830613)
            ·
              refine ⟨6028583599997637639042905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 257219566933232539265830613 6028583599997637639042905)
              ·
                refine ⟨4521437699998228229282179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6028583599997637639042905 4521437699998228229282179)
                ·
                  refine ⟨6782156549997342343923269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4521437699998228229282179 6782156549997342343923269)
                  ·
                    refine ⟨1271654353124501689485613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6782156549997342343923269 1271654353124501689485613)
                    ·
                      rfl

theorem cell22_3714807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_3714807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714807 prefixEnd_3714807 := by exact prefixLift 3714807
  have htrace : WordTrace (prefixWord ++ tailWord_3714807) baseStart_3714807 baseEnd_3714807 := by
    simpa [prefixWord, tailWord_3714807, baseEnd_3714807] using wordTrace_append hprefix tailTrace_3714807
  have hstable : (prefixWord ++ tailWord_3714807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714807).length < 2 ^ (prefixWord ++ tailWord_3714807).sum := by decide
  have hdescent : baseEnd_3714807 < baseStart_3714807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714824 : List Nat := [2, 1, 3, 2, 2, 1, 5, 1, 1, 4]
def baseStart_3714824 : Nat := 118140960795 + 3714824 * 2 ^ 59
def prefixEnd_3714824 : Nat := 4983230072969 + 3 ^ 40 * 3714824 * 2
def baseEnd_3714824 : Nat := 1271660172571919311810561

theorem tailTrace_3714824 : CollatzResearch.WordTrace tailWord_3714824 prefixEnd_3714824 1271660172571919311810561 := by
  unfold tailWord_3714824
  simp only [CollatzResearch.WordTrace]
  refine ⟨67745381146917282136923763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90327174862556376182565017 67745381146917282136923763)
  ·
    refine ⟨101618071720375923205385645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67745381146917282136923763 101618071720375923205385645)
    ·
      refine ⟨38106776895140971202019617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101618071720375923205385645 38106776895140971202019617)
      ·
        refine ⟨28580082671355728401514713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38106776895140971202019617 28580082671355728401514713)
        ·
          refine ⟨21435062003516796301136035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28580082671355728401514713 21435062003516796301136035)
          ·
            refine ⟨32152593005275194451704053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21435062003516796301136035 32152593005275194451704053)
            ·
              refine ⟨3014305594244549479847255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32152593005275194451704053 3014305594244549479847255)
              ·
                refine ⟨4521458391366824219770883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3014305594244549479847255 4521458391366824219770883)
                ·
                  refine ⟨6782187587050236329656325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4521458391366824219770883 6782187587050236329656325)
                  ·
                    refine ⟨1271660172571919311810561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6782187587050236329656325 1271660172571919311810561)
                    ·
                      rfl

theorem cell22_3714824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_3714824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714824 prefixEnd_3714824 := by exact prefixLift 3714824
  have htrace : WordTrace (prefixWord ++ tailWord_3714824) baseStart_3714824 baseEnd_3714824 := by
    simpa [prefixWord, tailWord_3714824, baseEnd_3714824] using wordTrace_append hprefix tailTrace_3714824
  have hstable : (prefixWord ++ tailWord_3714824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714824).length < 2 ^ (prefixWord ++ tailWord_3714824).sum := by decide
  have hdescent : baseEnd_3714824 < baseStart_3714824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714835 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 4, 4]
def baseStart_3714835 : Nat := 118140960795 + 3714835 * 2 ^ 59
def prefixEnd_3714835 : Nat := 4983230072969 + 3 ^ 40 * 3714835 * 2
def baseEnd_3714835 : Nat := 1271663938096718949785527

theorem tailTrace_3714835 : CollatzResearch.WordTrace tailWord_3714835 prefixEnd_3714835 1271663938096718949785527 := by
  unfold tailWord_3714835
  simp only [CollatzResearch.WordTrace]
  refine ⟨135491163496794713152497959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90327442331196475434998639 135491163496794713152497959)
  ·
    refine ⟨203236745245192069728746939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135491163496794713152497959 203236745245192069728746939)
    ·
      refine ⟨304855117867788104593120409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203236745245192069728746939 304855117867788104593120409)
      ·
        refine ⟨228641338400841078444840307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304855117867788104593120409 228641338400841078444840307)
        ·
          refine ⟨342962007601261617667260461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228641338400841078444840307 342962007601261617667260461)
          ·
            refine ⟨128610752850473106625222673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342962007601261617667260461 128610752850473106625222673)
            ·
              refine ⟨96458064637854829968917005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128610752850473106625222673 96458064637854829968917005)
              ·
                refine ⟨36171774239195561238343877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96458064637854829968917005 36171774239195561238343877)
                ·
                  refine ⟨6782207669849167732189477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36171774239195561238343877 6782207669849167732189477)
                  ·
                    refine ⟨1271663938096718949785527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6782207669849167732189477 1271663938096718949785527)
                    ·
                      rfl

theorem cell22_3714835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 4].length) (baseStart_3714835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714835 prefixEnd_3714835 := by exact prefixLift 3714835
  have htrace : WordTrace (prefixWord ++ tailWord_3714835) baseStart_3714835 baseEnd_3714835 := by
    simpa [prefixWord, tailWord_3714835, baseEnd_3714835] using wordTrace_append hprefix tailTrace_3714835
  have hstable : (prefixWord ++ tailWord_3714835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714835).length < 2 ^ (prefixWord ++ tailWord_3714835).sum := by decide
  have hdescent : baseEnd_3714835 < baseStart_3714835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714839 : List Nat := [1, 1, 3, 4, 2, 2, 1, 4, 4]
def baseStart_3714839 : Nat := 118140960795 + 3714839 * 2 ^ 59
def prefixEnd_3714839 : Nat := 4983230072969 + 3 ^ 40 * 3714839 * 2
def baseEnd_3714839 : Nat := 423888435792821424228505

theorem tailTrace_3714839 : CollatzResearch.WordTrace tailWord_3714839 prefixEnd_3714839 423888435792821424228505 := by
  unfold tailWord_3714839
  simp only [CollatzResearch.WordTrace]
  refine ⟨135491309388780221835643571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90327539592520147890429047 135491309388780221835643571)
  ·
    refine ⟨203236964083170332753465357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135491309388780221835643571 203236964083170332753465357)
    ·
      refine ⟨76213861531188874782549509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203236964083170332753465357 76213861531188874782549509)
      ·
        refine ⟨14290099037097914021728033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76213861531188874782549509 14290099037097914021728033)
        ·
          refine ⟨10717574277823435516296025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14290099037097914021728033 10717574277823435516296025)
          ·
            refine ⟨8038180708367576637222019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10717574277823435516296025 8038180708367576637222019)
            ·
              refine ⟨12057271062551364955833029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8038180708367576637222019 12057271062551364955833029)
              ·
                refine ⟨2260738324228380929218693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12057271062551364955833029 2260738324228380929218693)
                ·
                  refine ⟨423888435792821424228505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2260738324228380929218693 423888435792821424228505)
                  ·
                    rfl

theorem cell22_3714839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 4].length) (baseStart_3714839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3714839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3714839 prefixEnd_3714839 := by exact prefixLift 3714839
  have htrace : WordTrace (prefixWord ++ tailWord_3714839) baseStart_3714839 baseEnd_3714839 := by
    simpa [prefixWord, tailWord_3714839, baseEnd_3714839] using wordTrace_append hprefix tailTrace_3714839
  have hstable : (prefixWord ++ tailWord_3714839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714839).length < 2 ^ (prefixWord ++ tailWord_3714839).sum := by decide
  have hdescent : baseEnd_3714839 < baseStart_3714839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715006 : List Nat := [4, 2, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_3715006 : Nat := 118140960795 + 3715006 * 2 ^ 59
def prefixEnd_3715006 : Nat := 4983230072969 + 3 ^ 40 * 3715006 * 2
def baseEnd_3715006 : Nat := 1271722474891331503760003

theorem tailTrace_3715006 : CollatzResearch.WordTrace tailWord_3715006 prefixEnd_3715006 1271722474891331503760003 := by
  unfold tailWord_3715006
  simp only [CollatzResearch.WordTrace]
  refine ⟨16937175047396901169621609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90331600252783472904648581 16937175047396901169621609)
  ·
    refine ⟨12702881285547675877216207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16937175047396901169621609 12702881285547675877216207)
    ·
      refine ⟨19054321928321513815824311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12702881285547675877216207 19054321928321513815824311)
      ·
        refine ⟨28581482892482270723736467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19054321928321513815824311 28581482892482270723736467)
        ·
          refine ⟨42872224338723406085604701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28581482892482270723736467 42872224338723406085604701)
          ·
            refine ⟨16077084127021277282101763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42872224338723406085604701 16077084127021277282101763)
            ·
              refine ⟨24115626190531915923152645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16077084127021277282101763 24115626190531915923152645)
              ·
                refine ⟨4521679910724734235591121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24115626190531915923152645 4521679910724734235591121)
                ·
                  refine ⟨3391259933043550676693341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4521679910724734235591121 3391259933043550676693341)
                  ·
                    refine ⟨1271722474891331503760003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3391259933043550676693341 1271722474891331503760003)
                    ·
                      rfl

theorem cell22_3715006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_3715006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715006 prefixEnd_3715006 := by exact prefixLift 3715006
  have htrace : WordTrace (prefixWord ++ tailWord_3715006) baseStart_3715006 baseEnd_3715006 := by
    simpa [prefixWord, tailWord_3715006, baseEnd_3715006] using wordTrace_append hprefix tailTrace_3715006
  have hstable : (prefixWord ++ tailWord_3715006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715006).length < 2 ^ (prefixWord ++ tailWord_3715006).sum := by decide
  have hdescent : baseEnd_3715006 < baseStart_3715006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715032 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 2, 6]
def baseStart_3715032 : Nat := 118140960795 + 3715032 * 2 ^ 59
def prefixEnd_3715032 : Nat := 4983230072969 + 3 ^ 40 * 3715032 * 2
def baseEnd_3715032 : Nat := 1271731375222676102609923

theorem tailTrace_3715032 : CollatzResearch.WordTrace tailWord_3715032 prefixEnd_3715032 1271731375222676102609923 := by
  unfold tailWord_3715032
  simp only [CollatzResearch.WordTrace]
  refine ⟨67749174338540507898709675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90332232451387343864946233 67749174338540507898709675)
  ·
    refine ⟨101623761507810761848064513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67749174338540507898709675 101623761507810761848064513)
    ·
      refine ⟨76217821130858071386048385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101623761507810761848064513 76217821130858071386048385)
      ·
        refine ⟨57163365848143553539536289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76217821130858071386048385 57163365848143553539536289)
        ·
          refine ⟨42872524386107665154652217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57163365848143553539536289 42872524386107665154652217)
          ·
            refine ⟨32154393289580748865989163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42872524386107665154652217 32154393289580748865989163)
            ·
              refine ⟨48231589934371123298983745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32154393289580748865989163 48231589934371123298983745)
              ·
                refine ⟨36173692450778342474237809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48231589934371123298983745 36173692450778342474237809)
                ·
                  refine ⟨27130269338083756855678357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36173692450778342474237809 27130269338083756855678357)
                  ·
                    refine ⟨1271731375222676102609923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27130269338083756855678357 1271731375222676102609923)
                    ·
                      rfl

theorem cell22_3715032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_3715032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715032 prefixEnd_3715032 := by exact prefixLift 3715032
  have htrace : WordTrace (prefixWord ++ tailWord_3715032) baseStart_3715032 baseEnd_3715032 := by
    simpa [prefixWord, tailWord_3715032, baseEnd_3715032] using wordTrace_append hprefix tailTrace_3715032
  have hstable : (prefixWord ++ tailWord_3715032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715032).length < 2 ^ (prefixWord ++ tailWord_3715032).sum := by decide
  have hdescent : baseEnd_3715032 < baseStart_3715032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715064 : List Nat := [2, 1, 2, 1, 1, 3, 5, 2, 5]
def baseStart_3715064 : Nat := 118140960795 + 3715064 * 2 ^ 59
def prefixEnd_3715064 : Nat := 4983230072969 + 3 ^ 40 * 3715064 * 2
def baseEnd_3715064 : Nat := 423914109825546228603275

theorem tailTrace_3715064 : CollatzResearch.WordTrace tailWord_3715064 prefixEnd_3715064 423914109825546228603275 := by
  unfold tailWord_3715064
  simp only [CollatzResearch.WordTrace]
  refine ⟨67749757906482542631292123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90333010541976723508389497 67749757906482542631292123)
  ·
    refine ⟨101624636859723813946938185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67749757906482542631292123 101624636859723813946938185)
    ·
      refine ⟨76218477644792860460203639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101624636859723813946938185 76218477644792860460203639)
      ·
        refine ⟨114327716467189290690305459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76218477644792860460203639 114327716467189290690305459)
        ·
          refine ⟨171491574700783936035458189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114327716467189290690305459 171491574700783936035458189)
          ·
            refine ⟨64309340512793976013296821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171491574700783936035458189 64309340512793976013296821)
            ·
              refine ⟨6029000673074435251246577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64309340512793976013296821 6029000673074435251246577)
              ·
                refine ⟨4521750504805826438434933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6029000673074435251246577 4521750504805826438434933)
                ·
                  refine ⟨423914109825546228603275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4521750504805826438434933 423914109825546228603275)
                  ·
                    rfl

theorem cell22_3715064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 5].length) (baseStart_3715064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715064 prefixEnd_3715064 := by exact prefixLift 3715064
  have htrace : WordTrace (prefixWord ++ tailWord_3715064) baseStart_3715064 baseEnd_3715064 := by
    simpa [prefixWord, tailWord_3715064, baseEnd_3715064] using wordTrace_append hprefix tailTrace_3715064
  have hstable : (prefixWord ++ tailWord_3715064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715064).length < 2 ^ (prefixWord ++ tailWord_3715064).sum := by decide
  have hdescent : baseEnd_3715064 < baseStart_3715064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715079 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 2, 5]
def baseStart_3715079 : Nat := 118140960795 + 3715079 * 2 ^ 59
def prefixEnd_3715079 : Nat := 4983230072969 + 3 ^ 40 * 3715079 * 2
def baseEnd_3715079 : Nat := 1271747464283183646684779

theorem tailTrace_3715079 : CollatzResearch.WordTrace tailWord_3715079 prefixEnd_3715079 1271747464283183646684779 := by
  unfold tailWord_3715079
  simp only [CollatzResearch.WordTrace]
  refine ⟨135500062907910742824380291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90333375271940495216253527 135500062907910742824380291)
  ·
    refine ⟨203250094361866114236570437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135500062907910742824380291 203250094361866114236570437)
    ·
      refine ⟨38109392692849896419356957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203250094361866114236570437 38109392692849896419356957)
      ·
        refine ⟨14291022259818711157258859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38109392692849896419356957 14291022259818711157258859)
        ·
          refine ⟨21436533389728066735888289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14291022259818711157258859 21436533389728066735888289)
          ·
            refine ⟨16077400042296050051916217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21436533389728066735888289 16077400042296050051916217)
            ·
              refine ⟨12058050031722037538937163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16077400042296050051916217 12058050031722037538937163)
              ·
                refine ⟨18087075047583056308405745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12058050031722037538937163 18087075047583056308405745)
                ·
                  refine ⟨13565306285687292231304309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18087075047583056308405745 13565306285687292231304309)
                  ·
                    refine ⟨1271747464283183646684779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13565306285687292231304309 1271747464283183646684779)
                    ·
                      rfl

theorem cell22_3715079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_3715079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715079 prefixEnd_3715079 := by exact prefixLift 3715079
  have htrace : WordTrace (prefixWord ++ tailWord_3715079) baseStart_3715079 baseEnd_3715079 := by
    simpa [prefixWord, tailWord_3715079, baseEnd_3715079] using wordTrace_append hprefix tailTrace_3715079
  have hstable : (prefixWord ++ tailWord_3715079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715079).length < 2 ^ (prefixWord ++ tailWord_3715079).sum := by decide
  have hdescent : baseEnd_3715079 < baseStart_3715079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715158 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_3715158 : Nat := 118140960795 + 3715158 * 2 ^ 59
def prefixEnd_3715158 : Nat := 4983230072969 + 3 ^ 40 * 3715158 * 2
def baseEnd_3715158 : Nat := 1271774507597653773959537

theorem tailTrace_3715158 : CollatzResearch.WordTrace tailWord_3715158 prefixEnd_3715158 1271774507597653773959537 := by
  unfold tailWord_3715158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8468934017164033707281633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90335296183083026211004085 8468934017164033707281633)
  ·
    refine ⟨6351700512873025280461225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8468934017164033707281633 6351700512873025280461225)
    ·
      refine ⟨4763775384654768960345919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6351700512873025280461225 4763775384654768960345919)
      ·
        refine ⟨7145663076982153440518879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4763775384654768960345919 7145663076982153440518879)
        ·
          refine ⟨10718494615473230160778319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7145663076982153440518879 10718494615473230160778319)
          ·
            refine ⟨16077741923209845241167479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10718494615473230160778319 16077741923209845241167479)
            ·
              refine ⟨24116612884814767861751219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16077741923209845241167479 24116612884814767861751219)
              ·
                refine ⟨36174919327222151792626829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24116612884814767861751219 36174919327222151792626829)
                ·
                  refine ⟨13565594747708306922235061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36174919327222151792626829 13565594747708306922235061)
                  ·
                    refine ⟨1271774507597653773959537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13565594747708306922235061 1271774507597653773959537)
                    ·
                      rfl

theorem cell22_3715158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_3715158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715158 prefixEnd_3715158 := by exact prefixLift 3715158
  have htrace : WordTrace (prefixWord ++ tailWord_3715158) baseStart_3715158 baseEnd_3715158 := by
    simpa [prefixWord, tailWord_3715158, baseEnd_3715158] using wordTrace_append hprefix tailTrace_3715158
  have hstable : (prefixWord ++ tailWord_3715158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715158).length < 2 ^ (prefixWord ++ tailWord_3715158).sum := by decide
  have hdescent : baseEnd_3715158 < baseStart_3715158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715184 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 2, 6]
def baseStart_3715184 : Nat := 118140960795 + 3715184 * 2 ^ 59
def prefixEnd_3715184 : Nat := 4983230072969 + 3 ^ 40 * 3715184 * 2
def baseEnd_3715184 : Nat := 1271783407928998372809457

theorem tailTrace_3715184 : CollatzResearch.WordTrace tailWord_3715184 prefixEnd_3715184 1271783407928998372809457 := by
  unfold tailWord_3715184
  simp only [CollatzResearch.WordTrace]
  refine ⟨67751946286265172878476303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90335928381686897171301737 67751946286265172878476303)
  ·
    refine ⟨101627919429397759317714455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67751946286265172878476303 101627919429397759317714455)
    ·
      refine ⟨152441879144096638976571683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101627919429397759317714455 152441879144096638976571683)
      ·
        refine ⟨228662818716144958464857525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152441879144096638976571683 228662818716144958464857525)
        ·
          refine ⟨21437139254638589856080393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 228662818716144958464857525 21437139254638589856080393)
          ·
            refine ⟨16077854440978942392060295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21437139254638589856080393 16077854440978942392060295)
            ·
              refine ⟨24116781661468413588090443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16077854440978942392060295 24116781661468413588090443)
              ·
                refine ⟨36175172492202620382135665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24116781661468413588090443 36175172492202620382135665)
                ·
                  refine ⟨27131379369151965286601749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36175172492202620382135665 27131379369151965286601749)
                  ·
                    refine ⟨1271783407928998372809457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27131379369151965286601749 1271783407928998372809457)
                    ·
                      rfl

theorem cell22_3715184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_3715184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715184 prefixEnd_3715184 := by exact prefixLift 3715184
  have htrace : WordTrace (prefixWord ++ tailWord_3715184) baseStart_3715184 baseEnd_3715184 := by
    simpa [prefixWord, tailWord_3715184, baseEnd_3715184] using wordTrace_append hprefix tailTrace_3715184
  have hstable : (prefixWord ++ tailWord_3715184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715184).length < 2 ^ (prefixWord ++ tailWord_3715184).sum := by decide
  have hdescent : baseEnd_3715184 < baseStart_3715184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715222 : List Nat := [5, 3, 2, 1, 1, 1, 9]
def baseStart_3715222 : Nat := 118140960795 + 3715222 * 2 ^ 59
def prefixEnd_3715222 : Nat := 4983230072969 + 3 ^ 40 * 3715222 * 2
def baseEnd_3715222 : Nat := 47103570966873294087383

theorem tailTrace_3715222 : CollatzResearch.WordTrace tailWord_3715222 prefixEnd_3715222 47103570966873294087383 := by
  unfold tailWord_3715222
  simp only [CollatzResearch.WordTrace]
  refine ⟨8469079909149542390427245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90336852364261785497890613 8469079909149542390427245)
  ·
    refine ⟨3175904965931078396410217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8469079909149542390427245 3175904965931078396410217)
    ·
      refine ⟨2381928724448308797307663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3175904965931078396410217 2381928724448308797307663)
      ·
        refine ⟨3572893086672463195961495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2381928724448308797307663 3572893086672463195961495)
        ·
          refine ⟨5359339630008694793942243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3572893086672463195961495 5359339630008694793942243)
          ·
            refine ⟨8039009445013042190913365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5359339630008694793942243 8039009445013042190913365)
            ·
              refine ⟨47103570966873294087383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8039009445013042190913365 47103570966873294087383)
              ·
                rfl

theorem cell22_3715222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 9].length) (baseStart_3715222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715222 prefixEnd_3715222 := by exact prefixLift 3715222
  have htrace : WordTrace (prefixWord ++ tailWord_3715222) baseStart_3715222 baseEnd_3715222 := by
    simpa [prefixWord, tailWord_3715222, baseEnd_3715222] using wordTrace_append hprefix tailTrace_3715222
  have hstable : (prefixWord ++ tailWord_3715222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715222).length < 2 ^ (prefixWord ++ tailWord_3715222).sum := by decide
  have hdescent : baseEnd_3715222 < baseStart_3715222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715231 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 2, 5]
def baseStart_3715231 : Nat := 118140960795 + 3715231 * 2 ^ 59
def prefixEnd_3715231 : Nat := 4983230072969 + 3 ^ 40 * 3715231 * 2
def baseEnd_3715231 : Nat := 1271799496989505916884313

theorem tailTrace_3715231 : CollatzResearch.WordTrace tailWord_3715231 prefixEnd_3715231 1271799496989505916884313 := by
  unfold tailWord_3715231
  simp only [CollatzResearch.WordTrace]
  refine ⟨135505606803360072783913547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90337071202240048522609031 135505606803360072783913547)
  ·
    refine ⟨203258410205040109175870321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135505606803360072783913547 203258410205040109175870321)
    ·
      refine ⟨152443807653780081881902741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203258410205040109175870321 152443807653780081881902741)
      ·
        refine ⟨7145803483770941338214191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152443807653780081881902741 7145803483770941338214191)
        ·
          refine ⟨10718705225656412007321287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7145803483770941338214191 10718705225656412007321287)
          ·
            refine ⟨16078057838484618010981931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10718705225656412007321287 16078057838484618010981931)
            ·
              refine ⟨24117086757726927016472897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16078057838484618010981931 24117086757726927016472897)
              ·
                refine ⟨18087815068295195262354673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24117086757726927016472897 18087815068295195262354673)
                ·
                  refine ⟨13565861301221396446766005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18087815068295195262354673 13565861301221396446766005)
                  ·
                    refine ⟨1271799496989505916884313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13565861301221396446766005 1271799496989505916884313)
                    ·
                      rfl

theorem cell22_3715231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_3715231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715231 prefixEnd_3715231 := by exact prefixLift 3715231
  have htrace : WordTrace (prefixWord ++ tailWord_3715231) baseStart_3715231 baseEnd_3715231 := by
    simpa [prefixWord, tailWord_3715231, baseEnd_3715231] using wordTrace_append hprefix tailTrace_3715231
  have hstable : (prefixWord ++ tailWord_3715231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715231).length < 2 ^ (prefixWord ++ tailWord_3715231).sum := by decide
  have hdescent : baseEnd_3715231 < baseStart_3715231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715233 : List Nat := [1, 2, 3, 3, 1, 4, 1, 2, 5]
def baseStart_3715233 : Nat := 118140960795 + 3715233 * 2 ^ 59
def prefixEnd_3715233 : Nat := 4983230072969 + 3 ^ 40 * 3715233 * 2
def baseEnd_3715233 : Nat := 423933393876792859444769

theorem tailTrace_3715233 : CollatzResearch.WordTrace tailWord_3715233 prefixEnd_3715233 423933393876792859444769 := by
  unfold tailWord_3715233
  simp only [CollatzResearch.WordTrace]
  refine ⟨135505679749352827125486353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90337119832901884750324235 135505679749352827125486353)
  ·
    refine ⟨101629259812014620344114765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135505679749352827125486353 101629259812014620344114765)
    ·
      refine ⟨38110972429505482629043037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101629259812014620344114765 38110972429505482629043037)
      ·
        refine ⟨14291614661064555985891139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38110972429505482629043037 14291614661064555985891139)
        ·
          refine ⟨21437421991596833978836709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14291614661064555985891139 21437421991596833978836709)
          ·
            refine ⟨4019516623424406371031883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21437421991596833978836709 4019516623424406371031883)
            ·
              refine ⟨6029274935136609556547825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4019516623424406371031883 6029274935136609556547825)
              ·
                refine ⟨4521956201352457167410869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6029274935136609556547825 4521956201352457167410869)
                ·
                  refine ⟨423933393876792859444769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4521956201352457167410869 423933393876792859444769)
                  ·
                    rfl

theorem cell22_3715233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 5].length) (baseStart_3715233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715233 prefixEnd_3715233 := by exact prefixLift 3715233
  have htrace : WordTrace (prefixWord ++ tailWord_3715233) baseStart_3715233 baseEnd_3715233 := by
    simpa [prefixWord, tailWord_3715233, baseEnd_3715233] using wordTrace_append hprefix tailTrace_3715233
  have hstable : (prefixWord ++ tailWord_3715233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715233).length < 2 ^ (prefixWord ++ tailWord_3715233).sum := by decide
  have hdescent : baseEnd_3715233 < baseStart_3715233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715289 : List Nat := [1, 2, 1, 2, 3, 1, 12]
def baseStart_3715289 : Nat := 118140960795 + 3715289 * 2 ^ 59
def prefixEnd_3715289 : Nat := 4983230072969 + 3 ^ 40 * 3715289 * 2
def baseEnd_3715289 : Nat := 47104420428696781442005

theorem tailTrace_3715289 : CollatzResearch.WordTrace tailWord_3715289 prefixEnd_3715289 47104420428696781442005 := by
  unfold tailWord_3715289
  simp only [CollatzResearch.WordTrace]
  refine ⟨135507722237149948689524921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90338481491433299126349947 135507722237149948689524921)
  ·
    refine ⟨101630791677862461517143691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135507722237149948689524921 101630791677862461517143691)
    ·
      refine ⟨152446187516793692275715537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101630791677862461517143691 152446187516793692275715537)
      ·
        refine ⟨114334640637595269206786653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152446187516793692275715537 114334640637595269206786653)
        ·
          refine ⟨42875490239098225952544995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114334640637595269206786653 42875490239098225952544995)
          ·
            refine ⟨64313235358647338928817493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42875490239098225952544995 64313235358647338928817493)
            ·
              refine ⟨47104420428696781442005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 64313235358647338928817493 47104420428696781442005)
              ·
                rfl

theorem cell22_3715289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 12].length) (baseStart_3715289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715289 prefixEnd_3715289 := by exact prefixLift 3715289
  have htrace : WordTrace (prefixWord ++ tailWord_3715289) baseStart_3715289 baseEnd_3715289 := by
    simpa [prefixWord, tailWord_3715289, baseEnd_3715289] using wordTrace_append hprefix tailTrace_3715289
  have hstable : (prefixWord ++ tailWord_3715289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715289).length < 2 ^ (prefixWord ++ tailWord_3715289).sum := by decide
  have hdescent : baseEnd_3715289 < baseStart_3715289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715306 : List Nat := [3, 1, 3, 1, 1, 2, 4, 7]
def baseStart_3715306 : Nat := 118140960795 + 3715306 * 2 ^ 59
def prefixEnd_3715306 : Nat := 4983230072969 + 3 ^ 40 * 3715306 * 2
def baseEnd_3715306 : Nat := 141313907891358969028787

theorem tailTrace_3715306 : CollatzResearch.WordTrace tailWord_3715306 prefixEnd_3715306 141313907891358969028787 := by
  unfold tailWord_3715306
  simp only [CollatzResearch.WordTrace]
  refine ⟨33877085569522090148223443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90338894852058907061929181 33877085569522090148223443)
  ·
    refine ⟨50815628354283135222335165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33877085569522090148223443 50815628354283135222335165)
    ·
      refine ⟨19055860632856175708375687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50815628354283135222335165 19055860632856175708375687)
      ·
        refine ⟨28583790949284263562563531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19055860632856175708375687 28583790949284263562563531)
        ·
          refine ⟨42875686423926395343845297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28583790949284263562563531 42875686423926395343845297)
          ·
            refine ⟨32156764817944796507883973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42875686423926395343845297 32156764817944796507883973)
            ·
              refine ⟨6029393403364649345228245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32156764817944796507883973 6029393403364649345228245)
              ·
                refine ⟨141313907891358969028787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6029393403364649345228245 141313907891358969028787)
                ·
                  rfl

theorem cell22_3715306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 7].length) (baseStart_3715306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715306 prefixEnd_3715306 := by exact prefixLift 3715306
  have htrace : WordTrace (prefixWord ++ tailWord_3715306) baseStart_3715306 baseEnd_3715306 := by
    simpa [prefixWord, tailWord_3715306, baseEnd_3715306] using wordTrace_append hprefix tailTrace_3715306
  have hstable : (prefixWord ++ tailWord_3715306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715306).length < 2 ^ (prefixWord ++ tailWord_3715306).sum := by decide
  have hdescent : baseEnd_3715306 < baseStart_3715306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715445 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 4, 3]
def baseStart_3715445 : Nat := 118140960795 + 3715445 * 2 ^ 59
def prefixEnd_3715445 : Nat := 4983230072969 + 3 ^ 40 * 3715445 * 2
def baseEnd_3715445 : Nat := 1271872753562880692033657

theorem tailTrace_3715445 : CollatzResearch.WordTrace tailWord_3715445 prefixEnd_3715445 1271872753562880692033657 := by
  unfold tailWord_3715445
  simp only [CollatzResearch.WordTrace]
  refine ⟨135513412024584787332203789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90342274683056524888135859 135513412024584787332203789)
  ·
    refine ⟨50817529509219295249576421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135513412024584787332203789 50817529509219295249576421)
    ·
      refine ⟨9528286782978617859295579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50817529509219295249576421 9528286782978617859295579)
      ·
        refine ⟨14292430174467926788943369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9528286782978617859295579 14292430174467926788943369)
        ·
          refine ⟨10719322630850945091707527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14292430174467926788943369 10719322630850945091707527)
          ·
            refine ⟨16078983946276417637561291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10719322630850945091707527 16078983946276417637561291)
            ·
              refine ⟨24118475919414626456341937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16078983946276417637561291 24118475919414626456341937)
              ·
                refine ⟨18088856939560969842256453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24118475919414626456341937 18088856939560969842256453)
                ·
                  refine ⟨3391660676167681845423085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18088856939560969842256453 3391660676167681845423085)
                  ·
                    refine ⟨1271872753562880692033657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3391660676167681845423085 1271872753562880692033657)
                    ·
                      rfl

theorem cell22_3715445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_3715445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715445 prefixEnd_3715445 := by exact prefixLift 3715445
  have htrace : WordTrace (prefixWord ++ tailWord_3715445) baseStart_3715445 baseEnd_3715445 := by
    simpa [prefixWord, tailWord_3715445, baseEnd_3715445] using wordTrace_append hprefix tailTrace_3715445
  have hstable : (prefixWord ++ tailWord_3715445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715445).length < 2 ^ (prefixWord ++ tailWord_3715445).sum := by decide
  have hdescent : baseEnd_3715445 < baseStart_3715445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715490 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_3715490 : Nat := 118140960795 + 3715490 * 2 ^ 59
def prefixEnd_3715490 : Nat := 4983230072969 + 3 ^ 40 * 3715490 * 2
def baseEnd_3715490 : Nat := 1271888157982515574658519

theorem tailTrace_3715490 : CollatzResearch.WordTrace tailWord_3715490 prefixEnd_3715490 1271888157982515574658519 := by
  unfold tailWord_3715490
  simp only [CollatzResearch.WordTrace]
  refine ⟨33878763327355440004397981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90343368872947840011727949 33878763327355440004397981)
  ·
    refine ⟨12704536247758290001649243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33878763327355440004397981 12704536247758290001649243)
    ·
      refine ⟨19056804371637435002473865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12704536247758290001649243 19056804371637435002473865)
      ·
        refine ⟨14292603278728076251855399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19056804371637435002473865 14292603278728076251855399)
        ·
          refine ⟨21438904918092114377783099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14292603278728076251855399 21438904918092114377783099)
          ·
            refine ⟨32158357377138171566674649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21438904918092114377783099 32158357377138171566674649)
            ·
              refine ⟨24118768032853628675005987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32158357377138171566674649 24118768032853628675005987)
              ·
                refine ⟨36178152049280443012508981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24118768032853628675005987 36178152049280443012508981)
                ·
                  refine ⟨3391701754620041532422717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36178152049280443012508981 3391701754620041532422717)
                  ·
                    refine ⟨1271888157982515574658519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3391701754620041532422717 1271888157982515574658519)
                    ·
                      rfl

theorem cell22_3715490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_3715490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715490 prefixEnd_3715490 := by exact prefixLift 3715490
  have htrace : WordTrace (prefixWord ++ tailWord_3715490) baseStart_3715490 baseEnd_3715490 := by
    simpa [prefixWord, tailWord_3715490, baseEnd_3715490] using wordTrace_append hprefix tailTrace_3715490
  have hstable : (prefixWord ++ tailWord_3715490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715490).length < 2 ^ (prefixWord ++ tailWord_3715490).sum := by decide
  have hdescent : baseEnd_3715490 < baseStart_3715490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715563 : List Nat := [1, 1, 1, 1, 2, 3, 3, 4, 1, 5]
def baseStart_3715563 : Nat := 118140960795 + 3715563 * 2 ^ 59
def prefixEnd_3715563 : Nat := 4983230072969 + 3 ^ 40 * 3715563 * 2
def baseEnd_3715563 : Nat := 1271913147374367717583295

theorem tailTrace_3715563 : CollatzResearch.WordTrace tailWord_3715563 prefixEnd_3715563 1271913147374367717583295 := by
  unfold tailWord_3715563
  simp only [CollatzResearch.WordTrace]
  refine ⟨135517715838157293484999343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90345143892104862323332895 135517715838157293484999343)
  ·
    refine ⟨203276573757235940227499015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135517715838157293484999343 203276573757235940227499015)
    ·
      refine ⟨304914860635853910341248523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203276573757235940227499015 304914860635853910341248523)
      ·
        refine ⟨457372290953780865511872785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304914860635853910341248523 457372290953780865511872785)
        ·
          refine ⟨343029218215335649133904589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457372290953780865511872785 343029218215335649133904589)
          ·
            refine ⟨128635956830750868425214221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343029218215335649133904589 128635956830750868425214221)
            ·
              refine ⟨48238483811531575659455333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128635956830750868425214221 48238483811531575659455333)
              ·
                refine ⟨9044715714662170436147875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48238483811531575659455333 9044715714662170436147875)
                ·
                  refine ⟨13567073571993255654221813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9044715714662170436147875 13567073571993255654221813)
                  ·
                    refine ⟨1271913147374367717583295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13567073571993255654221813 1271913147374367717583295)
                    ·
                      rfl

theorem cell22_3715563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 5].length) (baseStart_3715563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715563 prefixEnd_3715563 := by exact prefixLift 3715563
  have htrace : WordTrace (prefixWord ++ tailWord_3715563) baseStart_3715563 baseEnd_3715563 := by
    simpa [prefixWord, tailWord_3715563, baseEnd_3715563] using wordTrace_append hprefix tailTrace_3715563
  have hstable : (prefixWord ++ tailWord_3715563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715563).length < 2 ^ (prefixWord ++ tailWord_3715563).sum := by decide
  have hdescent : baseEnd_3715563 < baseStart_3715563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715610 : List Nat := [3, 1, 1, 3, 1, 1, 6, 6]
def baseStart_3715610 : Nat := 118140960795 + 3715610 * 2 ^ 59
def prefixEnd_3715610 : Nat := 4983230072969 + 3 ^ 40 * 3715610 * 2
def baseEnd_3715610 : Nat := 141325470714986140184239

theorem tailTrace_3715610 : CollatzResearch.WordTrace tailWord_3715610 prefixEnd_3715610 141325470714986140184239 := by
  unfold tailWord_3715610
  simp only [CollatzResearch.WordTrace]
  refine ⟨33879857517246755127990071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90346286712658013674640189 33879857517246755127990071)
  ·
    refine ⟨50819786275870132691985107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33879857517246755127990071 50819786275870132691985107)
    ·
      refine ⟨76229679413805199037977661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50819786275870132691985107 76229679413805199037977661)
      ·
        refine ⟨28586129780176949639241623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76229679413805199037977661 28586129780176949639241623)
        ·
          refine ⟨42879194670265424458862435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28586129780176949639241623 42879194670265424458862435)
          ·
            refine ⟨64318792005398136688293653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42879194670265424458862435 64318792005398136688293653)
            ·
              refine ⟨3014943375253037657263765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64318792005398136688293653 3014943375253037657263765)
              ·
                refine ⟨141325470714986140184239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3014943375253037657263765 141325470714986140184239)
                ·
                  rfl

theorem cell22_3715610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 6].length) (baseStart_3715610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715610 prefixEnd_3715610 := by exact prefixLift 3715610
  have htrace : WordTrace (prefixWord ++ tailWord_3715610) baseStart_3715610 baseEnd_3715610 := by
    simpa [prefixWord, tailWord_3715610, baseEnd_3715610] using wordTrace_append hprefix tailTrace_3715610
  have hstable : (prefixWord ++ tailWord_3715610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715610).length < 2 ^ (prefixWord ++ tailWord_3715610).sum := by decide
  have hdescent : baseEnd_3715610 < baseStart_3715610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715616 : List Nat := [2, 1, 1, 6, 3, 1, 1, 3, 4]
def baseStart_3715616 : Nat := 118140960795 + 3715616 * 2 ^ 59
def prefixEnd_3715616 : Nat := 4983230072969 + 3 ^ 40 * 3715616 * 2
def baseEnd_3715616 : Nat := 423977096785831082002711

theorem tailTrace_3715616 : CollatzResearch.WordTrace tailWord_3715616 prefixEnd_3715616 423977096785831082002711 := by
  unfold tailWord_3715616
  simp only [CollatzResearch.WordTrace]
  refine ⟨67759824453482641768339351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90346432604643522357785801 67759824453482641768339351)
  ·
    refine ⟨101639736680223962652509027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67759824453482641768339351 101639736680223962652509027)
    ·
      refine ⟨152459605020335943978763541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101639736680223962652509027 152459605020335943978763541)
      ·
        refine ⟨7146543985328247374004541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152459605020335943978763541 7146543985328247374004541)
        ·
          refine ⟨2679953994498092765251703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7146543985328247374004541 2679953994498092765251703)
          ·
            refine ⟨4019930991747139147877555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2679953994498092765251703 4019930991747139147877555)
            ·
              refine ⟨6029896487620708721816333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4019930991747139147877555 6029896487620708721816333)
              ·
                refine ⟨2261211182857765770681125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6029896487620708721816333 2261211182857765770681125)
                ·
                  refine ⟨423977096785831082002711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2261211182857765770681125 423977096785831082002711)
                  ·
                    rfl

theorem cell22_3715616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 4].length) (baseStart_3715616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715616 prefixEnd_3715616 := by exact prefixLift 3715616
  have htrace : WordTrace (prefixWord ++ tailWord_3715616) baseStart_3715616 baseEnd_3715616 := by
    simpa [prefixWord, tailWord_3715616, baseEnd_3715616] using wordTrace_append hprefix tailTrace_3715616
  have hstable : (prefixWord ++ tailWord_3715616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715616).length < 2 ^ (prefixWord ++ tailWord_3715616).sum := by decide
  have hdescent : baseEnd_3715616 < baseStart_3715616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715642 : List Nat := [3, 1, 1, 1, 3, 3, 3, 1, 3, 3]
def baseStart_3715642 : Nat := 118140960795 + 3715642 * 2 ^ 59
def prefixEnd_3715642 : Nat := 4983230072969 + 3 ^ 40 * 3715642 * 2
def baseEnd_3715642 : Nat := 1271940190688837844858053

theorem tailTrace_3715642 : CollatzResearch.WordTrace tailWord_3715642 prefixEnd_3715642 1271940190688837844858053 := by
  unfold tailWord_3715642
  simp only [CollatzResearch.WordTrace]
  refine ⟨33880149301217772494281295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90347064803247393318083453 33880149301217772494281295)
  ·
    refine ⟨50820223951826658741421943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33880149301217772494281295 50820223951826658741421943)
    ·
      refine ⟨76230335927739988112132915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50820223951826658741421943 76230335927739988112132915)
      ·
        refine ⟨114345503891609982168199373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76230335927739988112132915 114345503891609982168199373)
        ·
          refine ⟨42879563959353743313074765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114345503891609982168199373 42879563959353743313074765)
          ·
            refine ⟨16079836484757653742403037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42879563959353743313074765 16079836484757653742403037)
            ·
              refine ⟨6029938681784120153401139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16079836484757653742403037 6029938681784120153401139)
              ·
                refine ⟨9044908022676180230101709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6029938681784120153401139 9044908022676180230101709)
                ·
                  refine ⟨3391840508503567586288141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9044908022676180230101709 3391840508503567586288141)
                  ·
                    refine ⟨1271940190688837844858053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3391840508503567586288141 1271940190688837844858053)
                    ·
                      rfl

theorem cell22_3715642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_3715642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715642 prefixEnd_3715642 := by exact prefixLift 3715642
  have htrace : WordTrace (prefixWord ++ tailWord_3715642) baseStart_3715642 baseEnd_3715642 := by
    simpa [prefixWord, tailWord_3715642, baseEnd_3715642] using wordTrace_append hprefix tailTrace_3715642
  have hstable : (prefixWord ++ tailWord_3715642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715642).length < 2 ^ (prefixWord ++ tailWord_3715642).sum := by decide
  have hdescent : baseEnd_3715642 < baseStart_3715642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715693 : List Nat := [1, 5, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_3715693 : Nat := 118140960795 + 3715693 * 2 ^ 59
def prefixEnd_3715693 : Nat := 4983230072969 + 3 ^ 40 * 3715693 * 2
def baseEnd_3715693 : Nat := 1271957649031090711832897

theorem tailTrace_3715693 : CollatzResearch.WordTrace tailWord_3715693 prefixEnd_3715693 1271957649031090711832897 := by
  unfold tailWord_3715693
  simp only [CollatzResearch.WordTrace]
  refine ⟨135522457327686325687231733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90348304885124217124821155 135522457327686325687231733)
  ·
    refine ⟨12705230374470593033177975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135522457327686325687231733 12705230374470593033177975)
    ·
      refine ⟨19057845561705889549766963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12705230374470593033177975 19057845561705889549766963)
      ·
        refine ⟨28586768342558834324650445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19057845561705889549766963 28586768342558834324650445)
        ·
          refine ⟨10720038128459562871743917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28586768342558834324650445 10720038128459562871743917)
          ·
            refine ⟨4020014298172336076903969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10720038128459562871743917 4020014298172336076903969)
            ·
              refine ⟨3015010723629252057677977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4020014298172336076903969 3015010723629252057677977)
              ·
                refine ⟨2261258042721939043258483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3015010723629252057677977 2261258042721939043258483)
                ·
                  refine ⟨3391887064082908564887725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2261258042721939043258483 3391887064082908564887725)
                  ·
                    refine ⟨1271957649031090711832897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3391887064082908564887725 1271957649031090711832897)
                    ·
                      rfl

theorem cell22_3715693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_3715693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715693 prefixEnd_3715693 := by exact prefixLift 3715693
  have htrace : WordTrace (prefixWord ++ tailWord_3715693) baseStart_3715693 baseEnd_3715693 := by
    simpa [prefixWord, tailWord_3715693, baseEnd_3715693] using wordTrace_append hprefix tailTrace_3715693
  have hstable : (prefixWord ++ tailWord_3715693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715693).length < 2 ^ (prefixWord ++ tailWord_3715693).sum := by decide
  have hdescent : baseEnd_3715693 < baseStart_3715693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715715 : List Nat := [1, 1, 1, 3, 3, 1, 3, 3, 1, 5]
def baseStart_3715715 : Nat := 118140960795 + 3715715 * 2 ^ 59
def prefixEnd_3715715 : Nat := 4983230072969 + 3 ^ 40 * 3715715 * 2
def baseEnd_3715715 : Nat := 1271965180080689987782829

theorem tailTrace_3715715 : CollatzResearch.WordTrace tailWord_3715715 prefixEnd_3715715 1271965180080689987782829 := by
  unfold tailWord_3715715
  simp only [CollatzResearch.WordTrace]
  refine ⟨135523259733606623444532599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90348839822404415629688399 135523259733606623444532599)
  ·
    refine ⟨203284889600409935166798899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135523259733606623444532599 203284889600409935166798899)
    ·
      refine ⟨304927334400614902750198349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203284889600409935166798899 304927334400614902750198349)
      ·
        refine ⟨114347750400230588531324381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304927334400614902750198349 114347750400230588531324381)
        ·
          refine ⟨42880406400086470699246643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114347750400230588531324381 42880406400086470699246643)
          ·
            refine ⟨64320609600129706048869965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42880406400086470699246643 64320609600129706048869965)
            ·
              refine ⟨24120228600048639768326237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64320609600129706048869965 24120228600048639768326237)
              ·
                refine ⟨9045085725018239913122339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24120228600048639768326237 9045085725018239913122339)
                ·
                  refine ⟨13567628587527359869683509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9045085725018239913122339 13567628587527359869683509)
                  ·
                    refine ⟨1271965180080689987782829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13567628587527359869683509 1271965180080689987782829)
                    ·
                      rfl

theorem cell22_3715715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 5].length) (baseStart_3715715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715715 prefixEnd_3715715 := by exact prefixLift 3715715
  have htrace : WordTrace (prefixWord ++ tailWord_3715715) baseStart_3715715 baseEnd_3715715 := by
    simpa [prefixWord, tailWord_3715715, baseEnd_3715715] using wordTrace_append hprefix tailTrace_3715715
  have hstable : (prefixWord ++ tailWord_3715715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715715).length < 2 ^ (prefixWord ++ tailWord_3715715).sum := by decide
  have hdescent : baseEnd_3715715 < baseStart_3715715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715811 : List Nat := [1, 1, 1, 7, 1, 3, 1, 1, 3, 3]
def baseStart_3715811 : Nat := 118140960795 + 3715811 * 2 ^ 59
def prefixEnd_3715811 : Nat := 4983230072969 + 3 ^ 40 * 3715811 * 2
def baseEnd_3715811 : Nat := 1271998042842577737382535

theorem tailTrace_3715811 : CollatzResearch.WordTrace tailWord_3715811 prefixEnd_3715811 1271998042842577737382535 := by
  unfold tailWord_3715811
  simp only [CollatzResearch.WordTrace]
  refine ⟨135526761141258831840027287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90351174094172554560018191 135526761141258831840027287)
  ·
    refine ⟨203290141711888247760040931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135526761141258831840027287 203290141711888247760040931)
    ·
      refine ⟨304935212567832371640061397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203290141711888247760040931 304935212567832371640061397)
      ·
        refine ⟨7146919044558571210313939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 304935212567832371640061397 7146919044558571210313939)
        ·
          refine ⟨10720378566837856815470909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7146919044558571210313939 10720378566837856815470909)
          ·
            refine ⟨4020141962564196305801591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10720378566837856815470909 4020141962564196305801591)
            ·
              refine ⟨6030212943846294458702387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4020141962564196305801591 6030212943846294458702387)
              ·
                refine ⟨9045319415769441688053581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6030212943846294458702387 9045319415769441688053581)
                ·
                  refine ⟨3391994780913540633020093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9045319415769441688053581 3391994780913540633020093)
                  ·
                    refine ⟨1271998042842577737382535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3391994780913540633020093 1271998042842577737382535)
                    ·
                      rfl

theorem cell22_3715811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 3].length) (baseStart_3715811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715811 prefixEnd_3715811 := by exact prefixLift 3715811
  have htrace : WordTrace (prefixWord ++ tailWord_3715811) baseStart_3715811 baseEnd_3715811 := by
    simpa [prefixWord, tailWord_3715811, baseEnd_3715811] using wordTrace_append hprefix tailTrace_3715811
  have hstable : (prefixWord ++ tailWord_3715811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715811).length < 2 ^ (prefixWord ++ tailWord_3715811).sum := by decide
  have hdescent : baseEnd_3715811 < baseStart_3715811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715820 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 2, 8]
def baseStart_3715820 : Nat := 118140960795 + 3715820 * 2 ^ 59
def prefixEnd_3715820 : Nat := 4983230072969 + 3 ^ 40 * 3715820 * 2
def baseEnd_3715820 : Nat := 1272001123726504713907507

theorem tailTrace_3715820 : CollatzResearch.WordTrace tailWord_3715820 prefixEnd_3715820 1272001123726504713907507 := by
  unfold tailWord_3715820
  simp only [CollatzResearch.WordTrace]
  refine ⟨67763544699113113188552457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90351392932150817584736609 67763544699113113188552457)
  ·
    refine ⟨50822658524334834891414343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67763544699113113188552457 50822658524334834891414343)
    ·
      refine ⟨76233987786502252337121515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50822658524334834891414343 76233987786502252337121515)
      ·
        refine ⟨114350981679753378505682273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76233987786502252337121515 114350981679753378505682273)
        ·
          refine ⟨85763236259815033879261705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114350981679753378505682273 85763236259815033879261705)
          ·
            refine ⟨64322427194861275409446279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85763236259815033879261705 64322427194861275409446279)
            ·
              refine ⟨96483640792291913114169419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64322427194861275409446279 96483640792291913114169419)
              ·
                refine ⟨144725461188437869671254129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96483640792291913114169419 144725461188437869671254129)
                ·
                  refine ⟨108544095891328402253440597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144725461188437869671254129 108544095891328402253440597)
                  ·
                    refine ⟨1272001123726504713907507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108544095891328402253440597 1272001123726504713907507)
                    ·
                      rfl

theorem cell22_3715820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_3715820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715820 prefixEnd_3715820 := by exact prefixLift 3715820
  have htrace : WordTrace (prefixWord ++ tailWord_3715820) baseStart_3715820 baseEnd_3715820 := by
    simpa [prefixWord, tailWord_3715820, baseEnd_3715820] using wordTrace_append hprefix tailTrace_3715820
  have hstable : (prefixWord ++ tailWord_3715820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715820).length < 2 ^ (prefixWord ++ tailWord_3715820).sum := by decide
  have hdescent : baseEnd_3715820 < baseStart_3715820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715837 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_3715837 : Nat := 118140960795 + 3715837 * 2 ^ 59
def prefixEnd_3715837 : Nat := 4983230072969 + 3 ^ 40 * 3715837 * 2
def baseEnd_3715837 : Nat := 1272006943173922336232455

theorem tailTrace_3715837 : CollatzResearch.WordTrace tailWord_3715837 prefixEnd_3715837 1272006943173922336232455 := by
  unfold tailWord_3715837
  simp only [CollatzResearch.WordTrace]
  refine ⟨135527709439164638280473765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90351806292776425520315843 135527709439164638280473765)
  ·
    refine ⟨25411445519843369677588831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135527709439164638280473765 25411445519843369677588831)
    ·
      refine ⟨38117168279765054516383247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25411445519843369677588831 38117168279765054516383247)
      ·
        refine ⟨57175752419647581774574871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38117168279765054516383247 57175752419647581774574871)
        ·
          refine ⟨85763628629471372661862307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57175752419647581774574871 85763628629471372661862307)
          ·
            refine ⟨128645442944207058992793461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85763628629471372661862307 128645442944207058992793461)
            ·
              refine ⟨12060510276019411780574387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128645442944207058992793461 12060510276019411780574387)
              ·
                refine ⟨18090765414029117670861581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12060510276019411780574387 18090765414029117670861581)
                ·
                  refine ⟨6784037030260919126573093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18090765414029117670861581 6784037030260919126573093)
                  ·
                    refine ⟨1272006943173922336232455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6784037030260919126573093 1272006943173922336232455)
                    ·
                      rfl

theorem cell22_3715837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_3715837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715837 prefixEnd_3715837 := by exact prefixLift 3715837
  have htrace : WordTrace (prefixWord ++ tailWord_3715837) baseStart_3715837 baseEnd_3715837 := by
    simpa [prefixWord, tailWord_3715837, baseEnd_3715837] using wordTrace_append hprefix tailTrace_3715837
  have hstable : (prefixWord ++ tailWord_3715837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715837).length < 2 ^ (prefixWord ++ tailWord_3715837).sum := by decide
  have hdescent : baseEnd_3715837 < baseStart_3715837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715884 : List Nat := [2, 2, 1, 1, 1, 4, 1, 5, 2, 3]
def baseStart_3715884 : Nat := 118140960795 + 3715884 * 2 ^ 59
def prefixEnd_3715884 : Nat := 4983230072969 + 3 ^ 40 * 3715884 * 2
def baseEnd_3715884 : Nat := 1272023032234429880307311

theorem tailTrace_3715884 : CollatzResearch.WordTrace tailWord_3715884 prefixEnd_3715884 1272023032234429880307311 := by
  unfold tailWord_3715884
  simp only [CollatzResearch.WordTrace]
  refine ⟨67764711834997182653717353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90352949113329576871623137 67764711834997182653717353)
  ·
    refine ⟨50823533876247886990288015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67764711834997182653717353 50823533876247886990288015)
    ·
      refine ⟨76235300814371830485432023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50823533876247886990288015 76235300814371830485432023)
      ·
        refine ⟨114352951221557745728148035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76235300814371830485432023 114352951221557745728148035)
        ·
          refine ⟨171529426832336618592222053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114352951221557745728148035 171529426832336618592222053)
          ·
            refine ⟨32161767531063115986041635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171529426832336618592222053 32161767531063115986041635)
            ·
              refine ⟨48242651296594673979062453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32161767531063115986041635 48242651296594673979062453)
              ·
                refine ⟨4522748559055750685537105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48242651296594673979062453 4522748559055750685537105)
                ·
                  refine ⟨3392061419291813014152829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4522748559055750685537105 3392061419291813014152829)
                  ·
                    refine ⟨1272023032234429880307311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3392061419291813014152829 1272023032234429880307311)
                    ·
                      rfl

theorem cell22_3715884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_3715884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715884 prefixEnd_3715884 := by exact prefixLift 3715884
  have htrace : WordTrace (prefixWord ++ tailWord_3715884) baseStart_3715884 baseEnd_3715884 := by
    simpa [prefixWord, tailWord_3715884, baseEnd_3715884] using wordTrace_append hprefix tailTrace_3715884
  have hstable : (prefixWord ++ tailWord_3715884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715884).length < 2 ^ (prefixWord ++ tailWord_3715884).sum := by decide
  have hdescent : baseEnd_3715884 < baseStart_3715884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715905 : List Nat := [1, 2, 5, 3, 1, 2, 2, 1, 1, 4]
def baseStart_3715905 : Nat := 118140960795 + 3715905 * 2 ^ 59
def prefixEnd_3715905 : Nat := 4983230072969 + 3 ^ 40 * 3715905 * 2
def baseEnd_3715905 : Nat := 1272030220963592825532247

theorem tailTrace_3715905 : CollatzResearch.WordTrace tailWord_3715905 prefixEnd_3715905 1272030220963592825532247 := by
  unfold tailWord_3715905
  simp only [CollatzResearch.WordTrace]
  refine ⟨135530189602918285893949169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90353459735278857262632779 135530189602918285893949169)
  ·
    refine ⟨101647642202188714420461877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135530189602918285893949169 101647642202188714420461877)
    ·
      refine ⟨9529466456455191976918301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101647642202188714420461877 9529466456455191976918301)
      ·
        refine ⟨3573549921170696991344363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9529466456455191976918301 3573549921170696991344363)
        ·
          refine ⟨5360324881756045487016545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3573549921170696991344363 5360324881756045487016545)
          ·
            refine ⟨4020243661317034115262409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5360324881756045487016545 4020243661317034115262409)
            ·
              refine ⟨3015182745987775586446807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4020243661317034115262409 3015182745987775586446807)
              ·
                refine ⟨4522774118981663379670211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3015182745987775586446807 4522774118981663379670211)
                ·
                  refine ⟨6784161178472495069505317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4522774118981663379670211 6784161178472495069505317)
                  ·
                    refine ⟨1272030220963592825532247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6784161178472495069505317 1272030220963592825532247)
                    ·
                      rfl

theorem cell22_3715905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_3715905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715905 prefixEnd_3715905 := by exact prefixLift 3715905
  have htrace : WordTrace (prefixWord ++ tailWord_3715905) baseStart_3715905 baseEnd_3715905 := by
    simpa [prefixWord, tailWord_3715905, baseEnd_3715905] using wordTrace_append hprefix tailTrace_3715905
  have hstable : (prefixWord ++ tailWord_3715905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715905).length < 2 ^ (prefixWord ++ tailWord_3715905).sum := by decide
  have hdescent : baseEnd_3715905 < baseStart_3715905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715929 : List Nat := [1, 2, 1, 2, 2, 4, 1, 3, 3, 3]
def baseStart_3715929 : Nat := 118140960795 + 3715929 * 2 ^ 59
def prefixEnd_3715929 : Nat := 4983230072969 + 3 ^ 40 * 3715929 * 2
def baseEnd_3715929 : Nat := 1272038436654064762932173

theorem tailTrace_3715929 : CollatzResearch.WordTrace tailWord_3715929 prefixEnd_3715929 1272038436654064762932173 := by
  unfold tailWord_3715929
  simp only [CollatzResearch.WordTrace]
  refine ⟨135531064954831337992822841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90354043303220891995215227 135531064954831337992822841)
  ·
    refine ⟨101648298716123503494617131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135531064954831337992822841 101648298716123503494617131)
    ·
      refine ⟨152472448074185255241925697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101648298716123503494617131 152472448074185255241925697)
      ·
        refine ⟨114354336055638941431444273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152472448074185255241925697 114354336055638941431444273)
        ·
          refine ⟨85765752041729206073583205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114354336055638941431444273 85765752041729206073583205)
          ·
            refine ⟨16081078507824226138796851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85765752041729206073583205 16081078507824226138796851)
            ·
              refine ⟨24121617761736339208195277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16081078507824226138796851 24121617761736339208195277)
              ·
                refine ⟨9045606660651127203073229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24121617761736339208195277 9045606660651127203073229)
                ·
                  refine ⟨3392102497744172701152461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9045606660651127203073229 3392102497744172701152461)
                  ·
                    refine ⟨1272038436654064762932173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3392102497744172701152461 1272038436654064762932173)
                    ·
                      rfl

theorem cell22_3715929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 3].length) (baseStart_3715929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715929 prefixEnd_3715929 := by exact prefixLift 3715929
  have htrace : WordTrace (prefixWord ++ tailWord_3715929) baseStart_3715929 baseEnd_3715929 := by
    simpa [prefixWord, tailWord_3715929, baseEnd_3715929] using wordTrace_append hprefix tailTrace_3715929
  have hstable : (prefixWord ++ tailWord_3715929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715929).length < 2 ^ (prefixWord ++ tailWord_3715929).sum := by decide
  have hdescent : baseEnd_3715929 < baseStart_3715929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715987 : List Nat := [1, 1, 1, 2, 1, 2, 1, 7, 6]
def baseStart_3715987 : Nat := 118140960795 + 3715987 * 2 ^ 59
def prefixEnd_3715987 : Nat := 4983230072969 + 3 ^ 40 * 3715987 * 2
def baseEnd_3715987 : Nat := 424019430413123981660665

theorem tailTrace_3715987 : CollatzResearch.WordTrace tailWord_3715987 prefixEnd_3715987 424019430413123981660665 := by
  unfold tailWord_3715987
  simp only [CollatzResearch.WordTrace]
  refine ⟨135533180388621213898434215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90355453592414142598956143 135533180388621213898434215)
  ·
    refine ⟨203299770582931820847651323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135533180388621213898434215 203299770582931820847651323)
    ·
      refine ⟨304949655874397731271476985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203299770582931820847651323 304949655874397731271476985)
      ·
        refine ⟨228712241905798298453607739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304949655874397731271476985 228712241905798298453607739)
        ·
          refine ⟨343068362858697447680411609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228712241905798298453607739 343068362858697447680411609)
          ·
            refine ⟨257301272144023085760308707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343068362858697447680411609 257301272144023085760308707)
            ·
              refine ⟨385951908216034628640463061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257301272144023085760308707 385951908216034628640463061)
              ·
                refine ⟨9045747848813311608760853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 385951908216034628640463061 9045747848813311608760853)
                ·
                  refine ⟨424019430413123981660665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9045747848813311608760853 424019430413123981660665)
                  ·
                    rfl

theorem cell22_3715987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 6].length) (baseStart_3715987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3715987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3715987 prefixEnd_3715987 := by exact prefixLift 3715987
  have htrace : WordTrace (prefixWord ++ tailWord_3715987) baseStart_3715987 baseEnd_3715987 := by
    simpa [prefixWord, tailWord_3715987, baseEnd_3715987] using wordTrace_append hprefix tailTrace_3715987
  have hstable : (prefixWord ++ tailWord_3715987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715987).length < 2 ^ (prefixWord ++ tailWord_3715987).sum := by decide
  have hdescent : baseEnd_3715987 < baseStart_3715987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716019 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 4, 3]
def baseStart_3716019 : Nat := 118140960795 + 3716019 * 2 ^ 59
def prefixEnd_3716019 : Nat := 4983230072969 + 3 ^ 40 * 3716019 * 2
def baseEnd_3716019 : Nat := 1272069245493334528181897

theorem tailTrace_3716019 : CollatzResearch.WordTrace tailWord_3716019 prefixEnd_3716019 1272069245493334528181897 := by
  unfold tailWord_3716019
  simp only [CollatzResearch.WordTrace]
  refine ⟨135534347524505283363599111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90356231683003522242399407 135534347524505283363599111)
  ·
    refine ⟨203301521286757925045398667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135534347524505283363599111 203301521286757925045398667)
    ·
      refine ⟨304952281930136887568098001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203301521286757925045398667 304952281930136887568098001)
      ·
        refine ⟨228714211447602665676073501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304952281930136887568098001 228714211447602665676073501)
        ·
          refine ⟨85767829292850999628527563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228714211447602665676073501 85767829292850999628527563)
          ·
            refine ⟨128651743939276499442791345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85767829292850999628527563 128651743939276499442791345)
            ·
              refine ⟨96488807954457374582093509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128651743939276499442791345 96488807954457374582093509)
              ·
                refine ⟨18091651491460757734142533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96488807954457374582093509 18091651491460757734142533)
                ·
                  refine ⟨3392184654648892075151725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18091651491460757734142533 3392184654648892075151725)
                  ·
                    refine ⟨1272069245493334528181897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3392184654648892075151725 1272069245493334528181897)
                    ·
                      rfl

theorem cell22_3716019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 3].length) (baseStart_3716019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716019 prefixEnd_3716019 := by exact prefixLift 3716019
  have htrace : WordTrace (prefixWord ++ tailWord_3716019) baseStart_3716019 baseEnd_3716019 := by
    simpa [prefixWord, tailWord_3716019, baseEnd_3716019] using wordTrace_append hprefix tailTrace_3716019
  have hstable : (prefixWord ++ tailWord_3716019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716019).length < 2 ^ (prefixWord ++ tailWord_3716019).sum := by decide
  have hdescent : baseEnd_3716019 < baseStart_3716019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716021 : List Nat := [1, 3, 3, 2, 1, 1, 2, 5, 4]
def baseStart_3716021 : Nat := 118140960795 + 3716021 * 2 ^ 59
def prefixEnd_3716021 : Nat := 4983230072969 + 3 ^ 40 * 3716021 * 2
def baseEnd_3716021 : Nat := 424023310044735729877297

theorem tailTrace_3716021 : CollatzResearch.WordTrace tailWord_3716021 prefixEnd_3716021 424023310044735729877297 := by
  unfold tailWord_3716021
  simp only [CollatzResearch.WordTrace]
  refine ⟨135534420470498037705171917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90356280313665358470114611 135534420470498037705171917)
  ·
    refine ⟨50825407676436764139439469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135534420470498037705171917 50825407676436764139439469)
    ·
      refine ⟨19059527878663786552289801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50825407676436764139439469 19059527878663786552289801)
      ·
        refine ⟨14294645908997839914217351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19059527878663786552289801 14294645908997839914217351)
        ·
          refine ⟨21441968863496759871326027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14294645908997839914217351 21441968863496759871326027)
          ·
            refine ⟨32162953295245139806989041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21441968863496759871326027 32162953295245139806989041)
            ·
              refine ⟨24122214971433854855241781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32162953295245139806989041 24122214971433854855241781)
              ·
                refine ⟨2261457653571923892678917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24122214971433854855241781 2261457653571923892678917)
                ·
                  refine ⟨424023310044735729877297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2261457653571923892678917 424023310044735729877297)
                  ·
                    rfl

theorem cell22_3716021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_3716021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716021 prefixEnd_3716021 := by exact prefixLift 3716021
  have htrace : WordTrace (prefixWord ++ tailWord_3716021) baseStart_3716021 baseEnd_3716021 := by
    simpa [prefixWord, tailWord_3716021, baseEnd_3716021] using wordTrace_append hprefix tailTrace_3716021
  have hstable : (prefixWord ++ tailWord_3716021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716021).length < 2 ^ (prefixWord ++ tailWord_3716021).sum := by decide
  have hdescent : baseEnd_3716021 < baseStart_3716021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716032 : List Nat := [2, 1, 1, 2, 3, 13]
def baseStart_3716032 : Nat := 118140960795 + 3716032 * 2 ^ 59
def prefixEnd_3716032 : Nat := 4983230072969 + 3 ^ 40 * 3716032 * 2
def baseEnd_3716032 : Nat := 15704613526654405279097

theorem tailTrace_3716032 : CollatzResearch.WordTrace tailWord_3716032 prefixEnd_3716032 15704613526654405279097 := by
  unfold tailWord_3716032
  simp only [CollatzResearch.WordTrace]
  refine ⟨67767410836729093291911175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90356547782305457722548233 67767410836729093291911175)
  ·
    refine ⟨101651116255093639937866763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67767410836729093291911175 101651116255093639937866763)
    ·
      refine ⟨152476674382640459906800145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101651116255093639937866763 152476674382640459906800145)
      ·
        refine ⟨114357505786980344930100109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152476674382640459906800145 114357505786980344930100109)
        ·
          refine ⟨42884064670117629348787541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114357505786980344930100109 42884064670117629348787541)
          ·
            refine ⟨15704613526654405279097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 42884064670117629348787541 15704613526654405279097)
            ·
              rfl

theorem cell22_3716032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 13].length) (baseStart_3716032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716032 prefixEnd_3716032 := by exact prefixLift 3716032
  have htrace : WordTrace (prefixWord ++ tailWord_3716032) baseStart_3716032 baseEnd_3716032 := by
    simpa [prefixWord, tailWord_3716032, baseEnd_3716032] using wordTrace_append hprefix tailTrace_3716032
  have hstable : (prefixWord ++ tailWord_3716032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716032).length < 2 ^ (prefixWord ++ tailWord_3716032).sum := by decide
  have hdescent : baseEnd_3716032 < baseStart_3716032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716132 : List Nat := [2, 3, 1, 4, 1, 3, 1, 3, 1, 3]
def baseStart_3716132 : Nat := 118140960795 + 3716132 * 2 ^ 59
def prefixEnd_3716132 : Nat := 4983230072969 + 3 ^ 40 * 3716132 * 2
def baseEnd_3716132 : Nat := 1272107927702639900106551

theorem tailTrace_3716132 : CollatzResearch.WordTrace tailWord_3716132 prefixEnd_3716132 1272107927702639900106551 := by
  unfold tailWord_3716132
  simp only [CollatzResearch.WordTrace]
  refine ⟨67769234486547951831231325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90358979315397269108308433 67769234486547951831231325)
  ·
    refine ⟨25413462932455481936711747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67769234486547951831231325 25413462932455481936711747)
    ·
      refine ⟨38120194398683222905067621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25413462932455481936711747 38120194398683222905067621)
      ·
        refine ⟨7147536449753104294700179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38120194398683222905067621 7147536449753104294700179)
        ·
          refine ⟨10721304674629656442050269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7147536449753104294700179 10721304674629656442050269)
          ·
            refine ⟨4020489252986121165768851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10721304674629656442050269 4020489252986121165768851)
            ·
              refine ⟨6030733879479181748653277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4020489252986121165768851 6030733879479181748653277)
              ·
                refine ⟨2261525204804693155744979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6030733879479181748653277 2261525204804693155744979)
                ·
                  refine ⟨3392287807207039733617469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2261525204804693155744979 3392287807207039733617469)
                  ·
                    refine ⟨1272107927702639900106551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3392287807207039733617469 1272107927702639900106551)
                    ·
                      rfl

theorem cell22_3716132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_3716132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716132 prefixEnd_3716132 := by exact prefixLift 3716132
  have htrace : WordTrace (prefixWord ++ tailWord_3716132) baseStart_3716132 baseEnd_3716132 := by
    simpa [prefixWord, tailWord_3716132, baseEnd_3716132] using wordTrace_append hprefix tailTrace_3716132
  have hstable : (prefixWord ++ tailWord_3716132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716132).length < 2 ^ (prefixWord ++ tailWord_3716132).sum := by decide
  have hdescent : baseEnd_3716132 < baseStart_3716132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716156 : List Nat := [2, 2, 2, 2, 2, 2, 3, 1, 6]
def baseStart_3716156 : Nat := 118140960795 + 3716156 * 2 ^ 59
def prefixEnd_3716156 : Nat := 4983230072969 + 3 ^ 40 * 3716156 * 2
def baseEnd_3716156 : Nat := 424038714464370612502159

theorem tailTrace_3716156 : CollatzResearch.WordTrace tailWord_3716156 prefixEnd_3716156 424038714464370612502159 := by
  unfold tailWord_3716156
  simp only [CollatzResearch.WordTrace]
  refine ⟨67769672162504477880668161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90359562883339303840890881 67769672162504477880668161)
  ·
    refine ⟨50827254121878358410501121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67769672162504477880668161 50827254121878358410501121)
    ·
      refine ⟨38120440591408768807875841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50827254121878358410501121 38120440591408768807875841)
      ·
        refine ⟨28590330443556576605906881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38120440591408768807875841 28590330443556576605906881)
        ·
          refine ⟨21442747832667432454430161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28590330443556576605906881 21442747832667432454430161)
          ·
            refine ⟨16082060874500574340822621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21442747832667432454430161 16082060874500574340822621)
            ·
              refine ⟨6030772827937715377808483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16082060874500574340822621 6030772827937715377808483)
              ·
                refine ⟨9046159241906573066712725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6030772827937715377808483 9046159241906573066712725)
                ·
                  refine ⟨424038714464370612502159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9046159241906573066712725 424038714464370612502159)
                  ·
                    rfl

theorem cell22_3716156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_3716156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716156 prefixEnd_3716156 := by exact prefixLift 3716156
  have htrace : WordTrace (prefixWord ++ tailWord_3716156) baseStart_3716156 baseEnd_3716156 := by
    simpa [prefixWord, tailWord_3716156, baseEnd_3716156] using wordTrace_append hprefix tailTrace_3716156
  have hstable : (prefixWord ++ tailWord_3716156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716156).length < 2 ^ (prefixWord ++ tailWord_3716156).sum := by decide
  have hdescent : baseEnd_3716156 < baseStart_3716156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716169 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 1, 6]
def baseStart_3716169 : Nat := 118140960795 + 3716169 * 2 ^ 59
def prefixEnd_3716169 : Nat := 4983230072969 + 3 ^ 40 * 3716169 * 2
def baseEnd_3716169 : Nat := 1272120593558784136931437

theorem tailTrace_3716169 : CollatzResearch.WordTrace tailWord_3716169 prefixEnd_3716169 1272120593558784136931437 := by
  unfold tailWord_3716169
  simp only [CollatzResearch.WordTrace]
  refine ⟨135539818473961858981559561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90359878982641239321039707 135539818473961858981559561)
  ·
    refine ⟨101654863855471394236169671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135539818473961858981559561 101654863855471394236169671)
    ·
      refine ⟨152482295783207091354254507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101654863855471394236169671 152482295783207091354254507)
      ·
        refine ⟨228723443674810637031381761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152482295783207091354254507 228723443674810637031381761)
        ·
          refine ⟨171542582756107977773536321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228723443674810637031381761 171542582756107977773536321)
          ·
            refine ⟨128656937067080983330152241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171542582756107977773536321 128656937067080983330152241)
            ·
              refine ⟨96492702800310737497614181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128656937067080983330152241 96492702800310737497614181)
              ·
                refine ⟨18092381775058263280802659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96492702800310737497614181 18092381775058263280802659)
                ·
                  refine ⟨27138572662587394921203989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18092381775058263280802659 27138572662587394921203989)
                  ·
                    refine ⟨1272120593558784136931437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27138572662587394921203989 1272120593558784136931437)
                    ·
                      rfl

theorem cell22_3716169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_3716169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716169 prefixEnd_3716169 := by exact prefixLift 3716169
  have htrace : WordTrace (prefixWord ++ tailWord_3716169) baseStart_3716169 baseEnd_3716169 := by
    simpa [prefixWord, tailWord_3716169, baseEnd_3716169] using wordTrace_append hprefix tailTrace_3716169
  have hstable : (prefixWord ++ tailWord_3716169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716169).length < 2 ^ (prefixWord ++ tailWord_3716169).sum := by decide
  have hdescent : baseEnd_3716169 < baseStart_3716169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716184 : List Nat := [2, 1, 2, 2, 1, 3, 1, 10]
def baseStart_3716184 : Nat := 118140960795 + 3716184 * 2 ^ 59
def prefixEnd_3716184 : Nat := 4983230072969 + 3 ^ 40 * 3716184 * 2
def baseEnd_3716184 : Nat := 141347303151703233089599

theorem tailTrace_3716184 : CollatzResearch.WordTrace tailWord_3716184 prefixEnd_3716184 141347303151703233089599 := by
  unfold tailWord_3716184
  simp only [CollatzResearch.WordTrace]
  refine ⟨67770182784453758271677803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90360243712605011028903737 67770182784453758271677803)
  ·
    refine ⟨101655274176680637407516705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67770182784453758271677803 101655274176680637407516705)
    ·
      refine ⟨76241455632510478055637529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101655274176680637407516705 76241455632510478055637529)
      ·
        refine ⟨57181091724382858541728147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76241455632510478055637529 57181091724382858541728147)
        ·
          refine ⟨85771637586574287812592221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57181091724382858541728147 85771637586574287812592221)
          ·
            refine ⟨32164364094965357929722083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85771637586574287812592221 32164364094965357929722083)
            ·
              refine ⟨48246546142448036894583125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32164364094965357929722083 48246546142448036894583125)
              ·
                refine ⟨141347303151703233089599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48246546142448036894583125 141347303151703233089599)
                ·
                  rfl

theorem cell22_3716184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 10].length) (baseStart_3716184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716184 prefixEnd_3716184 := by exact prefixLift 3716184
  have htrace : WordTrace (prefixWord ++ tailWord_3716184) baseStart_3716184 baseEnd_3716184 := by
    simpa [prefixWord, tailWord_3716184, baseEnd_3716184] using wordTrace_append hprefix tailTrace_3716184
  have hstable : (prefixWord ++ tailWord_3716184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716184).length < 2 ^ (prefixWord ++ tailWord_3716184).sum := by decide
  have hdescent : baseEnd_3716184 < baseStart_3716184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716205 : List Nat := [1, 5, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_3716205 : Nat := 118140960795 + 3716205 * 2 ^ 59
def prefixEnd_3716205 : Nat := 4983230072969 + 3 ^ 40 * 3716205 * 2
def baseEnd_3716205 : Nat := 1272132917094492043031327

theorem tailTrace_3716205 : CollatzResearch.WordTrace tailWord_3716205 prefixEnd_3716205 1272132917094492043031327 := by
  unfold tailWord_3716205
  simp only [CollatzResearch.WordTrace]
  refine ⟨135541131501831437129870069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90360754334554291419913379 135541131501831437129870069)
  ·
    refine ⟨12706981078296697230925319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135541131501831437129870069 12706981078296697230925319)
    ·
      refine ⟨19060471617445045846387979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12706981078296697230925319 19060471617445045846387979)
      ·
        refine ⟨28590707426167568769581969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19060471617445045846387979 28590707426167568769581969)
        ·
          refine ⟨21443030569625676577186477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28590707426167568769581969 21443030569625676577186477)
          ·
            refine ⟨8041136463609628716444929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21443030569625676577186477 8041136463609628716444929)
            ·
              refine ⟨6030852347707221537333697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8041136463609628716444929 6030852347707221537333697)
              ·
                refine ⟨4523139260780416153000273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6030852347707221537333697 4523139260780416153000273)
                ·
                  refine ⟨3392354445585312114750205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4523139260780416153000273 3392354445585312114750205)
                  ·
                    refine ⟨1272132917094492043031327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3392354445585312114750205 1272132917094492043031327)
                    ·
                      rfl

theorem cell22_3716205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_3716205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716205 prefixEnd_3716205 := by exact prefixLift 3716205
  have htrace : WordTrace (prefixWord ++ tailWord_3716205) baseStart_3716205 baseEnd_3716205 := by
    simpa [prefixWord, tailWord_3716205, baseEnd_3716205] using wordTrace_append hprefix tailTrace_3716205
  have hstable : (prefixWord ++ tailWord_3716205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716205).length < 2 ^ (prefixWord ++ tailWord_3716205).sum := by decide
  have hdescent : baseEnd_3716205 < baseStart_3716205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716233 : List Nat := [1, 2, 1, 1, 4, 4, 1, 2, 3, 3]
def baseStart_3716233 : Nat := 118140960795 + 3716233 * 2 ^ 59
def prefixEnd_3716233 : Nat := 4983230072969 + 3 ^ 40 * 3716233 * 2
def baseEnd_3716233 : Nat := 1272142502066709303331241

theorem tailTrace_3716233 : CollatzResearch.WordTrace tailWord_3716233 prefixEnd_3716233 1272142502066709303331241 := by
  unfold tailWord_3716233
  simp only [CollatzResearch.WordTrace]
  refine ⟨135542152745729997911889353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90361435163819998607926235 135542152745729997911889353)
  ·
    refine ⟨101656614559297498433917015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135542152745729997911889353 101656614559297498433917015)
    ·
      refine ⟨152484921838946247650875523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101656614559297498433917015 152484921838946247650875523)
      ·
        refine ⟨228727382758419371476313285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152484921838946247650875523 228727382758419371476313285)
        ·
          refine ⟨42886384267203632151808741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228727382758419371476313285 42886384267203632151808741)
          ·
            refine ⟨8041197050100681028464139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42886384267203632151808741 8041197050100681028464139)
            ·
              refine ⟨12061795575151021542696209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8041197050100681028464139 12061795575151021542696209)
              ·
                refine ⟨9046346681363266157022157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12061795575151021542696209 9046346681363266157022157)
                ·
                  refine ⟨3392380005511224808883309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9046346681363266157022157 3392380005511224808883309)
                  ·
                    refine ⟨1272142502066709303331241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3392380005511224808883309 1272142502066709303331241)
                    ·
                      rfl

theorem cell22_3716233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 3].length) (baseStart_3716233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716233 prefixEnd_3716233 := by exact prefixLift 3716233
  have htrace : WordTrace (prefixWord ++ tailWord_3716233) baseStart_3716233 baseEnd_3716233 := by
    simpa [prefixWord, tailWord_3716233, baseEnd_3716233] using wordTrace_append hprefix tailTrace_3716233
  have hstable : (prefixWord ++ tailWord_3716233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716233).length < 2 ^ (prefixWord ++ tailWord_3716233).sum := by decide
  have hdescent : baseEnd_3716233 < baseStart_3716233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716261 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 2, 5]
def baseStart_3716261 : Nat := 118140960795 + 3716261 * 2 ^ 59
def prefixEnd_3716261 : Nat := 4983230072969 + 3 ^ 40 * 3716261 * 2
def baseEnd_3716261 : Nat := 1272152087038926563631155

theorem tailTrace_3716261 : CollatzResearch.WordTrace tailWord_3716261 prefixEnd_3716261 1272152087038926563631155 := by
  unfold tailWord_3716261
  simp only [CollatzResearch.WordTrace]
  refine ⟨135543173989628558693908637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90362115993085705795939091 135543173989628558693908637)
  ·
    refine ⟨50828690246110709510215739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135543173989628558693908637 50828690246110709510215739)
    ·
      refine ⟨76243035369166064265323609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50828690246110709510215739 76243035369166064265323609)
      ·
        refine ⟨57182276526874548198992707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76243035369166064265323609 57182276526874548198992707)
        ·
          refine ⟨85773414790311822298489061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57182276526874548198992707 85773414790311822298489061)
          ·
            refine ⟨16082515273183466680966699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85773414790311822298489061 16082515273183466680966699)
            ·
              refine ⟨24123772909775200021450049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16082515273183466680966699 24123772909775200021450049)
              ·
                refine ⟨18092829682331400016087537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24123772909775200021450049 18092829682331400016087537)
                ·
                  refine ⟨13569622261748550012065653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18092829682331400016087537 13569622261748550012065653)
                  ·
                    refine ⟨1272152087038926563631155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13569622261748550012065653 1272152087038926563631155)
                    ·
                      rfl

theorem cell22_3716261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_3716261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716261 prefixEnd_3716261 := by exact prefixLift 3716261
  have htrace : WordTrace (prefixWord ++ tailWord_3716261) baseStart_3716261 baseEnd_3716261 := by
    simpa [prefixWord, tailWord_3716261, baseEnd_3716261] using wordTrace_append hprefix tailTrace_3716261
  have hstable : (prefixWord ++ tailWord_3716261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716261).length < 2 ^ (prefixWord ++ tailWord_3716261).sum := by decide
  have hdescent : baseEnd_3716261 < baseStart_3716261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716263 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 7]
def baseStart_3716263 : Nat := 118140960795 + 3716263 * 2 ^ 59
def prefixEnd_3716263 : Nat := 4983230072969 + 3 ^ 40 * 3716263 * 2
def baseEnd_3716263 : Nat := 424050923893266408360383

theorem tailTrace_3716263 : CollatzResearch.WordTrace tailWord_3716263 prefixEnd_3716263 424050923893266408360383 := by
  unfold tailWord_3716263
  simp only [CollatzResearch.WordTrace]
  refine ⟨135543246935621313035481443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90362164623747542023654295 135543246935621313035481443)
  ·
    refine ⟨203314870403431969553222165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135543246935621313035481443 203314870403431969553222165)
    ·
      refine ⟨9530384550160873572807289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 203314870403431969553222165 9530384550160873572807289)
      ·
        refine ⟨7147788412620655179605467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9530384550160873572807289 7147788412620655179605467)
        ·
          refine ⟨10721682618930982769408201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7147788412620655179605467 10721682618930982769408201)
          ·
            refine ⟨8041261964198237077056151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10721682618930982769408201 8041261964198237077056151)
            ·
              refine ⟨12061892946297355615584227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8041261964198237077056151 12061892946297355615584227)
              ·
                refine ⟨18092839419446033423376341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12061892946297355615584227 18092839419446033423376341)
                ·
                  refine ⟨424050923893266408360383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18092839419446033423376341 424050923893266408360383)
                  ·
                    rfl

theorem cell22_3716263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 7].length) (baseStart_3716263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716263 prefixEnd_3716263 := by exact prefixLift 3716263
  have htrace : WordTrace (prefixWord ++ tailWord_3716263) baseStart_3716263 baseEnd_3716263 := by
    simpa [prefixWord, tailWord_3716263, baseEnd_3716263] using wordTrace_append hprefix tailTrace_3716263
  have hstable : (prefixWord ++ tailWord_3716263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716263).length < 2 ^ (prefixWord ++ tailWord_3716263).sum := by decide
  have hdescent : baseEnd_3716263 < baseStart_3716263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716325 : List Nat := [1, 3, 1, 4, 3, 2, 1, 1, 6]
def baseStart_3716325 : Nat := 118140960795 + 3716325 * 2 ^ 59
def prefixEnd_3716325 : Nat := 4983230072969 + 3 ^ 40 * 3716325 * 2
def baseEnd_3716325 : Nat := 424057998515617243343653

theorem tailTrace_3716325 : CollatzResearch.WordTrace tailWord_3716325 prefixEnd_3716325 424057998515617243343653 := by
  unfold tailWord_3716325
  simp only [CollatzResearch.WordTrace]
  refine ⟨135545508261396697624238429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90363672174264465082825619 135545508261396697624238429)
  ·
    refine ⟨50829565598023761609089411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135545508261396697624238429 50829565598023761609089411)
    ·
      refine ⟨76244348397035642413634117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50829565598023761609089411 76244348397035642413634117)
      ·
        refine ⟨14295815324444182952556397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76244348397035642413634117 14295815324444182952556397)
        ·
          refine ⟨5360930746666568607208649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14295815324444182952556397 5360930746666568607208649)
          ·
            refine ⟨4020698059999926455406487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5360930746666568607208649 4020698059999926455406487)
            ·
              refine ⟨6031047089999889683109731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4020698059999926455406487 6031047089999889683109731)
              ·
                refine ⟨9046570634999834524664597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6031047089999889683109731 9046570634999834524664597)
                ·
                  refine ⟨424057998515617243343653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9046570634999834524664597 424057998515617243343653)
                  ·
                    rfl

theorem cell22_3716325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_3716325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716325 prefixEnd_3716325 := by exact prefixLift 3716325
  have htrace : WordTrace (prefixWord ++ tailWord_3716325) baseStart_3716325 baseEnd_3716325 := by
    simpa [prefixWord, tailWord_3716325, baseEnd_3716325] using wordTrace_append hprefix tailTrace_3716325
  have hstable : (prefixWord ++ tailWord_3716325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716325).length < 2 ^ (prefixWord ++ tailWord_3716325).sum := by decide
  have hdescent : baseEnd_3716325 < baseStart_3716325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716370 : List Nat := [3, 2, 4, 2, 1, 10]
def baseStart_3716370 : Nat := 118140960795 + 3716370 * 2 ^ 59
def prefixEnd_3716370 : Nat := 4983230072969 + 3 ^ 40 * 3716370 * 2
def baseEnd_3716370 : Nat := 15706041974894896452541

theorem tailTrace_3716370 : CollatzResearch.WordTrace tailWord_3716370 prefixEnd_3716370 15706041974894896452541 := by
  unfold tailWord_3716370
  simp only [CollatzResearch.WordTrace]
  refine ⟨33886787386558417577406641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90364766364155780206417709 33886787386558417577406641)
  ·
    refine ⟨25415090539918813183054981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33886787386558417577406641 25415090539918813183054981)
    ·
      refine ⟨4765329476234777471822809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25415090539918813183054981 4765329476234777471822809)
      ·
        refine ⟨3573997107176083103867107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4765329476234777471822809 3573997107176083103867107)
        ·
          refine ⟨5360995660764124655800661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3573997107176083103867107 5360995660764124655800661)
          ·
            refine ⟨15706041974894896452541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5360995660764124655800661 15706041974894896452541)
            ·
              rfl

theorem cell22_3716370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 10].length) (baseStart_3716370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716370 prefixEnd_3716370 := by exact prefixLift 3716370
  have htrace : WordTrace (prefixWord ++ tailWord_3716370) baseStart_3716370 baseEnd_3716370 := by
    simpa [prefixWord, tailWord_3716370, baseEnd_3716370] using wordTrace_append hprefix tailTrace_3716370
  have hstable : (prefixWord ++ tailWord_3716370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716370).length < 2 ^ (prefixWord ++ tailWord_3716370).sum := by decide
  have hdescent : baseEnd_3716370 < baseStart_3716370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716406 : List Nat := [5, 1, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_3716406 : Nat := 118140960795 + 3716406 * 2 ^ 59
def prefixEnd_3716406 : Nat := 4983230072969 + 3 ^ 40 * 3716406 * 2
def baseEnd_3716406 : Nat := 1272201723502194518755711

theorem tailTrace_3716406 : CollatzResearch.WordTrace tailWord_3716406 prefixEnd_3716406 1272201723502194518755711 := by
  unfold tailWord_3716406
  simp only [CollatzResearch.WordTrace]
  refine ⟨8471778910881453028621067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90365641716068832305291381 8471778910881453028621067)
  ·
    refine ⟨12707668366322179542931601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8471778910881453028621067 12707668366322179542931601)
    ·
      refine ⟨9530751274741634657198701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12707668366322179542931601 9530751274741634657198701)
      ·
        refine ⟨3574031728028112996449513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9530751274741634657198701 3574031728028112996449513)
        ·
          refine ⟨2680523796021084747337135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3574031728028112996449513 2680523796021084747337135)
          ·
            refine ⟨4020785694031627121005703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2680523796021084747337135 4020785694031627121005703)
            ·
              refine ⟨6031178541047440681508555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4020785694031627121005703 6031178541047440681508555)
              ·
                refine ⟨9046767811571161022262833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6031178541047440681508555 9046767811571161022262833)
                ·
                  refine ⟨6785075858678370766697125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9046767811571161022262833 6785075858678370766697125)
                  ·
                    refine ⟨1272201723502194518755711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6785075858678370766697125 1272201723502194518755711)
                    ·
                      rfl

theorem cell22_3716406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_3716406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716406 prefixEnd_3716406 := by exact prefixLift 3716406
  have htrace : WordTrace (prefixWord ++ tailWord_3716406) baseStart_3716406 baseEnd_3716406 := by
    simpa [prefixWord, tailWord_3716406, baseEnd_3716406] using wordTrace_append hprefix tailTrace_3716406
  have hstable : (prefixWord ++ tailWord_3716406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716406).length < 2 ^ (prefixWord ++ tailWord_3716406).sum := by decide
  have hdescent : baseEnd_3716406 < baseStart_3716406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716473 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 1, 6]
def baseStart_3716473 : Nat := 118140960795 + 3716473 * 2 ^ 59
def prefixEnd_3716473 : Nat := 4983230072969 + 3 ^ 40 * 3716473 * 2
def baseEnd_3716473 : Nat := 1272224658971428677330505

theorem tailTrace_3716473 : CollatzResearch.WordTrace tailWord_3716473 prefixEnd_3716473 1272224658971428677330505 := by
  unfold tailWord_3716473
  simp only [CollatzResearch.WordTrace]
  refine ⟨135550906264860518900626073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90367270843240345933750715 135550906264860518900626073)
  ·
    refine ⟨101663179698645389175469555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135550906264860518900626073 101663179698645389175469555)
    ·
      refine ⟨152494769547968083763204333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101663179698645389175469555 152494769547968083763204333)
      ·
        refine ⟨57185538580488031411201625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152494769547968083763204333 57185538580488031411201625)
        ·
          refine ⟨42889153935366023558401219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57185538580488031411201625 42889153935366023558401219)
          ·
            refine ⟨64333730903049035337601829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42889153935366023558401219 64333730903049035337601829)
            ·
              refine ⟨12062574544321694125800343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64333730903049035337601829 12062574544321694125800343)
              ·
                refine ⟨18093861816482541188700515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12062574544321694125800343 18093861816482541188700515)
                ·
                  refine ⟨27140792724723811783050773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18093861816482541188700515 27140792724723811783050773)
                  ·
                    refine ⟨1272224658971428677330505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27140792724723811783050773 1272224658971428677330505)
                    ·
                      rfl

theorem cell22_3716473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_3716473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716473 prefixEnd_3716473 := by exact prefixLift 3716473
  have htrace : WordTrace (prefixWord ++ tailWord_3716473) baseStart_3716473 baseEnd_3716473 := by
    simpa [prefixWord, tailWord_3716473, baseEnd_3716473] using wordTrace_append hprefix tailTrace_3716473
  have hstable : (prefixWord ++ tailWord_3716473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716473).length < 2 ^ (prefixWord ++ tailWord_3716473).sum := by decide
  have hdescent : baseEnd_3716473 < baseStart_3716473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716488 : List Nat := [2, 1, 3, 3, 1, 2, 10]
def baseStart_3716488 : Nat := 118140960795 + 3716488 * 2 ^ 59
def prefixEnd_3716488 : Nat := 4983230072969 + 3 ^ 40 * 3716488 * 2
def baseEnd_3716488 : Nat := 47119621991776801415017

theorem tailTrace_3716488 : CollatzResearch.WordTrace tailWord_3716488 prefixEnd_3716488 47119621991776801415017 := by
  unfold tailWord_3716488
  simp only [CollatzResearch.WordTrace]
  refine ⟨67775726679903088231211059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90367635573204117641614745 67775726679903088231211059)
  ·
    refine ⟨101663590019854632346816589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67775726679903088231211059 101663590019854632346816589)
    ·
      refine ⟨38123846257445487130056221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101663590019854632346816589 38123846257445487130056221)
      ·
        refine ⟨14296442346542057673771083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38123846257445487130056221 14296442346542057673771083)
        ·
          refine ⟨21444663519813086510656625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14296442346542057673771083 21444663519813086510656625)
          ·
            refine ⟨16083497639859814882992469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21444663519813086510656625 16083497639859814882992469)
            ·
              refine ⟨47119621991776801415017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16083497639859814882992469 47119621991776801415017)
              ·
                rfl

theorem cell22_3716488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 10].length) (baseStart_3716488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716488 prefixEnd_3716488 := by exact prefixLift 3716488
  have htrace : WordTrace (prefixWord ++ tailWord_3716488) baseStart_3716488 baseEnd_3716488 := by
    simpa [prefixWord, tailWord_3716488, baseEnd_3716488] using wordTrace_append hprefix tailTrace_3716488
  have hstable : (prefixWord ++ tailWord_3716488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716488).length < 2 ^ (prefixWord ++ tailWord_3716488).sum := by decide
  have hdescent : baseEnd_3716488 < baseStart_3716488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716494 : List Nat := [4, 1, 1, 4, 3, 1, 1, 1, 6]
def baseStart_3716494 : Nat := 118140960795 + 3716494 * 2 ^ 59
def prefixEnd_3716494 : Nat := 4983230072969 + 3 ^ 40 * 3716494 * 2
def baseEnd_3716494 : Nat := 424077282566863874185147

theorem tailTrace_3716494 : CollatzResearch.WordTrace tailWord_3716494 prefixEnd_3716494 424077282566863874185147 := by
  unfold tailWord_3716494
  simp only [CollatzResearch.WordTrace]
  refine ⟨16943959024723054935892567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90367781465189626324760357 16943959024723054935892567)
  ·
    refine ⟨25415938537084582403838851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16943959024723054935892567 25415938537084582403838851)
    ·
      refine ⟨38123907805626873605758277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25415938537084582403838851 38123907805626873605758277)
      ·
        refine ⟨7148232713555038801079677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38123907805626873605758277 7148232713555038801079677)
        ·
          refine ⟨2680587267583139550404879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7148232713555038801079677 2680587267583139550404879)
          ·
            refine ⟨4020880901374709325607319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2680587267583139550404879 4020880901374709325607319)
            ·
              refine ⟨6031321352062063988410979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4020880901374709325607319 6031321352062063988410979)
              ·
                refine ⟨9046982028093095982616469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6031321352062063988410979 9046982028093095982616469)
                ·
                  refine ⟨424077282566863874185147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9046982028093095982616469 424077282566863874185147)
                  ·
                    rfl

theorem cell22_3716494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_3716494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716494 prefixEnd_3716494 := by exact prefixLift 3716494
  have htrace : WordTrace (prefixWord ++ tailWord_3716494) baseStart_3716494 baseEnd_3716494 := by
    simpa [prefixWord, tailWord_3716494, baseEnd_3716494] using wordTrace_append hprefix tailTrace_3716494
  have hstable : (prefixWord ++ tailWord_3716494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716494).length < 2 ^ (prefixWord ++ tailWord_3716494).sum := by decide
  have hdescent : baseEnd_3716494 < baseStart_3716494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716509 : List Nat := [1, 4, 2, 1, 3, 1, 4, 1, 2, 3]
def baseStart_3716509 : Nat := 118140960795 + 3716509 * 2 ^ 59
def prefixEnd_3716509 : Nat := 4983230072969 + 3 ^ 40 * 3716509 * 2
def baseEnd_3716509 : Nat := 1272236982507136583430395

theorem tailTrace_3716509 : CollatzResearch.WordTrace tailWord_3716509 prefixEnd_3716509 1272236982507136583430395 := by
  unfold tailWord_3716509
  simp only [CollatzResearch.WordTrace]
  refine ⟨135552219292730097048936581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90368146195153398032624387 135552219292730097048936581)
  ·
    refine ⟨25416041117386893196675609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135552219292730097048936581 25416041117386893196675609)
    ·
      refine ⟨19062030838040169897506707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25416041117386893196675609 19062030838040169897506707)
      ·
        refine ⟨28593046257060254846260061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19062030838040169897506707 28593046257060254846260061)
        ·
          refine ⟨10722392346397595567347523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28593046257060254846260061 10722392346397595567347523)
          ·
            refine ⟨16083588519596393351021285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10722392346397595567347523 16083588519596393351021285)
            ·
              refine ⟨3015672847424323753316491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16083588519596393351021285 3015672847424323753316491)
              ·
                refine ⟨4523509271136485629974737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3015672847424323753316491 4523509271136485629974737)
                ·
                  refine ⟨3392631953352364222481053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4523509271136485629974737 3392631953352364222481053)
                  ·
                    refine ⟨1272236982507136583430395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3392631953352364222481053 1272236982507136583430395)
                    ·
                      rfl

theorem cell22_3716509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_3716509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716509 prefixEnd_3716509 := by exact prefixLift 3716509
  have htrace : WordTrace (prefixWord ++ tailWord_3716509) baseStart_3716509 baseEnd_3716509 := by
    simpa [prefixWord, tailWord_3716509, baseEnd_3716509] using wordTrace_append hprefix tailTrace_3716509
  have hstable : (prefixWord ++ tailWord_3716509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716509).length < 2 ^ (prefixWord ++ tailWord_3716509).sum := by decide
  have hdescent : baseEnd_3716509 < baseStart_3716509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716554 : List Nat := [3, 1, 2, 1, 2, 4, 1, 4, 1, 3]
def baseStart_3716554 : Nat := 118140960795 + 3716554 * 2 ^ 59
def prefixEnd_3716554 : Nat := 4983230072969 + 3 ^ 40 * 3716554 * 2
def baseEnd_3716554 : Nat := 1272252386926771466055257

theorem tailTrace_3716554 : CollatzResearch.WordTrace tailWord_3716554 prefixEnd_3716554 1272252386926771466055257 := by
  unfold tailWord_3716554
  simp only [CollatzResearch.WordTrace]
  refine ⟨33888465144391767433581179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90369240385044713156216477 33888465144391767433581179)
  ·
    refine ⟨50832697716587651150371769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33888465144391767433581179 50832697716587651150371769)
    ·
      refine ⟨38124523287440738362778827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50832697716587651150371769 38124523287440738362778827)
      ·
        refine ⟨57186784931161107544168241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38124523287440738362778827 57186784931161107544168241)
        ·
          refine ⟨42890088698370830658126181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57186784931161107544168241 42890088698370830658126181)
          ·
            refine ⟨8041891630944530748398659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42890088698370830658126181 8041891630944530748398659)
            ·
              refine ⟨12062837446416796122597989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8041891630944530748398659 12062837446416796122597989)
              ·
                refine ⟨2261782021203149272987123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12062837446416796122597989 2261782021203149272987123)
                ·
                  refine ⟨3392673031804723909480685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2261782021203149272987123 3392673031804723909480685)
                  ·
                    refine ⟨1272252386926771466055257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3392673031804723909480685 1272252386926771466055257)
                    ·
                      rfl

theorem cell22_3716554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_3716554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716554 prefixEnd_3716554 := by exact prefixLift 3716554
  have htrace : WordTrace (prefixWord ++ tailWord_3716554) baseStart_3716554 baseEnd_3716554 := by
    simpa [prefixWord, tailWord_3716554, baseEnd_3716554] using wordTrace_append hprefix tailTrace_3716554
  have hstable : (prefixWord ++ tailWord_3716554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716554).length < 2 ^ (prefixWord ++ tailWord_3716554).sum := by decide
  have hdescent : baseEnd_3716554 < baseStart_3716554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716565 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 2, 5]
def baseStart_3716565 : Nat := 118140960795 + 3716565 * 2 ^ 59
def prefixEnd_3716565 : Nat := 4983230072969 + 3 ^ 40 * 3716565 * 2
def baseEnd_3716565 : Nat := 1272256152451571104030223

theorem tailTrace_3716565 : CollatzResearch.WordTrace tailWord_3716565 prefixEnd_3716565 1272256152451571104030223 := by
  unfold tailWord_3716565
  simp only [CollatzResearch.WordTrace]
  refine ⟨135554261780527218612975149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90369507853684812408650099 135554261780527218612975149)
  ·
    refine ⟨50832848167697706979865681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135554261780527218612975149 50832848167697706979865681)
    ·
      refine ⟨38124636125773280234899261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50832848167697706979865681 38124636125773280234899261)
      ·
        refine ⟨14296738547164980088087223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38124636125773280234899261 14296738547164980088087223)
        ·
          refine ⟨21445107820747470132130835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14296738547164980088087223 21445107820747470132130835)
          ·
            refine ⟨32167661731121205198196253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21445107820747470132130835 32167661731121205198196253)
            ·
              refine ⟨12062873149170451949323595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32167661731121205198196253 12062873149170451949323595)
              ·
                refine ⟨18094309723755677923985393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12062873149170451949323595 18094309723755677923985393)
                ·
                  refine ⟨13570732292816758442989045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18094309723755677923985393 13570732292816758442989045)
                  ·
                    refine ⟨1272256152451571104030223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13570732292816758442989045 1272256152451571104030223)
                    ·
                      rfl

theorem cell22_3716565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_3716565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716565 prefixEnd_3716565 := by exact prefixLift 3716565
  have htrace : WordTrace (prefixWord ++ tailWord_3716565) baseStart_3716565 baseEnd_3716565 := by
    simpa [prefixWord, tailWord_3716565, baseEnd_3716565] using wordTrace_append hprefix tailTrace_3716565
  have hstable : (prefixWord ++ tailWord_3716565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716565).length < 2 ^ (prefixWord ++ tailWord_3716565).sum := by decide
  have hdescent : baseEnd_3716565 < baseStart_3716565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716627 : List Nat := [1, 1, 1, 2, 1, 8, 1, 1, 1, 5]
def baseStart_3716627 : Nat := 118140960795 + 3716627 * 2 ^ 59
def prefixEnd_3716627 : Nat := 4983230072969 + 3 ^ 40 * 3716627 * 2
def baseEnd_3716627 : Nat := 1272277376318623608980033

theorem tailTrace_3716627 : CollatzResearch.WordTrace tailWord_3716627 prefixEnd_3716627 1272277376318623608980033 := by
  unfold tailWord_3716627
  simp only [CollatzResearch.WordTrace]
  refine ⟨135556523106302603201732135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90371015404201735467821423 135556523106302603201732135)
  ·
    refine ⟨203334784659453904802598203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135556523106302603201732135 203334784659453904802598203)
    ·
      refine ⟨305002176989180857203897305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203334784659453904802598203 305002176989180857203897305)
      ·
        refine ⟨228751632741885642902922979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305002176989180857203897305 228751632741885642902922979)
        ·
          refine ⟨343127449112828464354384469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228751632741885642902922979 343127449112828464354384469)
          ·
            refine ⟨4021024794290958566652943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 343127449112828464354384469 4021024794290958566652943)
            ·
              refine ⟨6031537191436437849979415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4021024794290958566652943 6031537191436437849979415)
              ·
                refine ⟨9047305787154656774969123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6031537191436437849979415 9047305787154656774969123)
                ·
                  refine ⟨13570958680731985162453685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9047305787154656774969123 13570958680731985162453685)
                  ·
                    refine ⟨1272277376318623608980033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13570958680731985162453685 1272277376318623608980033)
                    ·
                      rfl

theorem cell22_3716627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 5].length) (baseStart_3716627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716627 prefixEnd_3716627 := by exact prefixLift 3716627
  have htrace : WordTrace (prefixWord ++ tailWord_3716627) baseStart_3716627 baseEnd_3716627 := by
    simpa [prefixWord, tailWord_3716627, baseEnd_3716627] using wordTrace_append hprefix tailTrace_3716627
  have hstable : (prefixWord ++ tailWord_3716627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716627).length < 2 ^ (prefixWord ++ tailWord_3716627).sum := by decide
  have hdescent : baseEnd_3716627 < baseStart_3716627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716678 : List Nat := [6, 1, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_3716678 : Nat := 118140960795 + 3716678 * 2 ^ 59
def prefixEnd_3716678 : Nat := 4983230072969 + 3 ^ 40 * 3716678 * 2
def baseEnd_3716678 : Nat := 1272294834660876475954877

theorem tailTrace_3716678 : CollatzResearch.WordTrace tailWord_3716678 prefixEnd_3716678 1272294834660876475954877 := by
  unfold tailWord_3716678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4236199475909932465994959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90372255486078559274559125 4236199475909932465994959)
  ·
    refine ⟨6354299213864898698992439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4236199475909932465994959 6354299213864898698992439)
    ·
      refine ⟨9531448820797348048488659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6354299213864898698992439 9531448820797348048488659)
      ·
        refine ⟨14297173231196022072732989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9531448820797348048488659 14297173231196022072732989)
        ·
          refine ⟨5361439961698508277274871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14297173231196022072732989 5361439961698508277274871)
          ·
            refine ⟨8042159942547762415912307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5361439961698508277274871 8042159942547762415912307)
            ·
              refine ⟨12063239913821643623868461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8042159942547762415912307 12063239913821643623868461)
              ·
                refine ⟨4523714967683116358950673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12063239913821643623868461 4523714967683116358950673)
                ·
                  refine ⟨3392786225762337269213005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4523714967683116358950673 3392786225762337269213005)
                  ·
                    refine ⟨1272294834660876475954877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3392786225762337269213005 1272294834660876475954877)
                    ·
                      rfl

theorem cell22_3716678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_3716678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716678 prefixEnd_3716678 := by exact prefixLift 3716678
  have htrace : WordTrace (prefixWord ++ tailWord_3716678) baseStart_3716678 baseEnd_3716678 := by
    simpa [prefixWord, tailWord_3716678, baseEnd_3716678] using wordTrace_append hprefix tailTrace_3716678
  have hstable : (prefixWord ++ tailWord_3716678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716678).length < 2 ^ (prefixWord ++ tailWord_3716678).sum := by decide
  have hdescent : baseEnd_3716678 < baseStart_3716678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716766 : List Nat := [4, 3, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_3716766 : Nat := 118140960795 + 3716766 * 2 ^ 59
def prefixEnd_3716766 : Nat := 4983230072969 + 3 ^ 40 * 3716766 * 2
def baseEnd_3716766 : Nat := 1272324958859273579754607

theorem tailTrace_3716766 : CollatzResearch.WordTrace tailWord_3716766 prefixEnd_3716766 1272324958859273579754607 := by
  unfold tailWord_3716766
  simp only [CollatzResearch.WordTrace]
  refine ⟨16945199106599878742630269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90374395235199353294028101 16945199106599878742630269)
  ·
    refine ⟨6354449664974954528486351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16945199106599878742630269 6354449664974954528486351)
    ·
      refine ⟨9531674497462431792729527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6354449664974954528486351 9531674497462431792729527)
      ·
        refine ⟨14297511746193647689094291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9531674497462431792729527 14297511746193647689094291)
        ·
          refine ⟨21446267619290471533641437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14297511746193647689094291 21446267619290471533641437)
          ·
            refine ⟨8042350357233926825115539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21446267619290471533641437 8042350357233926825115539)
            ·
              refine ⟨12063525535850890237673309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8042350357233926825115539 12063525535850890237673309)
              ·
                refine ⟨4523822075944083839127491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12063525535850890237673309 4523822075944083839127491)
                ·
                  refine ⟨6785733113916125758691237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4523822075944083839127491 6785733113916125758691237)
                  ·
                    refine ⟨1272324958859273579754607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6785733113916125758691237 1272324958859273579754607)
                    ·
                      rfl

theorem cell22_3716766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_3716766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716766 prefixEnd_3716766 := by exact prefixLift 3716766
  have htrace : WordTrace (prefixWord ++ tailWord_3716766) baseStart_3716766 baseEnd_3716766 := by
    simpa [prefixWord, tailWord_3716766, baseEnd_3716766] using wordTrace_append hprefix tailTrace_3716766
  have hstable : (prefixWord ++ tailWord_3716766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716766).length < 2 ^ (prefixWord ++ tailWord_3716766).sum := by decide
  have hdescent : baseEnd_3716766 < baseStart_3716766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716837 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 7]
def baseStart_3716837 : Nat := 118140960795 + 3716837 * 2 ^ 59
def prefixEnd_3716837 : Nat := 4983230072969 + 3 ^ 40 * 3716837 * 2
def baseEnd_3716837 : Nat := 424116421203417687076463

theorem tailTrace_3716837 : CollatzResearch.WordTrace tailWord_3716837 prefixEnd_3716837 424116421203417687076463 := by
  unfold tailWord_3716837
  simp only [CollatzResearch.WordTrace]
  refine ⟨135564182435541809066876765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90376121623694539377917843 135564182435541809066876765)
  ·
    refine ⟨50836568413328178400078787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135564182435541809066876765 50836568413328178400078787)
    ·
      refine ⟨76254852619992267600118181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50836568413328178400078787 76254852619992267600118181)
      ·
        refine ⟨14297784866248550175022159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76254852619992267600118181 14297784866248550175022159)
        ·
          refine ⟨21446677299372825262533239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14297784866248550175022159 21446677299372825262533239)
          ·
            refine ⟨32170015949059237893799859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21446677299372825262533239 32170015949059237893799859)
            ·
              refine ⟨48255023923588856840699789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32170015949059237893799859 48255023923588856840699789)
              ·
                refine ⟨18095633971345821315262421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48255023923588856840699789 18095633971345821315262421)
                ·
                  refine ⟨424116421203417687076463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18095633971345821315262421 424116421203417687076463)
                  ·
                    rfl

theorem cell22_3716837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_3716837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716837 prefixEnd_3716837 := by exact prefixLift 3716837
  have htrace : WordTrace (prefixWord ++ tailWord_3716837) baseStart_3716837 baseEnd_3716837 := by
    simpa [prefixWord, tailWord_3716837, baseEnd_3716837] using wordTrace_append hprefix tailTrace_3716837
  have hstable : (prefixWord ++ tailWord_3716837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716837).length < 2 ^ (prefixWord ++ tailWord_3716837).sum := by decide
  have hdescent : baseEnd_3716837 < baseStart_3716837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716914 : List Nat := [3, 2, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_3716914 : Nat := 118140960795 + 3716914 * 2 ^ 59
def prefixEnd_3716914 : Nat := 4983230072969 + 3 ^ 40 * 3716914 * 2
def baseEnd_3716914 : Nat := 1272375622283850527054153

theorem tailTrace_3716914 : CollatzResearch.WordTrace tailWord_3716914 prefixEnd_3716914 1272375622283850527054153 := by
  unfold tailWord_3716914
  simp only [CollatzResearch.WordTrace]
  refine ⟨33891747714065712804357449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90377993904175234144953197 33891747714065712804357449)
  ·
    refine ⟨25418810785549284603268087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33891747714065712804357449 25418810785549284603268087)
    ·
      refine ⟨38128216178323926904902131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25418810785549284603268087 38128216178323926904902131)
      ·
        refine ⟨57192324267485890357353197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38128216178323926904902131 57192324267485890357353197)
        ·
          refine ⟨21447121600307208884007449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57192324267485890357353197 21447121600307208884007449)
          ·
            refine ⟨16085341200230406663005587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21447121600307208884007449 16085341200230406663005587)
            ·
              refine ⟨24128011800345609994508381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16085341200230406663005587 24128011800345609994508381)
              ·
                refine ⟨9048004425129603747940643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24128011800345609994508381 9048004425129603747940643)
                ·
                  refine ⟨13572006637694405621910965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9048004425129603747940643 13572006637694405621910965)
                  ·
                    refine ⟨1272375622283850527054153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13572006637694405621910965 1272375622283850527054153)
                    ·
                      rfl

theorem cell22_3716914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_3716914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716914 prefixEnd_3716914 := by exact prefixLift 3716914
  have htrace : WordTrace (prefixWord ++ tailWord_3716914) baseStart_3716914 baseEnd_3716914 := by
    simpa [prefixWord, tailWord_3716914, baseEnd_3716914] using wordTrace_append hprefix tailTrace_3716914
  have hstable : (prefixWord ++ tailWord_3716914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716914).length < 2 ^ (prefixWord ++ tailWord_3716914).sum := by decide
  have hdescent : baseEnd_3716914 < baseStart_3716914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716916 : List Nat := [2, 5, 1, 1, 2, 2, 1, 2, 6]
def baseStart_3716916 : Nat := 118140960795 + 3716916 * 2 ^ 59
def prefixEnd_3716916 : Nat := 4983230072969 + 3 ^ 40 * 3716916 * 2
def baseEnd_3716916 : Nat := 424125435641574396168049

theorem tailTrace_3716916 : CollatzResearch.WordTrace tailWord_3716916 prefixEnd_3716916 424125435641574396168049 := by
  unfold tailWord_3716916
  simp only [CollatzResearch.WordTrace]
  refine ⟨67783531901127802779501301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90378042534837070372668401 67783531901127802779501301)
  ·
    refine ⟨6354706115730731510578247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67783531901127802779501301 6354706115730731510578247)
    ·
      refine ⟨9532059173596097265867371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6354706115730731510578247 9532059173596097265867371)
      ·
        refine ⟨14298088760394145898801057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9532059173596097265867371 14298088760394145898801057)
        ·
          refine ⟨10723566570295609424100793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14298088760394145898801057 10723566570295609424100793)
          ·
            refine ⟨8042674927721707068075595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10723566570295609424100793 8042674927721707068075595)
            ·
              refine ⟨12064012391582560602113393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8042674927721707068075595 12064012391582560602113393)
              ·
                refine ⟨9048009293686920451585045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12064012391582560602113393 9048009293686920451585045)
                ·
                  refine ⟨424125435641574396168049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9048009293686920451585045 424125435641574396168049)
                  ·
                    rfl

theorem cell22_3716916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_3716916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716916 prefixEnd_3716916 := by exact prefixLift 3716916
  have htrace : WordTrace (prefixWord ++ tailWord_3716916) baseStart_3716916 baseEnd_3716916 := by
    simpa [prefixWord, tailWord_3716916, baseEnd_3716916] using wordTrace_append hprefix tailTrace_3716916
  have hstable : (prefixWord ++ tailWord_3716916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716916).length < 2 ^ (prefixWord ++ tailWord_3716916).sum := by decide
  have hdescent : baseEnd_3716916 < baseStart_3716916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716948 : List Nat := [2, 4, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_3716948 : Nat := 118140960795 + 3716948 * 2 ^ 59
def prefixEnd_3716948 : Nat := 4983230072969 + 3 ^ 40 * 3716948 * 2
def baseEnd_3716948 : Nat := 1272387261178685771704049

theorem tailTrace_3716948 : CollatzResearch.WordTrace tailWord_3716948 prefixEnd_3716948 1272387261178685771704049 := by
  unfold tailWord_3716948
  simp only [CollatzResearch.WordTrace]
  refine ⟨67784115469069837512083749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90378820625426450016111665 67784115469069837512083749)
  ·
    refine ⟨12709521650450594533515703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67784115469069837512083749 12709521650450594533515703)
    ·
      refine ⟨19064282475675891800273555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12709521650450594533515703 19064282475675891800273555)
      ·
        refine ⟨28596423713513837700410333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19064282475675891800273555 28596423713513837700410333)
        ·
          refine ⟨10723658892567689137653875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28596423713513837700410333 10723658892567689137653875)
          ·
            refine ⟨16085488338851533706480813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10723658892567689137653875 16085488338851533706480813)
            ·
              refine ⟨6032058127069325139930305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16085488338851533706480813 6032058127069325139930305)
              ·
                refine ⟨4524043595301993854947729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6032058127069325139930305 4524043595301993854947729)
                ·
                  refine ⟨3393032696476495391210797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4524043595301993854947729 3393032696476495391210797)
                  ·
                    refine ⟨1272387261178685771704049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3393032696476495391210797 1272387261178685771704049)
                    ·
                      rfl

theorem cell22_3716948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_3716948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3716948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3716948 prefixEnd_3716948 := by exact prefixLift 3716948
  have htrace : WordTrace (prefixWord ++ tailWord_3716948) baseStart_3716948 baseEnd_3716948 := by
    simpa [prefixWord, tailWord_3716948, baseEnd_3716948] using wordTrace_append hprefix tailTrace_3716948
  have hstable : (prefixWord ++ tailWord_3716948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716948).length < 2 ^ (prefixWord ++ tailWord_3716948).sum := by decide
  have hdescent : baseEnd_3716948 < baseStart_3716948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717010 : List Nat := [3, 2, 3, 2, 1, 3, 1, 1, 3, 3]
def baseStart_3717010 : Nat := 118140960795 + 3717010 * 2 ^ 59
def prefixEnd_3717010 : Nat := 4983230072969 + 3 ^ 40 * 3717010 * 2
def baseEnd_3717010 : Nat := 1272408485045738276653859

theorem tailTrace_3717010 : CollatzResearch.WordTrace tailWord_3717010 prefixEnd_3717010 1272408485045738276653859 := by
  unfold tailWord_3717010
  simp only [CollatzResearch.WordTrace]
  refine ⟨33892623065978764903231121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90380328175943373075282989 33892623065978764903231121)
  ·
    refine ⟨25419467299484073677423341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33892623065978764903231121 25419467299484073677423341)
    ·
      refine ⟨9532300237306527629033753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25419467299484073677423341 9532300237306527629033753)
      ·
        refine ⟨7149225177979895721775315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9532300237306527629033753 7149225177979895721775315)
        ·
          refine ⟨10723837766969843582662973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7149225177979895721775315 10723837766969843582662973)
          ·
            refine ⟨4021439162613691343498615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10723837766969843582662973 4021439162613691343498615)
            ·
              refine ⟨6032158743920537015247923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4021439162613691343498615 6032158743920537015247923)
              ·
                refine ⟨9048238115880805522871885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6032158743920537015247923 9048238115880805522871885)
                ·
                  refine ⟨3393089293455302071076957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9048238115880805522871885 3393089293455302071076957)
                  ·
                    refine ⟨1272408485045738276653859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3393089293455302071076957 1272408485045738276653859)
                    ·
                      rfl

theorem cell22_3717010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_3717010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717010 prefixEnd_3717010 := by exact prefixLift 3717010
  have htrace : WordTrace (prefixWord ++ tailWord_3717010) baseStart_3717010 baseEnd_3717010 := by
    simpa [prefixWord, tailWord_3717010, baseEnd_3717010] using wordTrace_append hprefix tailTrace_3717010
  have hstable : (prefixWord ++ tailWord_3717010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717010).length < 2 ^ (prefixWord ++ tailWord_3717010).sum := by decide
  have hdescent : baseEnd_3717010 < baseStart_3717010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717066 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 4, 3]
def baseStart_3717066 : Nat := 118140960795 + 3717066 * 2 ^ 59
def prefixEnd_3717066 : Nat := 4983230072969 + 3 ^ 40 * 3717066 * 2
def baseEnd_3717066 : Nat := 1272427654990172797253687

theorem tailTrace_3717066 : CollatzResearch.WordTrace tailWord_3717066 prefixEnd_3717066 1272427654990172797253687 := by
  unfold tailWord_3717066
  simp only [CollatzResearch.WordTrace]
  refine ⟨33893133687928045294240763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90381689834474787451308701 33893133687928045294240763)
  ·
    refine ⟨50839700531892067941361145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33893133687928045294240763 50839700531892067941361145)
    ·
      refine ⟨38129775398919050956020859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50839700531892067941361145 38129775398919050956020859)
      ·
        refine ⟨57194663098378576434031289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38129775398919050956020859 57194663098378576434031289)
        ·
          refine ⟨42895997323783932325523467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57194663098378576434031289 42895997323783932325523467)
          ·
            refine ⟨64343995985675898488285201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42895997323783932325523467 64343995985675898488285201)
            ·
              refine ⟨48257996989256923866213901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64343995985675898488285201 48257996989256923866213901)
              ·
                refine ⟨18096748870971346449830213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48257996989256923866213901 18096748870971346449830213)
                ·
                  refine ⟨3393140413307127459343165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18096748870971346449830213 3393140413307127459343165)
                  ·
                    refine ⟨1272427654990172797253687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3393140413307127459343165 1272427654990172797253687)
                    ·
                      rfl

theorem cell22_3717066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_3717066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717066 prefixEnd_3717066 := by exact prefixLift 3717066
  have htrace : WordTrace (prefixWord ++ tailWord_3717066) baseStart_3717066 baseEnd_3717066 := by
    simpa [prefixWord, tailWord_3717066, baseEnd_3717066] using wordTrace_append hprefix tailTrace_3717066
  have hstable : (prefixWord ++ tailWord_3717066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717066).length < 2 ^ (prefixWord ++ tailWord_3717066).sum := by decide
  have hdescent : baseEnd_3717066 < baseStart_3717066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717068 : List Nat := [2, 2, 1, 4, 1, 3, 1, 4, 4]
def baseStart_3717068 : Nat := 118140960795 + 3717068 * 2 ^ 59
def prefixEnd_3717068 : Nat := 4983230072969 + 3 ^ 40 * 3717068 * 2
def baseEnd_3717068 : Nat := 424142779877015152901227

theorem tailTrace_3717068 : CollatzResearch.WordTrace tailWord_3717068 prefixEnd_3717068 424142779877015152901227 := by
  unfold tailWord_3717068
  simp only [CollatzResearch.WordTrace]
  refine ⟨67786303848852467759267929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90381738465136623679023905 67786303848852467759267929)
  ·
    refine ⟨50839727886639350819450947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67786303848852467759267929 50839727886639350819450947)
    ·
      refine ⟨76259591829959026229176421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50839727886639350819450947 76259591829959026229176421)
      ·
        refine ⟨14298673468117317417970579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76259591829959026229176421 14298673468117317417970579)
        ·
          refine ⟨21448010202175976126955869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14298673468117317417970579 21448010202175976126955869)
          ·
            refine ⟨8043003825815991047608451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21448010202175976126955869 8043003825815991047608451)
            ·
              refine ⟨12064505738723986571412677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8043003825815991047608451 12064505738723986571412677)
              ·
                refine ⟨2262094826010747482139877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12064505738723986571412677 2262094826010747482139877)
                ·
                  refine ⟨424142779877015152901227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2262094826010747482139877 424142779877015152901227)
                  ·
                    rfl

theorem cell22_3717068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_3717068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717068 prefixEnd_3717068 := by exact prefixLift 3717068
  have htrace : WordTrace (prefixWord ++ tailWord_3717068) baseStart_3717068 baseEnd_3717068 := by
    simpa [prefixWord, tailWord_3717068, baseEnd_3717068] using wordTrace_append hprefix tailTrace_3717068
  have hstable : (prefixWord ++ tailWord_3717068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717068).length < 2 ^ (prefixWord ++ tailWord_3717068).sum := by decide
  have hdescent : baseEnd_3717068 < baseStart_3717068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717128 : List Nat := [2, 1, 3, 2, 1, 2, 4, 1, 3, 3]
def baseStart_3717128 : Nat := 118140960795 + 3717128 * 2 ^ 59
def prefixEnd_3717128 : Nat := 4983230072969 + 3 ^ 40 * 3717128 * 2
def baseEnd_3717128 : Nat := 1272448878857225302203497

theorem tailTrace_3717128 : CollatzResearch.WordTrace tailWord_3717128 prefixEnd_3717128 1272448878857225302203497 := by
  unfold tailWord_3717128
  simp only [CollatzResearch.WordTrace]
  refine ⟨67787398038743782882860019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90383197384991710510480025 67787398038743782882860019)
  ·
    refine ⟨101681097058115674324290029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67787398038743782882860019 101681097058115674324290029)
    ·
      refine ⟨38130411396793377871608761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101681097058115674324290029 38130411396793377871608761)
      ·
        refine ⟨28597808547595033403706571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38130411396793377871608761 28597808547595033403706571)
        ·
          refine ⟨42896712821392550105559857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28597808547595033403706571 42896712821392550105559857)
          ·
            refine ⟨32172534616044412579169893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42896712821392550105559857 32172534616044412579169893)
            ·
              refine ⟨6032350240508327358594355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32172534616044412579169893 6032350240508327358594355)
              ·
                refine ⟨9048525360762491037891533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6032350240508327358594355 9048525360762491037891533)
                ·
                  refine ⟨3393197010285934139209325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9048525360762491037891533 3393197010285934139209325)
                  ·
                    refine ⟨1272448878857225302203497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3393197010285934139209325 1272448878857225302203497)
                    ·
                      rfl

theorem cell22_3717128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_3717128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717128 prefixEnd_3717128 := by exact prefixLift 3717128
  have htrace : WordTrace (prefixWord ++ tailWord_3717128) baseStart_3717128 baseEnd_3717128 := by
    simpa [prefixWord, tailWord_3717128, baseEnd_3717128] using wordTrace_append hprefix tailTrace_3717128
  have hstable : (prefixWord ++ tailWord_3717128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717128).length < 2 ^ (prefixWord ++ tailWord_3717128).sum := by decide
  have hdescent : baseEnd_3717128 < baseStart_3717128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717162 : List Nat := [3, 1, 4, 1, 2, 1, 3, 3, 1, 3]
def baseStart_3717162 : Nat := 118140960795 + 3717162 * 2 ^ 59
def prefixEnd_3717162 : Nat := 4983230072969 + 3 ^ 40 * 3717162 * 2
def baseEnd_3717162 : Nat := 1272460517752060546853393

theorem tailTrace_3717162 : CollatzResearch.WordTrace tailWord_3717162 prefixEnd_3717162 1272460517752060546853393 := by
  unfold tailWord_3717162
  simp only [CollatzResearch.WordTrace]
  refine ⟨33894009039841097393114435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90384024106242926381638493 33894009039841097393114435)
  ·
    refine ⟨50841013559761646089671653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33894009039841097393114435 50841013559761646089671653)
    ·
      refine ⟨9532690042455308641813435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50841013559761646089671653 9532690042455308641813435)
      ·
        refine ⟨14299035063682962962720153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9532690042455308641813435 14299035063682962962720153)
        ·
          refine ⟨10724276297762222222040115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14299035063682962962720153 10724276297762222222040115)
          ·
            refine ⟨16086414446643333333060173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10724276297762222222040115 16086414446643333333060173)
            ·
              refine ⟨6032405417491249999897565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16086414446643333333060173 6032405417491249999897565)
              ·
                refine ⟨2262152031559218749961587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6032405417491249999897565 2262152031559218749961587)
                ·
                  refine ⟨3393228047338828124942381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2262152031559218749961587 3393228047338828124942381)
                  ·
                    refine ⟨1272460517752060546853393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3393228047338828124942381 1272460517752060546853393)
                    ·
                      rfl

theorem cell22_3717162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_3717162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717162 prefixEnd_3717162 := by exact prefixLift 3717162
  have htrace : WordTrace (prefixWord ++ tailWord_3717162) baseStart_3717162 baseEnd_3717162 := by
    simpa [prefixWord, tailWord_3717162, baseEnd_3717162] using wordTrace_append hprefix tailTrace_3717162
  have hstable : (prefixWord ++ tailWord_3717162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717162).length < 2 ^ (prefixWord ++ tailWord_3717162).sum := by decide
  have hdescent : baseEnd_3717162 < baseStart_3717162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717201 : List Nat := [1, 2, 2, 1, 3, 1, 1, 5, 1, 5]
def baseStart_3717201 : Nat := 118140960795 + 3717201 * 2 ^ 59
def prefixEnd_3717201 : Nat := 4983230072969 + 3 ^ 40 * 3717201 * 2
def baseEnd_3717201 : Nat := 1272473868249077445128273

theorem tailTrace_3717201 : CollatzResearch.WordTrace tailWord_3717201 prefixEnd_3717201 1272473868249077445128273 := by
  unfold tailWord_3717201
  simp only [CollatzResearch.WordTrace]
  refine ⟨135577458606223099233127457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90384972404148732822084971 135577458606223099233127457)
  ·
    refine ⟨101683093954667324424845593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135577458606223099233127457 101683093954667324424845593)
    ·
      refine ⟨76262320466000493318634195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101683093954667324424845593 76262320466000493318634195)
      ·
        refine ⟨114393480699000739977951293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76262320466000493318634195 114393480699000739977951293)
        ·
          refine ⟨42897555262125277491731735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114393480699000739977951293 42897555262125277491731735)
          ·
            refine ⟨64346332893187916237597603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42897555262125277491731735 64346332893187916237597603)
            ·
              refine ⟨96519499339781874356396405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64346332893187916237597603 96519499339781874356396405)
              ·
                refine ⟨9048703063104550720912163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96519499339781874356396405 9048703063104550720912163)
                ·
                  refine ⟨13573054594656826081368245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9048703063104550720912163 13573054594656826081368245)
                  ·
                    refine ⟨1272473868249077445128273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13573054594656826081368245 1272473868249077445128273)
                    ·
                      rfl

theorem cell22_3717201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_3717201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717201 prefixEnd_3717201 := by exact prefixLift 3717201
  have htrace : WordTrace (prefixWord ++ tailWord_3717201) baseStart_3717201 baseEnd_3717201 := by
    simpa [prefixWord, tailWord_3717201, baseEnd_3717201] using wordTrace_append hprefix tailTrace_3717201
  have hstable : (prefixWord ++ tailWord_3717201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717201).length < 2 ^ (prefixWord ++ tailWord_3717201).sum := by decide
  have hdescent : baseEnd_3717201 < baseStart_3717201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717205 : List Nat := [1, 3, 2, 2, 1, 5, 1, 2, 1, 4]
def baseStart_3717205 : Nat := 118140960795 + 3717205 * 2 ^ 59
def prefixEnd_3717205 : Nat := 4983230072969 + 3 ^ 40 * 3717205 * 2
def baseEnd_3717205 : Nat := 1272475237530822768028261

theorem tailTrace_3717205 : CollatzResearch.WordTrace tailWord_3717205 prefixEnd_3717205 1272475237530822768028261 := by
  unfold tailWord_3717205
  simp only [CollatzResearch.WordTrace]
  refine ⟨135577604498208607916273069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90385069665472405277515379 135577604498208607916273069)
  ·
    refine ⟨50841601686828227968602401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135577604498208607916273069 50841601686828227968602401)
    ·
      refine ⟨38131201265121170976451801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50841601686828227968602401 38131201265121170976451801)
      ·
        refine ⟨28598400948840878232338851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38131201265121170976451801 28598400948840878232338851)
        ·
          refine ⟨42897601423261317348508277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28598400948840878232338851 42897601423261317348508277)
          ·
            refine ⟨4021650133430748501422651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42897601423261317348508277 4021650133430748501422651)
            ·
              refine ⟨6032475200146122752133977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4021650133430748501422651 6032475200146122752133977)
              ·
                refine ⟨4524356400109592064100483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6032475200146122752133977 4524356400109592064100483)
                ·
                  refine ⟨6786534600164388096150725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4524356400109592064100483 6786534600164388096150725)
                  ·
                    refine ⟨1272475237530822768028261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6786534600164388096150725 1272475237530822768028261)
                    ·
                      rfl

theorem cell22_3717205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_3717205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717205 prefixEnd_3717205 := by exact prefixLift 3717205
  have htrace : WordTrace (prefixWord ++ tailWord_3717205) baseStart_3717205 baseEnd_3717205 := by
    simpa [prefixWord, tailWord_3717205, baseEnd_3717205] using wordTrace_append hprefix tailTrace_3717205
  have hstable : (prefixWord ++ tailWord_3717205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717205).length < 2 ^ (prefixWord ++ tailWord_3717205).sum := by decide
  have hdescent : baseEnd_3717205 < baseStart_3717205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717297 : List Nat := [1, 2, 2, 5, 2, 1, 2, 1, 3, 3]
def baseStart_3717297 : Nat := 118140960795 + 3717297 * 2 ^ 59
def prefixEnd_3717297 : Nat := 4983230072969 + 3 ^ 40 * 3717297 * 2
def baseEnd_3717297 : Nat := 1272506731010965194727979

theorem tailTrace_3717297 : CollatzResearch.WordTrace tailWord_3717297 prefixEnd_3717297 1272506731010965194727979 := by
  unfold tailWord_3717297
  simp only [CollatzResearch.WordTrace]
  refine ⟨135580960013875307628622145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90387306675916871752414763 135580960013875307628622145)
  ·
    refine ⟨101685720010406480721466609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135580960013875307628622145 101685720010406480721466609)
    ·
      refine ⟨76264290007804860541099957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101685720010406480721466609 76264290007804860541099957)
      ·
        refine ⟨7149777188231705675728121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76264290007804860541099957 7149777188231705675728121)
        ·
          refine ⟨5362332891173779256796091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7149777188231705675728121 5362332891173779256796091)
          ·
            refine ⟨8043499336760668885194137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5362332891173779256796091 8043499336760668885194137)
            ·
              refine ⟨6032624502570501663895603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8043499336760668885194137 6032624502570501663895603)
              ·
                refine ⟨9048936753855752495843405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6032624502570501663895603 9048936753855752495843405)
                ·
                  refine ⟨3393351282695907185941277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9048936753855752495843405 3393351282695907185941277)
                  ·
                    refine ⟨1272506731010965194727979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3393351282695907185941277 1272506731010965194727979)
                    ·
                      rfl

theorem cell22_3717297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_3717297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717297 prefixEnd_3717297 := by exact prefixLift 3717297
  have htrace : WordTrace (prefixWord ++ tailWord_3717297) baseStart_3717297 baseEnd_3717297 := by
    simpa [prefixWord, tailWord_3717297, baseEnd_3717297] using wordTrace_append hprefix tailTrace_3717297
  have hstable : (prefixWord ++ tailWord_3717297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717297).length < 2 ^ (prefixWord ++ tailWord_3717297).sum := by decide
  have hdescent : baseEnd_3717297 < baseStart_3717297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717314 : List Nat := [3, 5, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_3717314 : Nat := 118140960795 + 3717314 * 2 ^ 59
def prefixEnd_3717314 : Nat := 4983230072969 + 3 ^ 40 * 3717314 * 2
def baseEnd_3717314 : Nat := 1272512550458382817052927

theorem tailTrace_3717314 : CollatzResearch.WordTrace tailWord_3717314 prefixEnd_3717314 1272512550458382817052927 := by
  unfold tailWord_3717314
  simp only [CollatzResearch.WordTrace]
  refine ⟨33895395013703429882997749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90387720036542479687993997 33895395013703429882997749)
  ·
    refine ⟨3177693282534696551531039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33895395013703429882997749 3177693282534696551531039)
    ·
      refine ⟨4766539923802044827296559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3177693282534696551531039 4766539923802044827296559)
      ·
        refine ⟨7149809885703067240944839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4766539923802044827296559 7149809885703067240944839)
        ·
          refine ⟨10724714828554600861417259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7149809885703067240944839 10724714828554600861417259)
          ·
            refine ⟨16087072242831901292125889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10724714828554600861417259 16087072242831901292125889)
            ·
              refine ⟨12065304182123925969094417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16087072242831901292125889 12065304182123925969094417)
              ·
                refine ⟨9048978136592944476820813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12065304182123925969094417 9048978136592944476820813)
                ·
                  refine ⟨3393366801222354178807805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9048978136592944476820813 3393366801222354178807805)
                  ·
                    refine ⟨1272512550458382817052927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3393366801222354178807805 1272512550458382817052927)
                    ·
                      rfl

theorem cell22_3717314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_3717314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717314 prefixEnd_3717314 := by exact prefixLift 3717314
  have htrace : WordTrace (prefixWord ++ tailWord_3717314) baseStart_3717314 baseEnd_3717314 := by
    simpa [prefixWord, tailWord_3717314, baseEnd_3717314] using wordTrace_append hprefix tailTrace_3717314
  have hstable : (prefixWord ++ tailWord_3717314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717314).length < 2 ^ (prefixWord ++ tailWord_3717314).sum := by decide
  have hdescent : baseEnd_3717314 < baseStart_3717314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717321 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 8]
def baseStart_3717321 : Nat := 118140960795 + 3717321 * 2 ^ 59
def prefixEnd_3717321 : Nat := 4983230072969 + 3 ^ 40 * 3717321 * 2
def baseEnd_3717321 : Nat := 424171648900479044042635

theorem tailTrace_3717321 : CollatzResearch.WordTrace tailWord_3717321 prefixEnd_3717321 424171648900479044042635 := by
  unfold tailWord_3717321
  simp only [CollatzResearch.WordTrace]
  refine ⟨135581835365788359727495817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90387890243858906484997211 135581835365788359727495817)
  ·
    refine ⟨101686376524341269795621863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135581835365788359727495817 101686376524341269795621863)
    ·
      refine ⟨152529564786511904693432795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101686376524341269795621863 152529564786511904693432795)
      ·
        refine ⟨228794347179767857040149193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152529564786511904693432795 228794347179767857040149193)
        ·
          refine ⟨171595760384825892780111895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228794347179767857040149193 171595760384825892780111895)
          ·
            refine ⟨257393640577238839170167843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171595760384825892780111895 257393640577238839170167843)
            ·
              refine ⟨386090460865858258755251765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257393640577238839170167843 386090460865858258755251765)
              ·
                refine ⟨36195980706174211758304853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 386090460865858258755251765 36195980706174211758304853)
                ·
                  refine ⟨424171648900479044042635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36195980706174211758304853 424171648900479044042635)
                  ·
                    rfl

theorem cell22_3717321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 8].length) (baseStart_3717321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717321 prefixEnd_3717321 := by exact prefixLift 3717321
  have htrace : WordTrace (prefixWord ++ tailWord_3717321) baseStart_3717321 baseEnd_3717321 := by
    simpa [prefixWord, tailWord_3717321, baseEnd_3717321] using wordTrace_append hprefix tailTrace_3717321
  have hstable : (prefixWord ++ tailWord_3717321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717321).length < 2 ^ (prefixWord ++ tailWord_3717321).sum := by decide
  have hdescent : baseEnd_3717321 < baseStart_3717321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717385 : List Nat := [1, 2, 1, 1, 3, 5, 2, 1, 2, 4]
def baseStart_3717385 : Nat := 118140960795 + 3717385 * 2 ^ 59
def prefixEnd_3717385 : Nat := 4983230072969 + 3 ^ 40 * 3717385 * 2
def baseEnd_3717385 : Nat := 1272536855209362298527709

theorem tailTrace_3717385 : CollatzResearch.WordTrace tailWord_3717385 prefixEnd_3717385 1272536855209362298527709 := by
  unfold tailWord_3717385
  simp only [CollatzResearch.WordTrace]
  refine ⟨135584169637556498657825609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90389446425037665771883739 135584169637556498657825609)
  ·
    refine ⟨101688127228167373993369207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135584169637556498657825609 101688127228167373993369207)
    ·
      refine ⟨152532190842251060990053811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101688127228167373993369207 152532190842251060990053811)
      ·
        refine ⟨228798286263376591485080717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152532190842251060990053811 228798286263376591485080717)
        ·
          refine ⟨85799357348766221806905269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228798286263376591485080717 85799357348766221806905269)
          ·
            refine ⟨8043689751446833294397369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85799357348766221806905269 8043689751446833294397369)
            ·
              refine ⟨6032767313585124970798027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8043689751446833294397369 6032767313585124970798027)
              ·
                refine ⟨9049150970377687456197041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6032767313585124970798027 9049150970377687456197041)
                ·
                  refine ⟨6786863227783265592147781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9049150970377687456197041 6786863227783265592147781)
                  ·
                    refine ⟨1272536855209362298527709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6786863227783265592147781 1272536855209362298527709)
                    ·
                      rfl

theorem cell22_3717385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 4].length) (baseStart_3717385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717385 prefixEnd_3717385 := by exact prefixLift 3717385
  have htrace : WordTrace (prefixWord ++ tailWord_3717385) baseStart_3717385 baseEnd_3717385 := by
    simpa [prefixWord, tailWord_3717385, baseEnd_3717385] using wordTrace_append hprefix tailTrace_3717385
  have hstable : (prefixWord ++ tailWord_3717385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717385).length < 2 ^ (prefixWord ++ tailWord_3717385).sum := by decide
  have hdescent : baseEnd_3717385 < baseStart_3717385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717406 : List Nat := [4, 3, 2, 1, 1, 1, 4, 2, 4]
def baseStart_3717406 : Nat := 118140960795 + 3717406 * 2 ^ 59
def prefixEnd_3717406 : Nat := 4983230072969 + 3 ^ 40 * 3717406 * 2
def baseEnd_3717406 : Nat := 424181347979508414584215

theorem tailTrace_3717406 : CollatzResearch.WordTrace tailWord_3717406 prefixEnd_3717406 424181347979508414584215 := by
  unfold tailWord_3717406
  simp only [CollatzResearch.WordTrace]
  refine ⟨16948116946310052405542509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90389957046986946162893381 16948116946310052405542509)
  ·
    refine ⟨6355543854866269652078441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16948116946310052405542509 6355543854866269652078441)
    ·
      refine ⟨4766657891149702239058831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6355543854866269652078441 4766657891149702239058831)
      ·
        refine ⟨7149986836724553358588247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4766657891149702239058831 7149986836724553358588247)
        ·
          refine ⟨10724980255086830037882371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7149986836724553358588247 10724980255086830037882371)
          ·
            refine ⟨16087470382630245056823557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10724980255086830037882371 16087470382630245056823557)
            ·
              refine ⟨3016400696743170948154417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16087470382630245056823557 3016400696743170948154417)
              ·
                refine ⟨2262300522557378211115813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3016400696743170948154417 2262300522557378211115813)
                ·
                  refine ⟨424181347979508414584215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2262300522557378211115813 424181347979508414584215)
                  ·
                    rfl

theorem cell22_3717406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_3717406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717406 prefixEnd_3717406 := by exact prefixLift 3717406
  have htrace : WordTrace (prefixWord ++ tailWord_3717406) baseStart_3717406 baseEnd_3717406 := by
    simpa [prefixWord, tailWord_3717406, baseEnd_3717406] using wordTrace_append hprefix tailTrace_3717406
  have hstable : (prefixWord ++ tailWord_3717406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717406).length < 2 ^ (prefixWord ++ tailWord_3717406).sum := by decide
  have hdescent : baseEnd_3717406 < baseStart_3717406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717460 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_3717460 : Nat := 118140960795 + 3717460 * 2 ^ 59
def prefixEnd_3717460 : Nat := 4983230072969 + 3 ^ 40 * 3717460 * 2
def baseEnd_3717460 : Nat := 1272562529242087102902479

theorem tailTrace_3717460 : CollatzResearch.WordTrace tailWord_3717460 prefixEnd_3717460 1272562529242087102902479 := by
  unfold tailWord_3717460
  simp only [CollatzResearch.WordTrace]
  refine ⟨67793452556142393233402917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90391270074856524311203889 67793452556142393233402917)
  ·
    refine ⟨12711272354276698731263047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67793452556142393233402917 12711272354276698731263047)
    ·
      refine ⟨19066908531415048096894571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12711272354276698731263047 19066908531415048096894571)
      ·
        refine ⟨28600362797122572145341857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19066908531415048096894571 28600362797122572145341857)
        ·
          refine ⟨21450272097841929109006393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28600362797122572145341857 21450272097841929109006393)
          ·
            refine ⟨16087704073381446831754795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21450272097841929109006393 16087704073381446831754795)
            ·
              refine ⟨24131556110072170247632193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16087704073381446831754795 24131556110072170247632193)
              ·
                refine ⟨18098667082554127685724145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24131556110072170247632193 18098667082554127685724145)
                ·
                  refine ⟨13574000311915595764293109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18098667082554127685724145 13574000311915595764293109)
                  ·
                    refine ⟨1272562529242087102902479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13574000311915595764293109 1272562529242087102902479)
                    ·
                      rfl

theorem cell22_3717460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_3717460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717460 prefixEnd_3717460 := by exact prefixLift 3717460
  have htrace : WordTrace (prefixWord ++ tailWord_3717460) baseStart_3717460 baseEnd_3717460 := by
    simpa [prefixWord, tailWord_3717460, baseEnd_3717460] using wordTrace_append hprefix tailTrace_3717460
  have hstable : (prefixWord ++ tailWord_3717460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717460).length < 2 ^ (prefixWord ++ tailWord_3717460).sum := by decide
  have hdescent : baseEnd_3717460 < baseStart_3717460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717490 : List Nat := [3, 2, 1, 2, 1, 3, 2, 2, 6]
def baseStart_3717490 : Nat := 118140960795 + 3717490 * 2 ^ 59
def prefixEnd_3717490 : Nat := 4983230072969 + 3 ^ 40 * 3717490 * 2
def baseEnd_3717490 : Nat := 424190932951725674884129

theorem tailTrace_3717490 : CollatzResearch.WordTrace tailWord_3717490 prefixEnd_3717490 424190932951725674884129 := by
  unfold tailWord_3717490
  simp only [CollatzResearch.WordTrace]
  refine ⟨33896999825544025397599481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90391999534784067726931949 33896999825544025397599481)
  ·
    refine ⟨25422749869158019048199611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33896999825544025397599481 25422749869158019048199611)
    ·
      refine ⟨38134124803737028572299417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25422749869158019048199611 38134124803737028572299417)
      ·
        refine ⟨28600593602802771429224563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38134124803737028572299417 28600593602802771429224563)
        ·
          refine ⟨42900890404204157143836845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28600593602802771429224563 42900890404204157143836845)
          ·
            refine ⟨16087833901576558928938817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42900890404204157143836845 16087833901576558928938817)
            ·
              refine ⟨12065875426182419196704113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16087833901576558928938817 12065875426182419196704113)
              ·
                refine ⟨9049406569636814397528085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12065875426182419196704113 9049406569636814397528085)
                ·
                  refine ⟨424190932951725674884129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9049406569636814397528085 424190932951725674884129)
                  ·
                    rfl

theorem cell22_3717490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_3717490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717490 prefixEnd_3717490 := by exact prefixLift 3717490
  have htrace : WordTrace (prefixWord ++ tailWord_3717490) baseStart_3717490 baseEnd_3717490 := by
    simpa [prefixWord, tailWord_3717490, baseEnd_3717490] using wordTrace_append hprefix tailTrace_3717490
  have hstable : (prefixWord ++ tailWord_3717490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717490).length < 2 ^ (prefixWord ++ tailWord_3717490).sum := by decide
  have hdescent : baseEnd_3717490 < baseStart_3717490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717524 : List Nat := [2, 4, 2, 1, 3, 2, 1, 1, 6]
def baseStart_3717524 : Nat := 118140960795 + 3717524 * 2 ^ 59
def prefixEnd_3717524 : Nat := 4983230072969 + 3 ^ 40 * 3717524 * 2
def baseEnd_3717524 : Nat := 424194812583337423100761

theorem tailTrace_3717524 : CollatzResearch.WordTrace tailWord_3717524 prefixEnd_3717524 424194812583337423100761 := by
  unfold tailWord_3717524
  simp only [CollatzResearch.WordTrace]
  refine ⟨67794619692026462698567813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90392826256035283598090417 67794619692026462698567813)
  ·
    refine ⟨12711491192254961755981465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67794619692026462698567813 12711491192254961755981465)
    ·
      refine ⟨9533618394191221316986099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12711491192254961755981465 9533618394191221316986099)
      ·
        refine ⟨14300427591286831975479149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9533618394191221316986099 14300427591286831975479149)
        ·
          refine ⟨5362660346732561990804681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14300427591286831975479149 5362660346732561990804681)
          ·
            refine ⟨4021995260049421493103511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5362660346732561990804681 4021995260049421493103511)
            ·
              refine ⟨6032992890074132239655267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4021995260049421493103511 6032992890074132239655267)
              ·
                refine ⟨9049489335111198359482901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6032992890074132239655267 9049489335111198359482901)
                ·
                  refine ⟨424194812583337423100761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9049489335111198359482901 424194812583337423100761)
                  ·
                    rfl

theorem cell22_3717524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_3717524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717524 prefixEnd_3717524 := by exact prefixLift 3717524
  have htrace : WordTrace (prefixWord ++ tailWord_3717524) baseStart_3717524 baseEnd_3717524 := by
    simpa [prefixWord, tailWord_3717524, baseEnd_3717524] using wordTrace_append hprefix tailTrace_3717524
  have hstable : (prefixWord ++ tailWord_3717524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717524).length < 2 ^ (prefixWord ++ tailWord_3717524).sum := by decide
  have hdescent : baseEnd_3717524 < baseStart_3717524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717535 : List Nat := [1, 1, 2, 5, 1, 1, 4, 7]
def baseStart_3717535 : Nat := 118140960795 + 3717535 * 2 ^ 59
def prefixEnd_3717535 : Nat := 4983230072969 + 3 ^ 40 * 3717535 * 2
def baseEnd_3717535 : Nat := 141398689252756878586361

theorem tailTrace_3717535 : CollatzResearch.WordTrace tailWord_3717535 prefixEnd_3717535 141398689252756878586361 := by
  unfold tailWord_3717535
  simp only [CollatzResearch.WordTrace]
  refine ⟨135589640587013074275786059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90393093724675382850524039 135589640587013074275786059)
  ·
    refine ⟨203384460880519611413679089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135589640587013074275786059 203384460880519611413679089)
    ·
      refine ⟨152538345660389708560259317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203384460880519611413679089 152538345660389708560259317)
      ·
        refine ⟨14300469905661535177524311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152538345660389708560259317 14300469905661535177524311)
        ·
          refine ⟨21450704858492302766286467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14300469905661535177524311 21450704858492302766286467)
          ·
            refine ⟨32176057287738454149429701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21450704858492302766286467 32176057287738454149429701)
            ·
              refine ⟨6033010741450960153018069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32176057287738454149429701 6033010741450960153018069)
              ·
                refine ⟨141398689252756878586361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6033010741450960153018069 141398689252756878586361)
                ·
                  rfl

theorem cell22_3717535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 7].length) (baseStart_3717535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717535 prefixEnd_3717535 := by exact prefixLift 3717535
  have htrace : WordTrace (prefixWord ++ tailWord_3717535) baseStart_3717535 baseEnd_3717535 := by
    simpa [prefixWord, tailWord_3717535, baseEnd_3717535] using wordTrace_append hprefix tailTrace_3717535
  have hstable : (prefixWord ++ tailWord_3717535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717535).length < 2 ^ (prefixWord ++ tailWord_3717535).sum := by decide
  have hdescent : baseEnd_3717535 < baseStart_3717535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717539 : List Nat := [1, 1, 1, 4, 1, 4, 4, 1, 2, 3]
def baseStart_3717539 : Nat := 118140960795 + 3717539 * 2 ^ 59
def prefixEnd_3717539 : Nat := 4983230072969 + 3 ^ 40 * 3717539 * 2
def baseEnd_3717539 : Nat := 1272589572556557230177237

theorem tailTrace_3717539 : CollatzResearch.WordTrace tailWord_3717539 prefixEnd_3717539 1272589572556557230177237 := by
  unfold tailWord_3717539
  simp only [CollatzResearch.WordTrace]
  refine ⟨135589786478998582958931671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90393190985999055305954447 135589786478998582958931671)
  ·
    refine ⟨203384679718497874438397507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135589786478998582958931671 203384679718497874438397507)
    ·
      refine ⟨305077019577746811657596261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203384679718497874438397507 305077019577746811657596261)
      ·
        refine ⟨57201941170827527185799299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305077019577746811657596261 57201941170827527185799299)
        ·
          refine ⟨85802911756241290778698949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57201941170827527185799299 85802911756241290778698949)
          ·
            refine ⟨16088045954295242021006053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85802911756241290778698949 16088045954295242021006053)
            ·
              refine ⟨3016508616430357878938635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16088045954295242021006053 3016508616430357878938635)
              ·
                refine ⟨4524762924645536818407953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3016508616430357878938635 4524762924645536818407953)
                ·
                  refine ⟨3393572193484152613805965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4524762924645536818407953 3393572193484152613805965)
                  ·
                    refine ⟨1272589572556557230177237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3393572193484152613805965 1272589572556557230177237)
                    ·
                      rfl

theorem cell22_3717539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 2, 3].length) (baseStart_3717539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717539 prefixEnd_3717539 := by exact prefixLift 3717539
  have htrace : WordTrace (prefixWord ++ tailWord_3717539) baseStart_3717539 baseEnd_3717539 := by
    simpa [prefixWord, tailWord_3717539, baseEnd_3717539] using wordTrace_append hprefix tailTrace_3717539
  have hstable : (prefixWord ++ tailWord_3717539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717539).length < 2 ^ (prefixWord ++ tailWord_3717539).sum := by decide
  have hdescent : baseEnd_3717539 < baseStart_3717539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717556 : List Nat := [2, 5, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_3717556 : Nat := 118140960795 + 3717556 * 2 ^ 59
def prefixEnd_3717556 : Nat := 4983230072969 + 3 ^ 40 * 3717556 * 2
def baseEnd_3717556 : Nat := 1272595392003974852502185

theorem tailTrace_3717556 : CollatzResearch.WordTrace tailWord_3717556 prefixEnd_3717556 1272595392003974852502185 := by
  unfold tailWord_3717556
  simp only [CollatzResearch.WordTrace]
  refine ⟨67795203259968497431150261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90393604346624663241533681 67795203259968497431150261)
  ·
    refine ⟨6355800305622046634170337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67795203259968497431150261 6355800305622046634170337)
    ·
      refine ⟨4766850229216534975627753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6355800305622046634170337 4766850229216534975627753)
      ·
        refine ⟨3575137671912401231720815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4766850229216534975627753 3575137671912401231720815)
        ·
          refine ⟨5362706507868601847581223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3575137671912401231720815 5362706507868601847581223)
          ·
            refine ⟨8044059761802902771371835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5362706507868601847581223 8044059761802902771371835)
            ·
              refine ⟨12066089642704354157057753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8044059761802902771371835 12066089642704354157057753)
              ·
                refine ⟨9049567232028265617793315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12066089642704354157057753 9049567232028265617793315)
                ·
                  refine ⟨13574350848042398426689973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9049567232028265617793315 13574350848042398426689973)
                  ·
                    refine ⟨1272595392003974852502185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13574350848042398426689973 1272595392003974852502185)
                    ·
                      rfl

theorem cell22_3717556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_3717556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717556 prefixEnd_3717556 := by exact prefixLift 3717556
  have htrace : WordTrace (prefixWord ++ tailWord_3717556) baseStart_3717556 baseEnd_3717556 := by
    simpa [prefixWord, tailWord_3717556, baseEnd_3717556] using wordTrace_append hprefix tailTrace_3717556
  have hstable : (prefixWord ++ tailWord_3717556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717556).length < 2 ^ (prefixWord ++ tailWord_3717556).sum := by decide
  have hdescent : baseEnd_3717556 < baseStart_3717556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717569 : List Nat := [1, 2, 7, 1, 1, 10]
def baseStart_3717569 : Nat := 118140960795 + 3717569 * 2 ^ 59
def prefixEnd_3717569 : Nat := 4983230072969 + 3 ^ 40 * 3717569 * 2
def baseEnd_3717569 : Nat := 15711109162588236443545

theorem tailTrace_3717569 : CollatzResearch.WordTrace tailWord_3717569 prefixEnd_3717569 15711109162588236443545 := by
  unfold tailWord_3717569
  simp only [CollatzResearch.WordTrace]
  refine ⟨135590880668889898082523761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90393920445926598721682507 135590880668889898082523761)
  ·
    refine ⟨101693160501667423561892821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135590880668889898082523761 101693160501667423561892821)
    ·
      refine ⟨2383433449257830239731863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 101693160501667423561892821 2383433449257830239731863)
      ·
        refine ⟨3575150173886745359597795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2383433449257830239731863 3575150173886745359597795)
        ·
          refine ⟨5362725260830118039396693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3575150173886745359597795 5362725260830118039396693)
          ·
            refine ⟨15711109162588236443545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5362725260830118039396693 15711109162588236443545)
            ·
              rfl

theorem cell22_3717569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 10].length) (baseStart_3717569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717569 prefixEnd_3717569 := by exact prefixLift 3717569
  have htrace : WordTrace (prefixWord ++ tailWord_3717569) baseStart_3717569 baseEnd_3717569 := by
    simpa [prefixWord, tailWord_3717569, baseEnd_3717569] using wordTrace_append hprefix tailTrace_3717569
  have hstable : (prefixWord ++ tailWord_3717569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717569).length < 2 ^ (prefixWord ++ tailWord_3717569).sum := by decide
  have hdescent : baseEnd_3717569 < baseStart_3717569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717586 : List Nat := [3, 2, 2, 4, 2, 1, 1, 7]
def baseStart_3717586 : Nat := 118140960795 + 3717586 * 2 ^ 59
def prefixEnd_3717586 : Nat := 4983230072969 + 3 ^ 40 * 3717586 * 2
def baseEnd_3717586 : Nat := 141400629068562752694677

theorem tailTrace_3717586 : CollatzResearch.WordTrace tailWord_3717586 prefixEnd_3717586 141400629068562752694677 := by
  unfold tailWord_3717586
  simp only [CollatzResearch.WordTrace]
  refine ⟨33897875177457077496473153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90394333806552206657261741 33897875177457077496473153)
  ·
    refine ⟨25423406383092808122354865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33897875177457077496473153 25423406383092808122354865)
    ·
      refine ⟨19067554787319606091766149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25423406383092808122354865 19067554787319606091766149)
      ·
        refine ⟨3575166522622426142206153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19067554787319606091766149 3575166522622426142206153)
        ·
          refine ⟨2681374891966819606654615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3575166522622426142206153 2681374891966819606654615)
          ·
            refine ⟨4022062337950229409981923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2681374891966819606654615 4022062337950229409981923)
            ·
              refine ⟨6033093506925344114972885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4022062337950229409981923 6033093506925344114972885)
              ·
                refine ⟨141400629068562752694677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6033093506925344114972885 141400629068562752694677)
                ·
                  rfl

theorem cell22_3717586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 7].length) (baseStart_3717586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717586 prefixEnd_3717586 := by exact prefixLift 3717586
  have htrace : WordTrace (prefixWord ++ tailWord_3717586) baseStart_3717586 baseEnd_3717586 := by
    simpa [prefixWord, tailWord_3717586, baseEnd_3717586] using wordTrace_append hprefix tailTrace_3717586
  have hstable : (prefixWord ++ tailWord_3717586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717586).length < 2 ^ (prefixWord ++ tailWord_3717586).sum := by decide
  have hdescent : baseEnd_3717586 < baseStart_3717586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717597 : List Nat := [1, 4, 3, 1, 1, 1, 1, 5, 5]
def baseStart_3717597 : Nat := 118140960795 + 3717597 * 2 ^ 59
def prefixEnd_3717597 : Nat := 4983230072969 + 3 ^ 40 * 3717597 * 2
def baseEnd_3717597 : Nat := 424203142380621470742353

theorem tailTrace_3717597 : CollatzResearch.WordTrace tailWord_3717597 prefixEnd_3717597 424203142380621470742353 := by
  unfold tailWord_3717597
  simp only [CollatzResearch.WordTrace]
  refine ⟨135591901912788458864543045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90394601275192305909695363 135591901912788458864543045)
  ·
    refine ⟨25423481608647836037101821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135591901912788458864543045 25423481608647836037101821)
    ·
      refine ⟨9533805603242938513913183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25423481608647836037101821 9533805603242938513913183)
      ·
        refine ⟨14300708404864407770869775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9533805603242938513913183 14300708404864407770869775)
        ·
          refine ⟨21451062607296611656304663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14300708404864407770869775 21451062607296611656304663)
          ·
            refine ⟨32176593910944917484456995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21451062607296611656304663 32176593910944917484456995)
            ·
              refine ⟨48264890866417376226685493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32176593910944917484456995 48264890866417376226685493)
              ·
                refine ⟨4524833518726629021251765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48264890866417376226685493 4524833518726629021251765)
                ·
                  refine ⟨424203142380621470742353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4524833518726629021251765 424203142380621470742353)
                  ·
                    rfl

theorem cell22_3717597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_3717597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717597 prefixEnd_3717597 := by exact prefixLift 3717597
  have htrace : WordTrace (prefixWord ++ tailWord_3717597) baseStart_3717597 baseEnd_3717597 := by
    simpa [prefixWord, tailWord_3717597, baseEnd_3717597] using wordTrace_append hprefix tailTrace_3717597
  have hstable : (prefixWord ++ tailWord_3717597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717597).length < 2 ^ (prefixWord ++ tailWord_3717597).sum := by decide
  have hdescent : baseEnd_3717597 < baseStart_3717597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717618 : List Nat := [3, 2, 1, 4, 2, 1, 2, 3, 1, 3]
def baseStart_3717618 : Nat := 118140960795 + 3717618 * 2 ^ 59
def prefixEnd_3717618 : Nat := 4983230072969 + 3 ^ 40 * 3717618 * 2
def baseEnd_3717618 : Nat := 1272616615871027357451995

theorem tailTrace_3717618 : CollatzResearch.WordTrace tailWord_3717618 prefixEnd_3717618 1272616615871027357451995 := by
  unfold tailWord_3717618
  simp only [CollatzResearch.WordTrace]
  refine ⟨33898166961428094862764377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90395111897141586300705005 33898166961428094862764377)
  ·
    refine ⟨25423625221071071147073283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33898166961428094862764377 25423625221071071147073283)
    ·
      refine ⟨38135437831606606720609925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25423625221071071147073283 38135437831606606720609925)
      ·
        refine ⟨7150394593426238760114361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38135437831606606720609925 7150394593426238760114361)
        ·
          refine ⟨5362795945069679070085771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7150394593426238760114361 5362795945069679070085771)
          ·
            refine ⟨8044193917604518605128657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5362795945069679070085771 8044193917604518605128657)
            ·
              refine ⟨6033145438203388953846493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8044193917604518605128657 6033145438203388953846493)
              ·
                refine ⟨2262429539326270857692435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6033145438203388953846493 2262429539326270857692435)
                ·
                  refine ⟨3393644308989406286538653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2262429539326270857692435 3393644308989406286538653)
                  ·
                    refine ⟨1272616615871027357451995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3393644308989406286538653 1272616615871027357451995)
                    ·
                      rfl

theorem cell22_3717618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_3717618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717618 prefixEnd_3717618 := by exact prefixLift 3717618
  have htrace : WordTrace (prefixWord ++ tailWord_3717618) baseStart_3717618 baseEnd_3717618 := by
    simpa [prefixWord, tailWord_3717618, baseEnd_3717618] using wordTrace_append hprefix tailTrace_3717618
  have hstable : (prefixWord ++ tailWord_3717618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717618).length < 2 ^ (prefixWord ++ tailWord_3717618).sum := by decide
  have hdescent : baseEnd_3717618 < baseStart_3717618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717642 : List Nat := [3, 1, 2, 2, 2, 1, 4, 1, 6]
def baseStart_3717642 : Nat := 118140960795 + 3717642 * 2 ^ 59
def prefixEnd_3717642 : Nat := 4983230072969 + 3 ^ 40 * 3717642 * 2
def baseEnd_3717642 : Nat := 424208277187166431617307

theorem tailTrace_3717642 : CollatzResearch.WordTrace tailWord_3717642 prefixEnd_3717642 424208277187166431617307 := by
  unfold tailWord_3717642
  simp only [CollatzResearch.WordTrace]
  refine ⟨33898385799406357887482795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90395695465083621033287453 33898385799406357887482795)
  ·
    refine ⟨50847578699109536831224193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33898385799406357887482795 50847578699109536831224193)
    ·
      refine ⟨38135684024332152623418145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50847578699109536831224193 38135684024332152623418145)
      ·
        refine ⟨28601763018249114467563609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38135684024332152623418145 28601763018249114467563609)
        ·
          refine ⟨21451322263686835850672707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28601763018249114467563609 21451322263686835850672707)
          ·
            refine ⟨32176983395530253776009061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21451322263686835850672707 32176983395530253776009061)
            ·
              refine ⟨6033184386661922583001699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32176983395530253776009061 6033184386661922583001699)
              ·
                refine ⟨9049776579992883874502549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6033184386661922583001699 9049776579992883874502549)
                ·
                  refine ⟨424208277187166431617307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9049776579992883874502549 424208277187166431617307)
                  ·
                    rfl

theorem cell22_3717642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_3717642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717642 prefixEnd_3717642 := by exact prefixLift 3717642
  have htrace : WordTrace (prefixWord ++ tailWord_3717642) baseStart_3717642 baseEnd_3717642 := by
    simpa [prefixWord, tailWord_3717642, baseEnd_3717642] using wordTrace_append hprefix tailTrace_3717642
  have hstable : (prefixWord ++ tailWord_3717642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717642).length < 2 ^ (prefixWord ++ tailWord_3717642).sum := by decide
  have hdescent : baseEnd_3717642 < baseStart_3717642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717674 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 4, 3]
def baseStart_3717674 : Nat := 118140960795 + 3717674 * 2 ^ 59
def prefixEnd_3717674 : Nat := 4983230072969 + 3 ^ 40 * 3717674 * 2
def baseEnd_3717674 : Nat := 1272635785815461878051823

theorem tailTrace_3717674 : CollatzResearch.WordTrace tailWord_3717674 prefixEnd_3717674 1272635785815461878051823 := by
  unfold tailWord_3717674
  simp only [CollatzResearch.WordTrace]
  refine ⟨33898677583377375253774019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90396473555673000676730717 33898677583377375253774019)
  ·
    refine ⟨50848016375066062880661029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33898677583377375253774019 50848016375066062880661029)
    ·
      refine ⟨9534003070324886790123943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50848016375066062880661029 9534003070324886790123943)
      ·
        refine ⟨14301004605487330185185915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9534003070324886790123943 14301004605487330185185915)
        ·
          refine ⟨21451506908230995277778873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14301004605487330185185915 21451506908230995277778873)
          ·
            refine ⟨16088630181173246458334155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21451506908230995277778873 16088630181173246458334155)
            ·
              refine ⟨24132945271759869687501233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16088630181173246458334155 24132945271759869687501233)
              ·
                refine ⟨18099708953819902265625925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24132945271759869687501233 18099708953819902265625925)
                ·
                  refine ⟨3393695428841231674804861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18099708953819902265625925 3393695428841231674804861)
                  ·
                    refine ⟨1272635785815461878051823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3393695428841231674804861 1272635785815461878051823)
                    ·
                      rfl

theorem cell22_3717674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_3717674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717674 prefixEnd_3717674 := by exact prefixLift 3717674
  have htrace : WordTrace (prefixWord ++ tailWord_3717674) baseStart_3717674 baseEnd_3717674 := by
    simpa [prefixWord, tailWord_3717674, baseEnd_3717674] using wordTrace_append hprefix tailTrace_3717674
  have hstable : (prefixWord ++ tailWord_3717674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717674).length < 2 ^ (prefixWord ++ tailWord_3717674).sum := by decide
  have hdescent : baseEnd_3717674 < baseStart_3717674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717753 : List Nat := [1, 2, 1, 3, 3, 2, 4, 2, 1, 3]
def baseStart_3717753 : Nat := 118140960795 + 3717753 * 2 ^ 59
def prefixEnd_3717753 : Nat := 4983230072969 + 3 ^ 40 * 3717753 * 2
def baseEnd_3717753 : Nat := 1272662829129932005326581

theorem tailTrace_3717753 : CollatzResearch.WordTrace tailWord_3717753 prefixEnd_3717753 1272662829129932005326581 := by
  unfold tailWord_3717753
  simp only [CollatzResearch.WordTrace]
  refine ⟨135597591700223297507221913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90398394466815531671481275 135597591700223297507221913)
  ·
    refine ⟨101698193775167473130416435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135597591700223297507221913 101698193775167473130416435)
    ·
      refine ⟨152547290662751209695624653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101698193775167473130416435 152547290662751209695624653)
      ·
        refine ⟨57205233998531703635859245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152547290662751209695624653 57205233998531703635859245)
        ·
          refine ⟨21451962749449388863447217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57205233998531703635859245 21451962749449388863447217)
          ·
            refine ⟨16088972062087041647585413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21451962749449388863447217 16088972062087041647585413)
            ·
              refine ⟨3016682261641320308922265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16088972062087041647585413 3016682261641320308922265)
              ·
                refine ⟨2262511696230990231691699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3016682261641320308922265 2262511696230990231691699)
                ·
                  refine ⟨3393767544346485347537549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2262511696230990231691699 3393767544346485347537549)
                  ·
                    refine ⟨1272662829129932005326581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3393767544346485347537549 1272662829129932005326581)
                    ·
                      rfl

theorem cell22_3717753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 1, 3].length) (baseStart_3717753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717753 prefixEnd_3717753 := by exact prefixLift 3717753
  have htrace : WordTrace (prefixWord ++ tailWord_3717753) baseStart_3717753 baseEnd_3717753 := by
    simpa [prefixWord, tailWord_3717753, baseEnd_3717753] using wordTrace_append hprefix tailTrace_3717753
  have hstable : (prefixWord ++ tailWord_3717753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717753).length < 2 ^ (prefixWord ++ tailWord_3717753).sum := by decide
  have hdescent : baseEnd_3717753 < baseStart_3717753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717764 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_3717764 : Nat := 118140960795 + 3717764 * 2 ^ 59
def prefixEnd_3717764 : Nat := 4983230072969 + 3 ^ 40 * 3717764 * 2
def baseEnd_3717764 : Nat := 1272666594654731643301547

theorem tailTrace_3717764 : CollatzResearch.WordTrace tailWord_3717764 prefixEnd_3717764 1272666594654731643301547 := by
  unfold tailWord_3717764
  simp only [CollatzResearch.WordTrace]
  refine ⟨67798996451591723192936173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90398661935455630923914897 67798996451591723192936173)
  ·
    refine ⟨25424623669346896197351065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67798996451591723192936173 25424623669346896197351065)
    ·
      refine ⟨19068467752010172148013299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25424623669346896197351065 19068467752010172148013299)
      ·
        refine ⟨28602701628015258222019949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19068467752010172148013299 28602701628015258222019949)
        ·
          refine ⟨10726013110505721833257481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28602701628015258222019949 10726013110505721833257481)
          ·
            refine ⟨8044509832879291374943111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10726013110505721833257481 8044509832879291374943111)
            ·
              refine ⟨12066764749318937062414667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8044509832879291374943111 12066764749318937062414667)
              ·
                refine ⟨18100147123978405593622001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12066764749318937062414667 18100147123978405593622001)
                ·
                  refine ⟨13575110342983804195216501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18100147123978405593622001 13575110342983804195216501)
                  ·
                    refine ⟨1272666594654731643301547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13575110342983804195216501 1272666594654731643301547)
                    ·
                      rfl

theorem cell22_3717764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_3717764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717764 prefixEnd_3717764 := by exact prefixLift 3717764
  have htrace : WordTrace (prefixWord ++ tailWord_3717764) baseStart_3717764 baseEnd_3717764 := by
    simpa [prefixWord, tailWord_3717764, baseEnd_3717764] using wordTrace_append hprefix tailTrace_3717764
  have hstable : (prefixWord ++ tailWord_3717764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717764).length < 2 ^ (prefixWord ++ tailWord_3717764).sum := by decide
  have hdescent : baseEnd_3717764 < baseStart_3717764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717845 : List Nat := [1, 3, 2, 5, 1, 2, 1, 3, 4]
def baseStart_3717845 : Nat := 118140960795 + 3717845 * 2 ^ 59
def prefixEnd_3717845 : Nat := 4983230072969 + 3 ^ 40 * 3717845 * 2
def baseEnd_3717845 : Nat := 424231440870024810675433

theorem tailTrace_3717845 : CollatzResearch.WordTrace tailWord_3717845 prefixEnd_3717845 424231440870024810675433 := by
  unfold tailWord_3717845
  simp only [CollatzResearch.WordTrace]
  refine ⟨135600947215889997219570989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90400631477259998146380659 135600947215889997219570989)
  ·
    refine ⟨50850355205958748957339121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135600947215889997219570989 50850355205958748957339121)
    ·
      refine ⟨38137766404469061718004341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50850355205958748957339121 38137766404469061718004341)
      ·
        refine ⟨3575415600418974536062907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38137766404469061718004341 3575415600418974536062907)
        ·
          refine ⟨5363123400628461804094361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3575415600418974536062907 5363123400628461804094361)
          ·
            refine ⟨4022342550471346353070771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5363123400628461804094361 4022342550471346353070771)
            ·
              refine ⟨6033513825707019529606157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4022342550471346353070771 6033513825707019529606157)
              ·
                refine ⟨2262567684640132323602309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6033513825707019529606157 2262567684640132323602309)
                ·
                  refine ⟨424231440870024810675433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2262567684640132323602309 424231440870024810675433)
                  ·
                    rfl

theorem cell22_3717845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_3717845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717845 prefixEnd_3717845 := by exact prefixLift 3717845
  have htrace : WordTrace (prefixWord ++ tailWord_3717845) baseStart_3717845 baseEnd_3717845 := by
    simpa [prefixWord, tailWord_3717845, baseEnd_3717845] using wordTrace_append hprefix tailTrace_3717845
  have hstable : (prefixWord ++ tailWord_3717845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717845).length < 2 ^ (prefixWord ++ tailWord_3717845).sum := by decide
  have hdescent : baseEnd_3717845 < baseStart_3717845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717869 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_3717869 : Nat := 118140960795 + 3717869 * 2 ^ 59
def prefixEnd_3717869 : Nat := 4983230072969 + 3 ^ 40 * 3717869 * 2
def baseEnd_3717869 : Nat := 1272702538300546369426225

theorem tailTrace_3717869 : CollatzResearch.WordTrace tailWord_3717869 prefixEnd_3717869 1272702538300546369426225 := by
  unfold tailWord_3717869
  simp only [CollatzResearch.WordTrace]
  refine ⟨135601822567803049318444661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90401215045202032878963107 135601822567803049318444661)
  ·
    refine ⟨12712670865731535873604187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135601822567803049318444661 12712670865731535873604187)
    ·
      refine ⟨19069006298597303810406281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12712670865731535873604187 19069006298597303810406281)
      ·
        refine ⟨14301754723947977857804711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19069006298597303810406281 14301754723947977857804711)
        ·
          refine ⟨21452632085921966786707067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14301754723947977857804711 21452632085921966786707067)
          ·
            refine ⟨32178948128882950180060601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21452632085921966786707067 32178948128882950180060601)
            ·
              refine ⟨24134211096662212635045451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32178948128882950180060601 24134211096662212635045451)
              ·
                refine ⟨36201316644993318952568177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24134211096662212635045451 36201316644993318952568177)
                ·
                  refine ⟨27150987483744989214426133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36201316644993318952568177 27150987483744989214426133)
                  ·
                    refine ⟨1272702538300546369426225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27150987483744989214426133 1272702538300546369426225)
                    ·
                      rfl

theorem cell22_3717869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_3717869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717869 prefixEnd_3717869 := by exact prefixLift 3717869
  have htrace : WordTrace (prefixWord ++ tailWord_3717869) baseStart_3717869 baseEnd_3717869 := by
    simpa [prefixWord, tailWord_3717869, baseEnd_3717869] using wordTrace_append hprefix tailTrace_3717869
  have hstable : (prefixWord ++ tailWord_3717869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717869).length < 2 ^ (prefixWord ++ tailWord_3717869).sum := by decide
  have hdescent : baseEnd_3717869 < baseStart_3717869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717871 : List Nat := [1, 1, 2, 1, 5, 2, 3, 1, 3, 3]
def baseStart_3717871 : Nat := 118140960795 + 3717871 * 2 ^ 59
def prefixEnd_3717871 : Nat := 4983230072969 + 3 ^ 40 * 3717871 * 2
def baseEnd_3717871 : Nat := 1272703222941419030876219

theorem tailTrace_3717871 : CollatzResearch.WordTrace tailWord_3717871 prefixEnd_3717871 1272703222941419030876219 := by
  unfold tailWord_3717871
  simp only [CollatzResearch.WordTrace]
  refine ⟨135601895513795803660017467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90401263675863869106678311 135601895513795803660017467)
  ·
    refine ⟨203402843270693705490026201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135601895513795803660017467 203402843270693705490026201)
    ·
      refine ⟨152552132453020279117519651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203402843270693705490026201 152552132453020279117519651)
      ·
        refine ⟨228828198679530418676279477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152552132453020279117519651 228828198679530418676279477)
        ·
          refine ⟨21452643626205976750901201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 228828198679530418676279477 21452643626205976750901201)
          ·
            refine ⟨16089482719654482563175901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21452643626205976750901201 16089482719654482563175901)
            ·
              refine ⟨6033556019870430961190963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16089482719654482563175901 6033556019870430961190963)
              ·
                refine ⟨9050334029805646441786445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6033556019870430961190963 9050334029805646441786445)
                ·
                  refine ⟨3393875261177117415669917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9050334029805646441786445 3393875261177117415669917)
                  ·
                    refine ⟨1272703222941419030876219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3393875261177117415669917 1272703222941419030876219)
                    ·
                      rfl

theorem cell22_3717871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 3].length) (baseStart_3717871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717871 prefixEnd_3717871 := by exact prefixLift 3717871
  have htrace : WordTrace (prefixWord ++ tailWord_3717871) baseStart_3717871 baseEnd_3717871 := by
    simpa [prefixWord, tailWord_3717871, baseEnd_3717871] using wordTrace_append hprefix tailTrace_3717871
  have hstable : (prefixWord ++ tailWord_3717871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717871).length < 2 ^ (prefixWord ++ tailWord_3717871).sum := by decide
  have hdescent : baseEnd_3717871 < baseStart_3717871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717877 : List Nat := [1, 3, 6, 1, 1, 1, 1, 3, 2, 3]
def baseStart_3717877 : Nat := 118140960795 + 3717877 * 2 ^ 59
def prefixEnd_3717877 : Nat := 4983230072969 + 3 ^ 40 * 3717877 * 2
def baseEnd_3717877 : Nat := 1272705276864037015226201

theorem tailTrace_3717877 : CollatzResearch.WordTrace tailWord_3717877 prefixEnd_3717877 1272705276864037015226201 := by
  unfold tailWord_3717877
  simp only [CollatzResearch.WordTrace]
  refine ⟨135602114351774066684735885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90401409567849377789823923 135602114351774066684735885)
  ·
    refine ⟨50850792881915275006775957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135602114351774066684735885 50850792881915275006775957)
    ·
      refine ⟨2383630916339778515942623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50850792881915275006775957 2383630916339778515942623)
      ·
        refine ⟨3575446374509667773913935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2383630916339778515942623 3575446374509667773913935)
        ·
          refine ⟨5363169561764501660870903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3575446374509667773913935 5363169561764501660870903)
          ·
            refine ⟨8044754342646752491306355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5363169561764501660870903 8044754342646752491306355)
            ·
              refine ⟨12067131513970128736959533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8044754342646752491306355 12067131513970128736959533)
              ·
                refine ⟨4525174317738798276359825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12067131513970128736959533 4525174317738798276359825)
                ·
                  refine ⟨3393880738304098707269869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4525174317738798276359825 3393880738304098707269869)
                  ·
                    refine ⟨1272705276864037015226201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3393880738304098707269869 1272705276864037015226201)
                    ·
                      rfl

theorem cell22_3717877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_3717877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717877 prefixEnd_3717877 := by exact prefixLift 3717877
  have htrace : WordTrace (prefixWord ++ tailWord_3717877) baseStart_3717877 baseEnd_3717877 := by
    simpa [prefixWord, tailWord_3717877, baseEnd_3717877] using wordTrace_append hprefix tailTrace_3717877
  have hstable : (prefixWord ++ tailWord_3717877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717877).length < 2 ^ (prefixWord ++ tailWord_3717877).sum := by decide
  have hdescent : baseEnd_3717877 < baseStart_3717877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717922 : List Nat := [3, 3, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_3717922 : Nat := 118140960795 + 3717922 * 2 ^ 59
def prefixEnd_3717922 : Nat := 4983230072969 + 3 ^ 40 * 3717922 * 2
def baseEnd_3717922 : Nat := 1272720681283671897851063

theorem tailTrace_3717922 : CollatzResearch.WordTrace tailWord_3717922 prefixEnd_3717922 1272720681283671897851063 := by
  unfold tailWord_3717922
  simp only [CollatzResearch.WordTrace]
  refine ⟨33900938909152759842531005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90402503757740692913416013 33900938909152759842531005)
  ·
    refine ⟨12712852090932284940949127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33900938909152759842531005 12712852090932284940949127)
    ·
      refine ⟨19069278136398427411423691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12712852090932284940949127 19069278136398427411423691)
      ·
        refine ⟨28603917204597641117135537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19069278136398427411423691 28603917204597641117135537)
        ·
          refine ⟨21452937903448230837851653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28603917204597641117135537 21452937903448230837851653)
          ·
            refine ⟨4022425856896543282097185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21452937903448230837851653 4022425856896543282097185)
            ·
              refine ⟨3016819392672407461572889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4022425856896543282097185 3016819392672407461572889)
              ·
                refine ⟨2262614544504305596179667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3016819392672407461572889 2262614544504305596179667)
                ·
                  refine ⟨3393921816756458394269501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2262614544504305596179667 3393921816756458394269501)
                  ·
                    refine ⟨1272720681283671897851063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3393921816756458394269501 1272720681283671897851063)
                    ·
                      rfl

theorem cell22_3717922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_3717922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717922 prefixEnd_3717922 := by exact prefixLift 3717922
  have htrace : WordTrace (prefixWord ++ tailWord_3717922) baseStart_3717922 baseEnd_3717922 := by
    simpa [prefixWord, tailWord_3717922, baseEnd_3717922] using wordTrace_append hprefix tailTrace_3717922
  have hstable : (prefixWord ++ tailWord_3717922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717922).length < 2 ^ (prefixWord ++ tailWord_3717922).sum := by decide
  have hdescent : baseEnd_3717922 < baseStart_3717922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717946 : List Nat := [3, 1, 1, 1, 6, 1, 1, 2, 6]
def baseStart_3717946 : Nat := 118140960795 + 3717946 * 2 ^ 59
def prefixEnd_3717946 : Nat := 4983230072969 + 3 ^ 40 * 3717946 * 2
def baseEnd_3717946 : Nat := 424242965658047945083663

theorem tailTrace_3717946 : CollatzResearch.WordTrace tailWord_3717946 prefixEnd_3717946 424242965658047945083663 := by
  unfold tailWord_3717946
  simp only [CollatzResearch.WordTrace]
  refine ⟨33901157747131022867249423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90403087325682727645998461 33901157747131022867249423)
  ·
    refine ⟨50851736620696534300874135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33901157747131022867249423 50851736620696534300874135)
    ·
      refine ⟨76277604931044801451311203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50851736620696534300874135 76277604931044801451311203)
      ·
        refine ⟨114416407396567202176966805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76277604931044801451311203 114416407396567202176966805)
        ·
          refine ⟨5363269096714087602045319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114416407396567202176966805 5363269096714087602045319)
          ·
            refine ⟨8044903645071131403067979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5363269096714087602045319 8044903645071131403067979)
            ·
              refine ⟨12067355467606697104601969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8044903645071131403067979 12067355467606697104601969)
              ·
                refine ⟨9050516600705022828451477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12067355467606697104601969 9050516600705022828451477)
                ·
                  refine ⟨424242965658047945083663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9050516600705022828451477 424242965658047945083663)
                  ·
                    rfl

theorem cell22_3717946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_3717946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717946 prefixEnd_3717946 := by exact prefixLift 3717946
  have htrace : WordTrace (prefixWord ++ tailWord_3717946) baseStart_3717946 baseEnd_3717946 := by
    simpa [prefixWord, tailWord_3717946, baseEnd_3717946] using wordTrace_append hprefix tailTrace_3717946
  have hstable : (prefixWord ++ tailWord_3717946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717946).length < 2 ^ (prefixWord ++ tailWord_3717946).sum := by decide
  have hdescent : baseEnd_3717946 < baseStart_3717946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717965 : List Nat := [1, 6, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_3717965 : Nat := 118140960795 + 3717965 * 2 ^ 59
def prefixEnd_3717965 : Nat := 4983230072969 + 3 ^ 40 * 3717965 * 2
def baseEnd_3717965 : Nat := 1272735401062434119025931

theorem tailTrace_3717965 : CollatzResearch.WordTrace tailWord_3717965 prefixEnd_3717965 1272735401062434119025931 := by
  unfold tailWord_3717965
  simp only [CollatzResearch.WordTrace]
  refine ⟨135605323975455257713939349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90403549316970171809292899 135605323975455257713939349)
  ·
    refine ⟨6356499561349465205340907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 135605323975455257713939349 6356499561349465205340907)
    ·
      refine ⟨9534749342024197808011361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6356499561349465205340907 9534749342024197808011361)
      ·
        refine ⟨7151062006518148356008521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9534749342024197808011361 7151062006518148356008521)
        ·
          refine ⟨5363296504888611267006391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7151062006518148356008521 5363296504888611267006391)
          ·
            refine ⟨8044944757332916900509587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5363296504888611267006391 8044944757332916900509587)
            ·
              refine ⟨12067417135999375350764381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8044944757332916900509587 12067417135999375350764381)
              ·
                refine ⟨4525281425999765756536643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12067417135999375350764381 4525281425999765756536643)
                ·
                  refine ⟨6787922138999648634804965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4525281425999765756536643 6787922138999648634804965)
                  ·
                    refine ⟨1272735401062434119025931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6787922138999648634804965 1272735401062434119025931)
                    ·
                      rfl

theorem cell22_3717965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_3717965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717965 prefixEnd_3717965 := by exact prefixLift 3717965
  have htrace : WordTrace (prefixWord ++ tailWord_3717965) baseStart_3717965 baseEnd_3717965 := by
    simpa [prefixWord, tailWord_3717965, baseEnd_3717965] using wordTrace_append hprefix tailTrace_3717965
  have hstable : (prefixWord ++ tailWord_3717965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717965).length < 2 ^ (prefixWord ++ tailWord_3717965).sum := by decide
  have hdescent : baseEnd_3717965 < baseStart_3717965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717978 : List Nat := [3, 1, 1, 2, 1, 4, 3, 2, 2, 3]
def baseStart_3717978 : Nat := 118140960795 + 3717978 * 2 ^ 59
def prefixEnd_3717978 : Nat := 4983230072969 + 3 ^ 40 * 3717978 * 2
def baseEnd_3717978 : Nat := 1272739851228106418450891

theorem tailTrace_3717978 : CollatzResearch.WordTrace tailWord_3717978 prefixEnd_3717978 1272739851228106418450891 := by
  unfold tailWord_3717978
  simp only [CollatzResearch.WordTrace]
  refine ⟨33901449531102040233540647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90403865416272107289441725 33901449531102040233540647)
  ·
    refine ⟨50852174296653060350310971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33901449531102040233540647 50852174296653060350310971)
    ·
      refine ⟨76278261444979590525466457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50852174296653060350310971 76278261444979590525466457)
      ·
        refine ⟨57208696083734692894099843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76278261444979590525466457 57208696083734692894099843)
        ·
          refine ⟨85813044125602039341149765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57208696083734692894099843 85813044125602039341149765)
          ·
            refine ⟨16089945773550382376465581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85813044125602039341149765 16089945773550382376465581)
            ·
              refine ⟨6033729665081393391174593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16089945773550382376465581 6033729665081393391174593)
              ·
                refine ⟨4525297248811045043380945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6033729665081393391174593 4525297248811045043380945)
                ·
                  refine ⟨3393972936608283782535709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4525297248811045043380945 3393972936608283782535709)
                  ·
                    refine ⟨1272739851228106418450891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3393972936608283782535709 1272739851228106418450891)
                    ·
                      rfl

theorem cell22_3717978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_3717978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3717978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3717978 prefixEnd_3717978 := by exact prefixLift 3717978
  have htrace : WordTrace (prefixWord ++ tailWord_3717978) baseStart_3717978 baseEnd_3717978 := by
    simpa [prefixWord, tailWord_3717978, baseEnd_3717978] using wordTrace_append hprefix tailTrace_3717978
  have hstable : (prefixWord ++ tailWord_3717978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717978).length < 2 ^ (prefixWord ++ tailWord_3717978).sum := by decide
  have hdescent : baseEnd_3717978 < baseStart_3717978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718014 : List Nat := [4, 2, 3, 1, 3, 1, 1, 3, 4]
def baseStart_3718014 : Nat := 118140960795 + 3718014 * 2 ^ 59
def prefixEnd_3718014 : Nat := 4983230072969 + 3 ^ 40 * 3718014 * 2
def baseEnd_3718014 : Nat := 424250724921271441516927

theorem tailTrace_3718014 : CollatzResearch.WordTrace tailWord_3718014 prefixEnd_3718014 424250724921271441516927 := by
  unfold tailWord_3718014
  simp only [CollatzResearch.WordTrace]
  refine ⟨16950888894034717385309137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90404740768185159388315397 16950888894034717385309137)
  ·
    refine ⟨12713166670526038038981853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16950888894034717385309137 12713166670526038038981853)
    ·
      refine ⟨4767437501447264264618195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12713166670526038038981853 4767437501447264264618195)
      ·
        refine ⟨7151156252170896396927293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4767437501447264264618195 7151156252170896396927293)
        ·
          refine ⟨2681683594564086148847735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7151156252170896396927293 2681683594564086148847735)
          ·
            refine ⟨4022525391846129223271603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2681683594564086148847735 4022525391846129223271603)
            ·
              refine ⟨6033788087769193834907405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4022525391846129223271603 6033788087769193834907405)
              ·
                refine ⟨2262670532913447688090277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6033788087769193834907405 2262670532913447688090277)
                ·
                  refine ⟨424250724921271441516927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2262670532913447688090277 424250724921271441516927)
                  ·
                    rfl

theorem cell22_3718014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_3718014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718014 prefixEnd_3718014 := by exact prefixLift 3718014
  have htrace : WordTrace (prefixWord ++ tailWord_3718014) baseStart_3718014 baseEnd_3718014 := by
    simpa [prefixWord, tailWord_3718014, baseEnd_3718014] using wordTrace_append hprefix tailTrace_3718014
  have hstable : (prefixWord ++ tailWord_3718014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718014).length < 2 ^ (prefixWord ++ tailWord_3718014).sum := by decide
  have hdescent : baseEnd_3718014 < baseStart_3718014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718019 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 9]
def baseStart_3718019 : Nat := 118140960795 + 3718019 * 2 ^ 59
def prefixEnd_3718019 : Nat := 4983230072969 + 3 ^ 40 * 3718019 * 2
def baseEnd_3718019 : Nat := 424251295455331992725255

theorem tailTrace_3718019 : CollatzResearch.WordTrace tailWord_3718019 prefixEnd_3718019 424251295455331992725255 := by
  unfold tailWord_3718019
  simp only [CollatzResearch.WordTrace]
  refine ⟨135607293517259624936405111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90404862344839749957603407 135607293517259624936405111)
  ·
    refine ⟨203410940275889437404607667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135607293517259624936405111 203410940275889437404607667)
    ·
      refine ⟨305116410413834156106911501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203410940275889437404607667 305116410413834156106911501)
      ·
        refine ⟨114418653905187808540091813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305116410413834156106911501 114418653905187808540091813)
        ·
          refine ⟨21453497607222714101267215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114418653905187808540091813 21453497607222714101267215)
          ·
            refine ⟨32180246410834071151900823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21453497607222714101267215 32180246410834071151900823)
            ·
              refine ⟨48270369616251106727851235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32180246410834071151900823 48270369616251106727851235)
              ·
                refine ⟨72405554424376660091776853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48270369616251106727851235 72405554424376660091776853)
                ·
                  refine ⟨424251295455331992725255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72405554424376660091776853 424251295455331992725255)
                  ·
                    rfl

theorem cell22_3718019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 9].length) (baseStart_3718019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718019 prefixEnd_3718019 := by exact prefixLift 3718019
  have htrace : WordTrace (prefixWord ++ tailWord_3718019) baseStart_3718019 baseEnd_3718019 := by
    simpa [prefixWord, tailWord_3718019, baseEnd_3718019] using wordTrace_append hprefix tailTrace_3718019
  have hstable : (prefixWord ++ tailWord_3718019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718019).length < 2 ^ (prefixWord ++ tailWord_3718019).sum := by decide
  have hdescent : baseEnd_3718019 < baseStart_3718019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718036 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 7]
def baseStart_3718036 : Nat := 118140960795 + 3718036 * 2 ^ 59
def prefixEnd_3718036 : Nat := 4983230072969 + 3 ^ 40 * 3718036 * 2
def baseEnd_3718036 : Nat := 424253235271137866833571

theorem tailTrace_3718036 : CollatzResearch.WordTrace tailWord_3718036 prefixEnd_3718036 424253235271137866833571 := by
  unfold tailWord_3718036
  simp only [CollatzResearch.WordTrace]
  refine ⟨67803956779099018419886981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90405275705465357893182641 67803956779099018419886981)
  ·
    refine ⟨12713241896081065953728809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67803956779099018419886981 12713241896081065953728809)
    ·
      refine ⟨9534931422060799465296607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12713241896081065953728809 9534931422060799465296607)
      ·
        refine ⟨14302397133091199197944911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9534931422060799465296607 14302397133091199197944911)
        ·
          refine ⟨21453595699636798796917367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14302397133091199197944911 21453595699636798796917367)
          ·
            refine ⟨32180393549455198195376051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21453595699636798796917367 32180393549455198195376051)
            ·
              refine ⟨48270590324182797293064077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32180393549455198195376051 48270590324182797293064077)
              ·
                refine ⟨18101471371568548984899029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48270590324182797293064077 18101471371568548984899029)
                ·
                  refine ⟨424253235271137866833571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18101471371568548984899029 424253235271137866833571)
                  ·
                    rfl

theorem cell22_3718036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_3718036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718036 prefixEnd_3718036 := by exact prefixLift 3718036
  have htrace : WordTrace (prefixWord ++ tailWord_3718036) baseStart_3718036 baseEnd_3718036 := by
    simpa [prefixWord, tailWord_3718036, baseEnd_3718036] using wordTrace_append hprefix tailTrace_3718036
  have hstable : (prefixWord ++ tailWord_3718036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718036).length < 2 ^ (prefixWord ++ tailWord_3718036).sum := by decide
  have hdescent : baseEnd_3718036 < baseStart_3718036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
